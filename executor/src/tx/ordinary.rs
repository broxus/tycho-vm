use anyhow::{Context, anyhow};
use tycho_types::models::{
    AccountStatus, BounceReason, ComputePhase, NewBounceComputePhaseInfo, OrdinaryTxInfo,
};
use tycho_types::num::Tokens;
use tycho_types::prelude::*;

use crate::error::{TxError, TxResult};
use crate::phase::{
    ActionPhaseContext, BouncePhaseContext, ComputePhaseContext, ComputePhaseFull,
    StoragePhaseContext, TransactionInput,
};
use crate::{ExecutorInspector, ExecutorState};

impl ExecutorState<'_> {
    pub fn run_ordinary_transaction(
        &mut self,
        is_external: bool,
        msg_root: Cell,
        mut inspector: Option<&mut ExecutorInspector<'_>>,
    ) -> TxResult<OrdinaryTxInfo> {
        // Receive inbound message.
        let mut msg = match self.receive_in_msg(msg_root) {
            Ok(msg) if msg.is_external == is_external => msg,
            Ok(_) => {
                return Err(TxError::Fatal(anyhow!(
                    "received an unexpected inbound message"
                )));
            }
            // Invalid external messages can be safely skipped.
            Err(_) if is_external => return Err(TxError::Skipped),
            Err(e) => return Err(TxError::Fatal(e)),
        };

        // Order of credit and storage phases depends on the `bounce` flag
        // of the inbound message.
        let storage_phase;
        let credit_phase;
        if msg.bounce_enabled {
            // Run storage phase.
            storage_phase = self
                .storage_phase(StoragePhaseContext {
                    adjust_msg_balance: false,
                    received_message: Some(&mut msg),
                    inspector: inspector.as_deref_mut(),
                })
                .context("storage phase failed")?;

            // Run credit phase (only for internal messages).
            credit_phase = if is_external {
                None
            } else {
                Some(self.credit_phase(&msg).context("credit phase failed")?)
            };
        } else {
            // Run credit phase (only for internal messages).
            credit_phase = if is_external {
                None
            } else {
                Some(self.credit_phase(&msg).context("credit phase failed")?)
            };

            // Run storage phase.
            storage_phase = self
                .storage_phase(StoragePhaseContext {
                    adjust_msg_balance: true,
                    received_message: Some(&mut msg),
                    inspector: inspector.as_deref_mut(),
                })
                .context("storage phase failed")?;
        }

        // Run compute phase.
        let ComputePhaseFull {
            compute_phase,
            accepted,
            original_balance,
            new_state,
            actions,
        } = self
            .compute_phase(ComputePhaseContext {
                input: TransactionInput::Ordinary(&msg),
                storage_fee: storage_phase.storage_fees_collected,
                force_accept: false,
                stop_on_accept: false,
                inspector: inspector.as_deref_mut(),
            })
            .context("compute phase failed")?;

        if is_external && !accepted {
            return Err(TxError::Skipped);
        }

        // Run action phase only if compute phase succeeded.
        let mut aborted = true;
        let mut state_exceeds_limits = false;
        let mut bounce_required = false;
        let mut action_fine = Tokens::ZERO;
        let mut destroyed = false;

        let mut action_phase = None;
        if let ComputePhase::Executed(compute_phase) = &compute_phase
            && compute_phase.success
        {
            let res = self
                .action_phase(ActionPhaseContext {
                    received_message: Some(&mut msg),
                    original_balance,
                    new_state,
                    actions,
                    compute_phase,
                    inspector,
                })
                .context("action phase failed")?;

            aborted = !res.action_phase.success;
            state_exceeds_limits = res.state_exceeds_limits;
            bounce_required = res.bounce;
            action_fine = res.action_fine;
            destroyed = self.end_status == AccountStatus::NotExists;

            action_phase = Some(res.action_phase);
        }

        // Run bounce phase for internal messages if something failed.
        let mut bounce_phase = None;
        if msg.bounce_enabled
            && (!matches!(&compute_phase, ComputePhase::Executed(p) if p.success)
                || state_exceeds_limits
                || bounce_required)
        {
            debug_assert!(!is_external);

            let reason = if let Some(phase) = &action_phase {
                BounceReason::ActionPhaseFailed {
                    result_code: phase.result_code,
                }
            } else {
                match &compute_phase {
                    ComputePhase::Executed(phase) => BounceReason::ComputePhaseFailed {
                        exit_code: phase.exit_code,
                    },
                    ComputePhase::Skipped(skipped) => {
                        BounceReason::ComputePhaseSkipped(skipped.reason)
                    }
                }
            };

            let (gas_fees, compute_phase_info) = match &compute_phase {
                ComputePhase::Executed(phase) => (
                    phase.gas_fees,
                    Some(NewBounceComputePhaseInfo {
                        gas_used: phase.gas_used.into_inner().try_into().unwrap_or(u32::MAX),
                        vm_steps: phase.vm_steps,
                    }),
                ),
                ComputePhase::Skipped(_) => (Tokens::ZERO, None),
            };

            bounce_phase = Some(
                self.bounce_phase(BouncePhaseContext {
                    gas_fees,
                    action_fine,
                    received_message: &msg,
                    reason,
                    compute_phase_info,
                })
                .context("bounce phase failed")?,
            );
        }

        // Build transaction info.
        Ok(OrdinaryTxInfo {
            credit_first: !msg.bounce_enabled,
            storage_phase: Some(storage_phase),
            credit_phase,
            compute_phase,
            action_phase,
            aborted,
            bounce_phase,
            destroyed,
        })
    }

    pub fn check_ordinary_transaction(
        &mut self,
        msg_root: Cell,
        mut inspector: Option<&mut ExecutorInspector<'_>>,
    ) -> TxResult<()> {
        // Receive phase
        let mut msg = match self.receive_in_msg(msg_root) {
            Ok(msg) if msg.is_external => msg,
            _ => return Err(TxError::Skipped),
        };

        // Storage phase
        let storage_phase = self
            .storage_phase(StoragePhaseContext {
                adjust_msg_balance: false,
                received_message: Some(&mut msg),
                inspector: inspector.as_deref_mut(),
            })
            .context("storage phase failed")?;

        // Compute phase with partial execution
        let ComputePhaseFull { accepted, .. } = self
            .compute_phase(ComputePhaseContext {
                input: TransactionInput::Ordinary(&msg),
                storage_fee: storage_phase.storage_fees_collected,
                force_accept: false,
                stop_on_accept: true,
                inspector,
            })
            .context("compute phase failed")?;

        if !accepted {
            return Err(TxError::Skipped);
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use tycho_asm_macros::tvmasm;
    use tycho_types::cell::Lazy;
    use tycho_types::models::{
        Account, AccountState, AccountStatusChange, ComputePhaseSkipReason, CurrencyCollection,
        ExtInMsgInfo, IntMsgInfo, MsgInfo, OptionalAccount, ShardAccount, SimpleLib, StateInit,
        StdAddr, StorageInfo, StorageUsed, TxInfo,
    };
    use tycho_types::num::VarUint56;

    use super::*;
    use crate::tests::{make_default_config, make_default_params, make_message};
    use crate::{Executor, PublicLibraryChange};

    const STUB_ADDR: StdAddr = StdAddr::new(0, HashBytes::ZERO);
    const MASTERCHAIN_ADDR: StdAddr = StdAddr::new(-1, HashBytes::ZERO);

    fn make_library(id: u16) -> Cell {
        CellBuilder::build_from(id).unwrap()
    }

    fn make_libraries<I>(items: I) -> Dict<HashBytes, SimpleLib>
    where
        I: IntoIterator<Item = (u16, bool)>,
    {
        let mut items = items
            .into_iter()
            .map(|(id, public)| {
                let root = make_library(id);
                (*root.repr_hash(), SimpleLib { root, public })
            })
            .collect::<Vec<_>>();
        items.sort_unstable_by_key(|(hash, _)| *hash);
        Dict::try_from_sorted_slice(&items).unwrap()
    }

    fn set_libraries(state: &mut ExecutorState<'_>, libraries: Dict<HashBytes, SimpleLib>) {
        let AccountState::Active(state) = &mut state.state else {
            panic!("expected active account state");
        };
        state.libraries = libraries;
    }

    fn assert_public_libs_diff(
        actual: &ahash::HashMap<HashBytes, PublicLibraryChange>,
        added: &[Cell],
        removed: &[Cell],
    ) {
        let expected = added
            .iter()
            .cloned()
            .map(|cell| (*cell.repr_hash(), PublicLibraryChange::Add(cell)))
            .chain(
                removed
                    .iter()
                    .map(|cell| (*cell.repr_hash(), PublicLibraryChange::Remove)),
            )
            .collect::<ahash::HashMap<_, _>>();
        assert_eq!(actual, &expected);
    }

    pub fn make_uninit_with_balance<T: Into<CurrencyCollection>>(
        address: &StdAddr,
        balance: T,
    ) -> ShardAccount {
        ShardAccount {
            account: Lazy::new(&OptionalAccount(Some(Account {
                address: address.clone().into(),
                storage_stat: StorageInfo::default(),
                last_trans_lt: 1001,
                balance: balance.into(),
                state: AccountState::Uninit,
            })))
            .unwrap(),
            last_trans_hash: HashBytes([0x11; 32]),
            last_trans_lt: 1000,
        }
    }

    #[test]
    fn ever_wallet_deploys() -> Result<()> {
        let config = make_default_config();
        let params = make_default_params();

        let code = Boc::decode(include_bytes!("../../res/ever_wallet_code.boc"))?;
        let data = CellBuilder::build_from((HashBytes::ZERO, 0u64))?;

        let state_init = StateInit {
            split_depth: None,
            special: None,
            code: Some(code),
            data: Some(data),
            libraries: Dict::new(),
        };
        let address = StdAddr::new(0, *CellBuilder::build_from(&state_init)?.repr_hash());

        let msg = make_message(
            ExtInMsgInfo {
                src: None,
                dst: address.clone().into(),
                import_fee: Tokens::ZERO,
            },
            Some(state_init),
            Some({
                let mut b = CellBuilder::new();
                // just$1 Signature
                b.store_bit_one()?;
                b.store_u256(&HashBytes::ZERO)?;
                b.store_u256(&HashBytes::ZERO)?;
                // just$1 Pubkey
                b.store_bit_one()?;
                b.store_zeros(256)?;
                // header_time:u64
                b.store_u64((params.block_unixtime - 10) as u64 * 1000)?;
                // header_expire:u32
                b.store_u32(params.block_unixtime + 40)?;
                // sendTransaction
                b.store_u32(0x4cee646c)?;
                // ...
                b.store_reference({
                    let mut b = CellBuilder::new();
                    // dest:address
                    address.store_into(&mut b, Cell::empty_context())?;
                    // value:uint128
                    b.store_u128(10000000)?;
                    // bounce:false
                    b.store_bit_zero()?;
                    // mode:uint8
                    b.store_u8(0b11)?;
                    // payload:cell
                    b.store_reference(Cell::empty_cell())?;
                    //
                    b.build()?
                })?;
                //
                b
            }),
        );

        let state = make_uninit_with_balance(&address, CurrencyCollection::new(1_000_000_000));

        let output = Executor::new(&params, config.as_ref())
            .begin_ordinary(&address, true, &msg, &state)?
            .commit()?;

        println!("SHARD_STATE: {:#?}", output.new_state);
        let account = output.new_state.load_account()?;
        println!("ACCOUNT: {:#?}", account);

        let tx = output.transaction.load()?;
        println!("TX: {tx:#?}");
        let info = tx.load_info()?;
        println!("INFO: {info:#?}");

        Ok(())
    }

    #[test]
    fn freeze_account() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();

        let code = tvmasm!(
            r#"
            NEWC INT 123 STUR 32 ENDC
            POP c4
            ACCEPT
            "#
        );
        let mut state = ExecutorState::new_active(
            &params,
            &config,
            &STUB_ADDR,
            Tokens::ZERO,
            CellBuilder::build_from(u32::MIN)?,
            code,
        );
        state.storage_stat = StorageInfo {
            used: StorageUsed {
                bits: VarUint56::new(128),
                cells: VarUint56::new(1),
            },
            storage_extra: Default::default(),
            last_paid: params.block_unixtime - 1000,
            due_payment: Some(Tokens::new(2 * config.gas_prices.freeze_due_limit as u128)),
        };

        let info = state.run_ordinary_transaction(
            false,
            make_message(
                IntMsgInfo {
                    src: STUB_ADDR.into(),
                    dst: STUB_ADDR.into(),
                    value: CurrencyCollection::new(1_000_000),
                    bounce: true,
                    ..Default::default()
                },
                None,
                None,
            ),
            None,
        )?;

        assert!(!info.aborted);
        assert_eq!(
            info.storage_phase.unwrap().status_change,
            AccountStatusChange::Frozen
        );

        let ComputePhase::Executed(compute_phase) = info.compute_phase else {
            panic!("expected an executed compute phase");
        };
        assert!(compute_phase.success);

        let action_phase = info.action_phase.unwrap();
        assert!(action_phase.success);
        assert_eq!(action_phase.messages_created, 0);

        assert_eq!(info.bounce_phase, None);

        assert_eq!(state.orig_status, AccountStatus::Active);
        assert_eq!(state.end_status, AccountStatus::Frozen);
        assert_eq!(state.balance, CurrencyCollection::ZERO);

        assert_eq!(
            state.state,
            AccountState::Active(StateInit {
                code: Boc::decode(code).map(Some)?,
                data: CellBuilder::build_from(123u32).map(Some)?,
                ..Default::default()
            })
        );

        Ok(())
    }

    #[test]
    fn deleted_account_removes_public_libs() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();

        let code = tvmasm!(
            r#"
            ACCEPT
            // This library only exists during the action phase and must not appear in the diff.
            PUSHREF x{4444}
            INT 2 SETLIBCODE
            NEWC
            // int_msg_info$0 ihr_disabled:Bool bounce:Bool bounced:Bool src:MsgAddress -> 011000
            INT 0b011000 STUR 6
            MYADDR
            STSLICER
            INT 0 STGRAMS
            // extra:$0 ihr_fee:Tokens fwd_fee:Tokens created_lt:uint64 created_at:uint32
            // 1       + 4            + 4            + 64              + 32
            // init:none$0 body:left$0
            // 1          + 1
            INT 107 STZEROES
            ENDC INT 160 SENDRAWMSG
            "#
        );
        let public_lib_1 = make_library(0x1111);
        let public_lib_2 = make_library(0x2222);
        let private_lib = make_library(0x3333);

        let mut state = ExecutorState::new_active(
            &params,
            &config,
            &MASTERCHAIN_ADDR,
            Tokens::new(1_000_000_000),
            Cell::empty_cell(),
            code,
        );
        set_libraries(
            &mut state,
            make_libraries([(0x1111, true), (0x2222, true), (0x3333, false)]),
        );

        let mut inspector = ExecutorInspector::default();
        let info = state.run_ordinary_transaction(
            false,
            make_message(
                IntMsgInfo {
                    src: MASTERCHAIN_ADDR.into(),
                    dst: MASTERCHAIN_ADDR.into(),
                    value: CurrencyCollection::new(1_000_000_000),
                    ..Default::default()
                },
                None,
                None,
            ),
            Some(&mut inspector),
        )?;

        assert!(info.destroyed);
        assert_eq!(state.end_status, AccountStatus::NotExists);
        assert_eq!(
            info.action_phase.unwrap().status_change,
            AccountStatusChange::Deleted
        );
        assert_public_libs_diff(&inspector.public_libs_diff, &[], &[
            public_lib_1,
            public_lib_2,
        ]);
        assert!(
            !inspector
                .public_libs_diff
                .contains_key(private_lib.repr_hash())
        );
        assert!(
            !inspector
                .public_libs_diff
                .contains_key(make_library(0x4444).repr_hash())
        );

        Ok(())
    }

    #[test]
    fn frozen_account_removes_public_libs() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let public_lib_1 = make_library(0x1111);
        let public_lib_2 = make_library(0x2222);
        let private_lib = make_library(0x3333);

        let mut state = ExecutorState::new_active(
            &params,
            &config,
            &MASTERCHAIN_ADDR,
            Tokens::ZERO,
            Cell::empty_cell(),
            tvmasm!("ACCEPT"),
        );
        set_libraries(
            &mut state,
            make_libraries([(0x1111, true), (0x2222, true), (0x3333, false)]),
        );
        state.storage_stat = StorageInfo {
            used: StorageUsed {
                bits: VarUint56::new(128),
                cells: VarUint56::new(1),
            },
            storage_extra: Default::default(),
            last_paid: params.block_unixtime - 1000,
            due_payment: Some(Tokens::new(
                2 * config.mc_gas_prices.freeze_due_limit as u128,
            )),
        };

        let mut inspector = ExecutorInspector::default();
        let info = state.run_ordinary_transaction(
            false,
            make_message(
                IntMsgInfo {
                    src: MASTERCHAIN_ADDR.into(),
                    dst: MASTERCHAIN_ADDR.into(),
                    value: CurrencyCollection::new(1_000_000_000),
                    bounce: true,
                    ..Default::default()
                },
                None,
                None,
            ),
            Some(&mut inspector),
        )?;

        assert_eq!(
            info.storage_phase.unwrap().status_change,
            AccountStatusChange::Frozen
        );
        assert_eq!(state.end_status, AccountStatus::Frozen);
        assert_public_libs_diff(&inspector.public_libs_diff, &[], &[
            public_lib_1,
            public_lib_2,
        ]);
        assert!(
            !inspector
                .public_libs_diff
                .contains_key(private_lib.repr_hash())
        );

        Ok(())
    }

    #[test]
    fn unfrozen_account_adds_public_libs() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let public_lib_1 = make_library(0x1111);
        let public_lib_2 = make_library(0x2222);
        let private_lib = make_library(0x3333);
        let state_init = StateInit {
            code: Some(Boc::decode(tvmasm!("ACCEPT"))?),
            libraries: make_libraries([(0x1111, true), (0x2222, true), (0x3333, false)]),
            ..Default::default()
        };
        let state_init_hash = *CellBuilder::build_from(&state_init)?.repr_hash();
        let mut state = ExecutorState::new_frozen(
            &params,
            &config,
            &MASTERCHAIN_ADDR,
            Tokens::ZERO,
            state_init_hash,
        );

        let mut inspector = ExecutorInspector::default();
        let info = state.run_ordinary_transaction(
            false,
            make_message(
                IntMsgInfo {
                    src: MASTERCHAIN_ADDR.into(),
                    dst: MASTERCHAIN_ADDR.into(),
                    value: CurrencyCollection::new(1_000_000_000),
                    ..Default::default()
                },
                Some(state_init),
                None,
            ),
            Some(&mut inspector),
        )?;

        let ComputePhase::Executed(compute_phase) = info.compute_phase else {
            panic!("expected an executed compute phase");
        };
        assert!(compute_phase.success);
        assert!(compute_phase.account_activated);
        assert_eq!(state.end_status, AccountStatus::Active);
        assert_public_libs_diff(
            &inspector.public_libs_diff,
            &[public_lib_1, public_lib_2],
            &[],
        );
        assert!(
            !inspector
                .public_libs_diff
                .contains_key(private_lib.repr_hash())
        );

        Ok(())
    }

    #[test]
    fn unfrozen_account_adds_public_libs_with_actions() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let removed_lib = make_library(0x1111);
        let retained_lib = make_library(0x2222);
        let added_lib = make_library(0x4444);
        let state_init = StateInit {
            code: Some(Boc::decode(tvmasm!(
                r#"
                ACCEPT
                PUSHREF x{1111}
                INT 0 SETLIBCODE
                PUSHREF x{4444}
                INT 2 SETLIBCODE
                "#
            ))?),
            libraries: make_libraries([(0x1111, true), (0x2222, true), (0x3333, false)]),
            ..Default::default()
        };
        let state_init_hash = *CellBuilder::build_from(&state_init)?.repr_hash();
        let mut state = ExecutorState::new_frozen(
            &params,
            &config,
            &MASTERCHAIN_ADDR,
            Tokens::ZERO,
            state_init_hash,
        );

        let mut inspector = ExecutorInspector::default();
        let info = state.run_ordinary_transaction(
            false,
            make_message(
                IntMsgInfo {
                    src: MASTERCHAIN_ADDR.into(),
                    dst: MASTERCHAIN_ADDR.into(),
                    value: CurrencyCollection::new(1_000_000_000),
                    ..Default::default()
                },
                Some(state_init),
                None,
            ),
            Some(&mut inspector),
        )?;

        let action_phase = info.action_phase.unwrap();
        assert!(action_phase.success);
        assert_eq!(action_phase.special_actions, 2);
        let AccountState::Active(final_state) = &state.state else {
            panic!("expected active account state");
        };
        assert_eq!(
            final_state.libraries,
            make_libraries([(0x2222, true), (0x3333, false), (0x4444, true),])
        );
        assert_public_libs_diff(&inspector.public_libs_diff, &[retained_lib, added_lib], &[]);
        assert!(
            !inspector
                .public_libs_diff
                .contains_key(removed_lib.repr_hash())
        );

        Ok(())
    }

    #[test]
    fn deploy_with_libraries_fails() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let state_init = StateInit {
            code: Some(Boc::decode(tvmasm!("ACCEPT"))?),
            libraries: make_libraries([(0x1111, true)]),
            ..Default::default()
        };
        let address = StdAddr::new(-1, *CellBuilder::build_from(&state_init)?.repr_hash());
        let mut state = ExecutorState::new_uninit(&params, &config, &address, Tokens::ZERO);

        let mut inspector = ExecutorInspector::default();
        let info = state.run_ordinary_transaction(
            false,
            make_message(
                IntMsgInfo {
                    src: address.clone().into(),
                    dst: address.clone().into(),
                    value: CurrencyCollection::new(1_000_000_000),
                    ..Default::default()
                },
                Some(state_init),
                None,
            ),
            Some(&mut inspector),
        )?;

        let ComputePhase::Skipped(compute_phase) = info.compute_phase else {
            panic!("expected a skipped compute phase");
        };
        assert_eq!(compute_phase.reason, ComputePhaseSkipReason::BadState);
        assert_eq!(state.state, AccountState::Uninit);
        assert_eq!(state.end_status, AccountStatus::Uninit);
        assert!(inspector.public_libs_diff.is_empty());

        Ok(())
    }

    #[test]
    fn deploy_delete_in_same_tx() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();

        let code = Boc::decode(tvmasm!(
            r#"
            ACCEPT
            NEWC
            // int_msg_info$0 ihr_disabled:Bool bounce:Bool bounced:Bool src:MsgAddress -> 011000
            INT 0b011000 STUR 6
            MYADDR
            STSLICER
            INT 0 STGRAMS
            // extra:$0 ihr_fee:Tokens fwd_fee:Tokens created_lt:uint64 created_at:uint32
            // 1       + 4            + 4            + 64              + 32
            // init:none$0 body:left$0
            // 1          + 1
            INT 107 STZEROES
            ENDC INT 160 SENDRAWMSG
            "#
        ))?;
        let state_init = StateInit {
            code: Some(code),
            ..Default::default()
        };

        let address = StdAddr::new(0, *CellBuilder::build_from(&state_init)?.repr_hash());

        let msg_balance = Tokens::new(1_000_000_000);
        let msg = make_message(
            IntMsgInfo {
                src: address.clone().into(),
                dst: address.clone().into(),
                value: msg_balance.into(),
                ..Default::default()
            },
            Some(state_init),
            None,
        );

        let state = ShardAccount {
            account: Lazy::new(&OptionalAccount::EMPTY)?,
            last_trans_hash: HashBytes::ZERO,
            last_trans_lt: 0,
        };

        let output = Executor::new(&params, config.as_ref())
            .begin_ordinary(&address, false, msg, &state)?
            .commit()?;

        let new_account_state = output.new_state.load_account()?;
        assert_eq!(new_account_state, None);

        let tx = output.transaction.load()?;
        assert_eq!(tx.orig_status, AccountStatus::NotExists);
        assert_eq!(tx.end_status, AccountStatus::NotExists);

        let TxInfo::Ordinary(info) = tx.load_info()? else {
            panic!("expected an ordinary transaction info");
        };
        println!("{info:#?}");

        assert!(!info.aborted);
        assert!(info.destroyed);

        let ComputePhase::Executed(compute_phase) = info.compute_phase else {
            panic!("expected an executed compute phase");
        };
        assert!(compute_phase.success);
        let action_phase = info.action_phase.unwrap();
        assert!(action_phase.success);
        assert_eq!(action_phase.total_actions, 1);
        assert_eq!(action_phase.messages_created, 1);

        assert_eq!(output.transaction_meta.out_msgs.len(), 1);
        let out_msg = output.transaction_meta.out_msgs.last().unwrap().load()?;

        {
            let MsgInfo::Int(info) = out_msg.info else {
                panic!("expected an internal outbound message");
            };

            assert_eq!(info.src, address.clone().into());
            assert_eq!(info.dst, address.clone().into());
            assert!(info.value.other.is_empty());
            assert_eq!(
                info.value.tokens,
                msg_balance
                    - compute_phase.gas_fees
                    - action_phase.total_fwd_fees.unwrap_or_default()
            );

            assert_eq!(out_msg.init, None);
            assert_eq!(out_msg.body, Default::default());
        }

        Ok(())
    }
}
