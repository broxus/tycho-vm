use anyhow::Result;
use num_bigint::{BigInt, Sign};
use tycho_types::models::{
    AccountState, AccountStatus, ComputePhase, ComputePhaseSkipReason, CurrencyCollection,
    ExecutedComputePhase, IntAddr, IntMsgInfo, MsgType, SkippedComputePhase, StateInit, TickTock,
};
use tycho_types::num::Tokens;
use tycho_types::prelude::*;
use tycho_vm::{SafeRc, SmcInfoBase, Stack, Tuple, UnpackedInMsgSmcInfo, VmState, tuple};

use crate::phase::receive::{MsgStateInit, ReceivedMessage};
use crate::util::{
    StateLimitsResult, check_state_limits_diff, new_varuint24_truncate, new_varuint56_truncate,
    unlikely,
};
use crate::{ExecutorInspector, ExecutorState};

/// Compute phase input context.
pub struct ComputePhaseContext<'a, 'e> {
    /// Parsed transaction input.
    pub input: TransactionInput<'a>,
    /// Fees collected during the storage phase.
    pub storage_fee: Tokens,
    /// Accept message even without opcode.
    ///
    /// Should only be used as part of the `run_local` stuff.
    pub force_accept: bool,
    /// Executor inspector.
    pub inspector: Option<&'a mut ExecutorInspector<'e>>,
}

/// Parsed transaction input.
#[derive(Debug, Clone, Copy)]
pub enum TransactionInput<'a> {
    Ordinary(&'a ReceivedMessage),
    TickTock(TickTock),
}

impl<'a> TransactionInput<'a> {
    const fn is_ordinary(&self) -> bool {
        matches!(self, Self::Ordinary(_))
    }

    fn in_msg(&self) -> Option<&'a ReceivedMessage> {
        match self {
            Self::Ordinary(msg) => Some(msg),
            Self::TickTock(_) => None,
        }
    }

    fn in_msg_init(&self) -> Option<&'a MsgStateInit> {
        match self {
            Self::Ordinary(msg) => msg.init.as_ref(),
            Self::TickTock(_) => None,
        }
    }
}

/// Executed compute phase with additional info.
#[derive(Debug)]
pub struct ComputePhaseFull {
    /// Resulting comput phase.
    pub compute_phase: ComputePhase,
    /// Whether the inbound message was accepted.
    ///
    /// NOTE: Message can be accepted even without a committed state,
    /// so we can't use [`ExecutedComputePhase::success`].
    pub accepted: bool,
    /// Original account balance before this phase.
    pub original_balance: CurrencyCollection,
    /// New account state.
    pub new_state: StateInit,
    /// Resulting actions list.
    pub actions: Cell,
}

impl ExecutorState<'_> {
    /// Compute phase of ordinary or ticktock transactions.
    ///
    /// - Tries to deploy or unfreeze account if it was [`Uninit`] or [`Frozen`];
    /// - Executes contract code and produces a new account state;
    /// - Produces an action list on successful execution;
    /// - External messages can be ignored if they were not accepted;
    /// - Necessary for all types of messages or even without them;
    ///
    /// Returns an executed [`ComputePhase`] with extra data.
    ///
    /// Fails only on account balance overflow. This should not happen on networks
    /// with valid value flow.
    ///
    /// [`Uninit`]: AccountState::Uninit
    /// [`Frozen`]: AccountState::Frozen
    pub fn compute_phase(&mut self, ctx: ComputePhaseContext<'_, '_>) -> Result<ComputePhaseFull> {
        let is_masterchain = self.address.is_masterchain();

        // Compute original balance for the action phase.
        let mut original_balance = self.balance.clone();
        if let Some(msg) = ctx.input.in_msg() {
            original_balance.try_sub_assign(&msg.balance_remaining)?;
        }

        // Prepare full phase output.
        let new_state = if let AccountState::Active(current) = &self.state {
            current.clone()
        } else {
            Default::default()
        };

        let mut res = ComputePhaseFull {
            compute_phase: ComputePhase::Skipped(SkippedComputePhase {
                reason: ComputePhaseSkipReason::NoGas,
            }),
            accepted: false,
            original_balance,
            new_state,
            actions: Cell::empty_cell(),
        };

        // Compute VM gas limits.
        if self.balance.tokens.is_zero() {
            res.compute_phase = ComputePhase::Skipped(SkippedComputePhase {
                reason: ComputePhaseSkipReason::NoGas,
            });
            return Ok(res);
        }

        // Skip compute phase for accounts suspended by authority marks.
        if self.is_suspended_by_marks {
            res.compute_phase = ComputePhase::Skipped(SkippedComputePhase {
                reason: ComputePhaseSkipReason::Suspended,
            });
            return Ok(res);
        }

        let (msg_balance_remaining, is_external) = match ctx.input.in_msg() {
            Some(msg) => (msg.balance_remaining.clone(), msg.is_external),
            None => (CurrencyCollection::ZERO, false),
        };

        let gas = if unlikely(ctx.force_accept) {
            tycho_vm::GasParams::getter()
        } else {
            self.config.compute_gas_params(
                &self.balance.tokens,
                &msg_balance_remaining.tokens,
                self.is_special,
                is_masterchain,
                ctx.input.is_ordinary(),
                is_external,
            )
        };
        if gas.limit == 0 && gas.credit == 0 {
            res.compute_phase = ComputePhase::Skipped(SkippedComputePhase {
                reason: ComputePhaseSkipReason::NoGas,
            });
            return Ok(res);
        }

        // Apply internal message state.
        let state_libs;
        let msg_libs;
        let msg_state_used;
        match (ctx.input.in_msg_init(), &self.state) {
            // Uninit account cannot run anything without deploy.
            (None, AccountState::Uninit) => {
                res.compute_phase = ComputePhase::Skipped(SkippedComputePhase {
                    reason: ComputePhaseSkipReason::NoState,
                });
                return Ok(res);
            }
            // Frozen account cannot run anything until receives its old state.
            (None, AccountState::Frozen { .. }) => {
                res.compute_phase = ComputePhase::Skipped(SkippedComputePhase {
                    reason: ComputePhaseSkipReason::BadState,
                });
                return Ok(res);
            }
            // Active account simply runs its code. (use libraries from its state).
            (None, AccountState::Active(StateInit { libraries, .. })) => {
                state_libs = Some(libraries);
                msg_libs = None;
                msg_state_used = false;
            }
            // Received a new state init for an uninit account or an old state for a frozen account.
            (Some(from_msg), AccountState::Uninit | AccountState::Frozen(..)) => {
                let target_hash = if let AccountState::Frozen(old_hash) = &self.state {
                    old_hash
                } else {
                    &self.address.address
                };

                if from_msg.root_hash() != target_hash || from_msg.parsed.split_depth.is_some() {
                    // State hash mismatch, cannot use this state.
                    // We also forbid using `split_depth` (for now).
                    res.compute_phase = ComputePhase::Skipped(SkippedComputePhase {
                        reason: ComputePhaseSkipReason::BadState,
                    });
                    return Ok(res);
                }

                // Check if we can use the new state from the message.
                let mut limits = self.config.size_limits.clone();
                if is_masterchain && matches!(&self.state, AccountState::Uninit) {
                    // Forbid public libraries when deploying, allow for unfreezing.
                    limits.max_acc_public_libraries = 0;
                }

                if matches!(
                    check_state_limits_diff(
                        &res.new_state,
                        &from_msg.parsed,
                        &limits,
                        is_masterchain,
                        &mut self.cached_storage_stat,
                    ),
                    StateLimitsResult::Exceeds
                ) {
                    res.compute_phase = ComputePhase::Skipped(SkippedComputePhase {
                        reason: ComputePhaseSkipReason::BadState,
                    });
                    return Ok(res);
                }

                // NOTE: At this point the `cached_storage_stat` will always contain
                // visited cells because previous state was not active and we
                // handled a case when check overflowed.

                // Use state
                res.new_state = from_msg.parsed.clone();
                self.state = AccountState::Active(res.new_state.clone());
                msg_state_used = true;

                // Use libraries.
                state_libs = None;
                msg_libs = Some(from_msg.parsed.libraries.clone());
            }
            (Some(from_msg), AccountState::Active(StateInit { libraries, .. })) => {
                // Check if a state from the external message has the correct hash.
                if is_external && from_msg.root_hash() != &self.address.address {
                    res.compute_phase = ComputePhase::Skipped(SkippedComputePhase {
                        reason: ComputePhaseSkipReason::BadState,
                    });
                    return Ok(res);
                }

                // We use only libraries here.
                msg_state_used = false;

                // Use libraries.
                state_libs = Some(libraries);
                msg_libs = Some(from_msg.parsed.libraries.clone());
            }
        }

        // Unpack internal message.
        let unpacked_in_msg = match ctx.input.in_msg() {
            Some(msg) => msg.make_tuple()?,
            None => None,
        };

        // Build VM stack and register info.
        let stack = self.prepare_vm_stack(ctx.input);

        let code = res.new_state.code.clone();

        let smc_info = SmcInfoBase::new()
            .with_now(self.params.block_unixtime)
            .with_block_lt(self.params.block_lt)
            .with_tx_lt(self.start_lt)
            .with_mixed_rand_seed(&self.params.rand_seed, &self.address.address)
            .with_account_balance(self.balance.clone())
            .with_account_addr(self.address.clone().into())
            .with_config(self.config.raw.params.clone())
            .require_ton_v4()
            .with_code(code.clone().unwrap_or_default())
            .with_message_balance(msg_balance_remaining.clone())
            .with_storage_fees(ctx.storage_fee)
            .require_ton_v6()
            .with_unpacked_config(self.config.unpacked.as_tuple())
            .require_ton_v11()
            .with_unpacked_in_msg(unpacked_in_msg);

        let libraries = (msg_libs, state_libs, &self.params.libraries);
        let mut vm = VmState::builder()
            .with_smc_info(smc_info)
            .with_code(code)
            .with_data(res.new_state.data.clone().unwrap_or_default())
            .with_libraries(&libraries)
            .with_init_selector(false)
            .with_raw_stack(stack)
            .with_gas(gas)
            .with_modifiers(self.params.vm_modifiers)
            .build();

        // Connect inspected output as debug.
        let mut inspector_actions = None;
        let mut inspector_exit_code = None;
        let mut inspector_total_gas_used = None;
        if let Some(inspector) = ctx.inspector {
            inspector_actions = Some(&mut inspector.actions);
            inspector_exit_code = Some(&mut inspector.exit_code);
            inspector_total_gas_used = Some(&mut inspector.total_gas_used);
            if let Some(debug) = inspector.debug.as_deref_mut() {
                vm.debug = Some(debug);
            }
        }

        // Run VM.
        let exit_code = !vm.run();

        if let Some(inspector_exit_code) = inspector_exit_code {
            *inspector_exit_code = Some(exit_code);
        }

        let consumed_paid_gas = vm.gas.consumed();
        if let Some(total_gas_used) = inspector_total_gas_used {
            *total_gas_used = consumed_paid_gas.saturating_add(vm.gas.free_gas_consumed());
        }

        // Parse VM state.
        res.accepted = ctx.force_accept || vm.gas.credit() == 0;
        debug_assert!(
            is_external || res.accepted,
            "internal messages must be accepted"
        );

        let success = res.accepted && vm.committed_state.is_some();

        let gas_used = std::cmp::min(consumed_paid_gas, vm.gas.limit());
        let gas_fees = if res.accepted && !self.is_special {
            self.config
                .gas_prices(is_masterchain)
                .compute_gas_fee(gas_used)
        } else {
            // We don't add any fees for messages that were not accepted.
            Tokens::ZERO
        };

        let mut account_activated = false;
        if res.accepted && msg_state_used {
            account_activated = self.orig_status != AccountStatus::Active;
            self.end_status = AccountStatus::Active;
        }

        if let Some(committed) = vm.committed_state
            && res.accepted
        {
            res.new_state.data = Some(committed.c4);
            res.actions = committed.c5;

            // Set inspector actions.
            if let Some(actions) = inspector_actions {
                *actions = Some(res.actions.clone());
            }
        }

        self.balance.try_sub_assign_tokens(gas_fees)?;
        self.total_fees.try_add_assign(gas_fees)?;

        res.compute_phase = ComputePhase::Executed(ExecutedComputePhase {
            success,
            msg_state_used,
            account_activated,
            gas_fees,
            gas_used: new_varuint56_truncate(gas_used),
            // NOTE: Initial value is stored here (not `vm.gas.limit()`).
            gas_limit: new_varuint56_truncate(gas.limit),
            // NOTE: Initial value is stored here (not `vm.gas.credit()`).
            gas_credit: (gas.credit != 0).then(|| new_varuint24_truncate(gas.credit)),
            mode: 0,
            exit_code,
            exit_arg: if success {
                None
            } else {
                vm.stack.get_exit_arg().filter(|x| *x != 0)
            },
            vm_steps: vm.steps.try_into().unwrap_or(u32::MAX),
            vm_init_state_hash: HashBytes::ZERO,
            vm_final_state_hash: HashBytes::ZERO,
        });
        Ok(res)
    }

    fn prepare_vm_stack(&self, input: TransactionInput<'_>) -> SafeRc<Stack> {
        SafeRc::new(Stack::with_items(match input {
            TransactionInput::Ordinary(msg) => {
                tuple![
                    int self.balance.tokens,
                    int msg.balance_remaining.tokens,
                    cell msg.root.clone(),
                    slice msg.body.clone(),
                    int if msg.is_external { -1 } else { 0 },
                ]
            }
            TransactionInput::TickTock(ty) => {
                tuple![
                    int self.balance.tokens,
                    int BigInt::from_bytes_be(Sign::Plus, self.address.address.as_array()),
                    int match ty {
                        TickTock::Tick => 0,
                        TickTock::Tock => -1,
                    },
                    int -2,
                ]
            }
        }))
    }
}

impl ReceivedMessage {
    fn make_tuple(&self) -> Result<Option<SafeRc<Tuple>>, tycho_types::error::Error> {
        let mut cs = self.root.as_slice()?;
        if MsgType::load_from(&mut cs)? != MsgType::Int {
            return Ok(None);
        }

        // Get `src` addr range.
        let src_addr_slice = {
            let mut cs = cs;
            // Skip flags.
            cs.skip_first(3, 0)?;
            let mut addr_slice = cs;
            // Read `src`.
            IntAddr::load_from(&mut cs)?;
            addr_slice.skip_last(cs.size_bits(), cs.size_refs())?;
            addr_slice.range()
        };

        let info = IntMsgInfo::load_from(&mut cs)?;

        let unpacked = UnpackedInMsgSmcInfo {
            bounce: info.bounce,
            bounced: info.bounced,
            src_addr: (src_addr_slice, self.root.clone()).into(),
            fwd_fee: info.fwd_fee,
            created_lt: info.created_lt,
            created_at: info.created_at,
            original_value: info.value.tokens,
            remaining_value: self.balance_remaining.clone(),
            state_init: self.init.as_ref().map(|init| init.root.clone()),
        };
        Ok(Some(unpacked.into_tuple()))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use tycho_asm_macros::tvmasm;
    use tycho_types::models::{
        AuthorityMarksConfig, ExtInMsgInfo, IntMsgInfo, LibDescr, SimpleLib, StdAddr,
    };
    use tycho_types::num::{VarUint24, VarUint56, VarUint248};

    use super::*;
    use crate::ExecutorParams;
    use crate::tests::{
        make_custom_config, make_default_config, make_default_params, make_message,
    };

    const STUB_ADDR: StdAddr = StdAddr::new(0, HashBytes::ZERO);
    const OK_BALANCE: Tokens = Tokens::new(1_000_000_000);

    fn empty_ext_in_msg(addr: &StdAddr) -> Cell {
        make_message(
            ExtInMsgInfo {
                dst: addr.clone().into(),
                ..Default::default()
            },
            None,
            None,
        )
    }

    fn empty_int_msg(addr: &StdAddr, value: impl Into<CurrencyCollection>) -> Cell {
        make_message(
            IntMsgInfo {
                src: addr.clone().into(),
                dst: addr.clone().into(),
                value: value.into(),
                ..Default::default()
            },
            None,
            None,
        )
    }

    fn simple_state(code: &[u8]) -> StateInit {
        StateInit {
            split_depth: None,
            special: None,
            code: Some(Boc::decode(code).unwrap()),
            data: None,
            libraries: Dict::new(),
        }
    }

    fn init_tracing() {
        tracing_subscriber::fmt::fmt()
            .with_env_filter("tycho_vm=trace")
            .with_writer(tracing_subscriber::fmt::TestWriter::new)
            .try_init()
            .ok();
    }

    fn make_lib_ref(code: &DynCell) -> Cell {
        let mut b = CellBuilder::new();
        b.set_exotic(true);
        b.store_u8(CellType::LibraryReference.to_byte()).unwrap();
        b.store_u256(code.repr_hash()).unwrap();
        b.build().unwrap()
    }

    #[test]
    fn ext_in_run_no_accept() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_active(
            &params,
            &config,
            &STUB_ADDR,
            OK_BALANCE,
            Cell::empty_cell(),
            tvmasm!("INT 123 NOP"),
        );

        let msg = state.receive_in_msg(empty_ext_in_msg(&state.address))?;

        let prev_balance = state.balance.clone();
        let prev_state = state.state.clone();
        let prev_total_fees = state.total_fees;
        let prev_end_status = state.end_status;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(prev_balance, compute_phase.original_balance);
        // Message must not be accepted.
        assert!(!compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(prev_end_status, state.end_status);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // No fees must be paid when message was not accepted.
        assert_eq!(state.total_fees, prev_total_fees);
        assert_eq!(state.balance, prev_balance);

        let ComputePhase::Executed(compute_phase) = compute_phase.compute_phase else {
            panic!("expected executed compute phase");
        };

        assert!(!compute_phase.success);
        assert!(!compute_phase.msg_state_used);
        assert!(!compute_phase.account_activated);
        assert_eq!(compute_phase.gas_fees, Tokens::ZERO);
        assert_eq!(compute_phase.gas_used, VarUint56::new(0)); // only credit was used
        assert_eq!(compute_phase.gas_limit, VarUint56::new(0)); // zero, for external messages before accept
        assert_eq!(compute_phase.gas_credit, Some(VarUint24::new(10_000)));
        assert_eq!(compute_phase.exit_code, 0);
        assert_eq!(compute_phase.exit_arg, Some(123)); // top int is treated as exit arg if !success
        assert_eq!(compute_phase.vm_steps, 3); // pushint, nop, implicit ret

        Ok(())
    }

    #[test]
    fn ext_in_run_uninit_no_accept() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE);

        let msg = state.receive_in_msg(empty_ext_in_msg(&state.address))?;

        let prev_balance = state.balance.clone();
        let prev_state = state.state.clone();
        let prev_total_fees = state.total_fees;
        let prev_end_status = state.end_status;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(prev_balance, compute_phase.original_balance);
        // Message must not be accepted.
        assert!(!compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(prev_end_status, state.end_status);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // No fees must be paid when message was not accepted.
        assert_eq!(state.total_fees, prev_total_fees);
        assert_eq!(state.balance, prev_balance);

        let ComputePhase::Skipped(compute_phase) = compute_phase.compute_phase else {
            panic!("expected skipped compute phase");
        };
        assert_eq!(compute_phase.reason, ComputePhaseSkipReason::NoState);

        Ok(())
    }

    #[test]
    fn ext_in_run_no_code_no_accept() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE);
        state.state = AccountState::Active(StateInit::default());
        state.orig_status = AccountStatus::Active;
        state.end_status = AccountStatus::Active;

        let msg = state.receive_in_msg(empty_ext_in_msg(&state.address))?;

        let prev_balance = state.balance.clone();
        let prev_state = state.state.clone();
        let prev_total_fees = state.total_fees;
        let prev_end_status = state.end_status;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(prev_balance, compute_phase.original_balance);
        // Message must not be accepted.
        assert!(!compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(prev_end_status, state.end_status);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // No fees must be paid when message was not accepted.
        assert_eq!(state.total_fees, prev_total_fees);
        assert_eq!(state.balance, prev_balance);

        let ComputePhase::Executed(compute_phase) = compute_phase.compute_phase else {
            panic!("expected executed compute phase");
        };

        assert!(!compute_phase.success);
        assert!(!compute_phase.msg_state_used);
        assert!(!compute_phase.account_activated);
        assert_eq!(compute_phase.gas_fees, Tokens::ZERO);
        assert_eq!(compute_phase.gas_used, VarUint56::new(0)); // only credit was used
        assert_eq!(compute_phase.gas_limit, VarUint56::new(0)); // zero, for external messages before accept
        assert_eq!(compute_phase.gas_credit, Some(VarUint24::new(10_000)));
        assert_eq!(
            compute_phase.exit_code,
            tycho_vm::VmException::Fatal.as_exit_code()
        );
        assert_eq!(compute_phase.exit_arg, Some(-1)); // top int is treated as exit arg if !success
        assert_eq!(compute_phase.vm_steps, 0);

        Ok(())
    }

    #[test]
    fn ext_in_accept_no_commit() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_active(
            &params,
            &config,
            &STUB_ADDR,
            OK_BALANCE,
            Cell::empty_cell(),
            tvmasm!("ACCEPT THROW 42"),
        );

        let msg = state.receive_in_msg(empty_ext_in_msg(&state.address))?;

        let prev_balance = state.balance.clone();
        let prev_state = state.state.clone();
        let prev_total_fees = state.total_fees;
        let prev_end_status = state.end_status;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(prev_balance, compute_phase.original_balance);
        // Message must be accepted.
        assert!(compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(prev_end_status, state.end_status);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // Fees must be paid.
        let expected_gas_fee = Tokens::new(config.gas_prices.flat_gas_price as _);
        assert_eq!(state.total_fees, prev_total_fees + expected_gas_fee);
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(state.balance.tokens, prev_balance.tokens - expected_gas_fee);

        let ComputePhase::Executed(compute_phase) = compute_phase.compute_phase else {
            panic!("expected executed compute phase");
        };

        assert!(!compute_phase.success);
        assert!(!compute_phase.msg_state_used);
        assert!(!compute_phase.account_activated);
        assert_eq!(compute_phase.gas_fees, expected_gas_fee);
        assert_eq!(compute_phase.gas_used, (10 + 16) * 2 + 50); // two 16bit opcodes + exception
        assert_eq!(compute_phase.gas_limit, VarUint56::ZERO);
        assert_eq!(compute_phase.gas_credit, Some(VarUint24::new(10_000)));
        assert_eq!(compute_phase.exit_code, 42);
        assert_eq!(compute_phase.exit_arg, None);
        assert_eq!(compute_phase.vm_steps, 2); // accept, throw

        Ok(())
    }

    #[test]
    fn ext_in_accept_invalid_commit() -> Result<()> {
        init_tracing();
        let params = make_default_params();
        let config = make_default_config();

        let mut state = ExecutorState::new_active(
            &params,
            &config,
            &STUB_ADDR,
            OK_BALANCE,
            Cell::empty_cell(),
            tvmasm!(
                r#"
                ACCEPT
                NEWC
                INT 1 STUR 8
                INT 7 STUR 8
                INT 816 STZEROES
                TRUE ENDXC
                POP c5
                "#
            ),
        );

        let msg = state.receive_in_msg(empty_ext_in_msg(&state.address))?;

        let prev_balance = state.balance.clone();
        let prev_state = state.state.clone();
        let prev_total_fees = state.total_fees;
        let prev_end_status = state.end_status;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(prev_balance, compute_phase.original_balance);
        // Message must be accepted.
        assert!(compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(prev_end_status, state.end_status);
        // No (VALID) actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // Fees must be paid.
        let expected_gas_fee = Tokens::new(config.gas_prices.flat_gas_price as _);
        assert_eq!(state.total_fees, prev_total_fees + expected_gas_fee);
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(state.balance.tokens, prev_balance.tokens - expected_gas_fee);

        let ComputePhase::Executed(compute_phase) = compute_phase.compute_phase else {
            panic!("expected executed compute phase");
        };

        assert!(!compute_phase.success);
        assert!(!compute_phase.msg_state_used);
        assert!(!compute_phase.account_activated);
        assert_eq!(compute_phase.gas_fees, expected_gas_fee);
        assert_eq!(compute_phase.gas_used, 783);
        assert_eq!(compute_phase.gas_limit, VarUint56::ZERO);
        assert_eq!(compute_phase.gas_credit, Some(VarUint24::new(10_000)));
        assert_eq!(
            compute_phase.exit_code,
            tycho_vm::VmException::CellOverflow as i32
        );
        assert_eq!(compute_phase.exit_arg, None);
        assert_eq!(compute_phase.vm_steps, 12); // accept, throw

        Ok(())
    }

    #[test]
    fn suspended_account_skips_compute() -> Result<()> {
        let params = ExecutorParams {
            authority_marks_enabled: true,
            ..make_default_params()
        };

        let config = make_custom_config(|config| {
            config.set_authority_marks_config(&AuthorityMarksConfig {
                authority_addresses: Dict::new(),
                black_mark_id: 100,
                white_mark_id: 101,
            })?;
            Ok(())
        });

        let mut state = ExecutorState::new_active(
            &params,
            &config,
            &STUB_ADDR,
            CurrencyCollection {
                tokens: OK_BALANCE,
                other: BTreeMap::from_iter([
                    (100u32, VarUint248::new(500)), // blocked by black marks
                ])
                .try_into()?,
            },
            CellBuilder::build_from(u32::MIN)?,
            tvmasm!("ACCEPT"),
        );

        let msg = state.receive_in_msg(empty_int_msg(&STUB_ADDR, OK_BALANCE))?;
        state.credit_phase(&msg)?;

        let prev_balance = state.balance.clone();
        let prev_state = state.state.clone();
        let prev_total_fees = state.total_fees;
        let prev_end_status = state.end_status;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Message must not be accepted.
        assert!(!compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(prev_end_status, state.end_status);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // No fees must be paid when message was not accepted.
        assert_eq!(state.total_fees, prev_total_fees);
        assert_eq!(state.balance, prev_balance);

        let ComputePhase::Skipped(compute_phase) = compute_phase.compute_phase else {
            panic!("expected skipped compute phase");
        };
        assert_eq!(compute_phase.reason, ComputePhaseSkipReason::Suspended);

        Ok(())
    }

    #[test]
    fn cant_suspend_authority_address() -> Result<()> {
        let params = ExecutorParams {
            authority_marks_enabled: true,
            ..make_default_params()
        };
        let config = make_custom_config(|config| {
            config.set_authority_marks_config(&AuthorityMarksConfig {
                authority_addresses: Dict::try_from_btree(&BTreeMap::from_iter([(
                    HashBytes::ZERO,
                    (),
                )]))?,
                black_mark_id: 100,
                white_mark_id: 101,
            })?;
            Ok(())
        });

        let mut state = ExecutorState::new_active(
            &params,
            &config,
            &StdAddr::new(-1, HashBytes::ZERO),
            CurrencyCollection {
                tokens: OK_BALANCE,
                other: BTreeMap::from_iter([
                    (100u32, VarUint248::new(1000)), // more black barks than white
                    (101u32, VarUint248::new(100)),
                ])
                .try_into()?,
            },
            Cell::default(),
            tvmasm!("ACCEPT"),
        );

        let msg = state.receive_in_msg(empty_ext_in_msg(&state.address))?;

        let prev_balance = state.balance.clone();
        let prev_state = state.state.clone();
        let prev_total_fees = state.total_fees;
        let prev_end_status = state.end_status;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(prev_balance, compute_phase.original_balance);
        // Message must be accepted.
        assert!(compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(prev_end_status, state.end_status);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // Fees must be paid.
        let expected_gas_fee = Tokens::new(config.mc_gas_prices.flat_gas_price as _);
        assert_eq!(state.total_fees, prev_total_fees + expected_gas_fee);
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(state.balance.tokens, prev_balance.tokens - expected_gas_fee);

        let ComputePhase::Executed(compute_phase) = compute_phase.compute_phase else {
            panic!("expected executed compute phase");
        };

        assert!(compute_phase.success);
        assert!(!compute_phase.msg_state_used);
        assert!(!compute_phase.account_activated);
        assert_eq!(compute_phase.gas_fees, expected_gas_fee);
        assert_eq!(compute_phase.gas_used, 31);
        assert_eq!(compute_phase.gas_limit, VarUint56::ZERO);
        assert_eq!(compute_phase.gas_credit, Some(VarUint24::new(10_000)));
        assert_eq!(compute_phase.exit_code, 0);
        assert_eq!(compute_phase.exit_arg, None);
        assert_eq!(compute_phase.vm_steps, 2);

        Ok(())
    }

    #[test]
    fn ext_in_accept_simple() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_active(
            &params,
            &config,
            &STUB_ADDR,
            OK_BALANCE,
            Cell::empty_cell(),
            tvmasm!("ACCEPT NEWC INT 0xdeafbeaf STUR 32 ENDC POP c5"),
        );

        let msg = state.receive_in_msg(empty_ext_in_msg(&state.address))?;

        let prev_balance = state.balance.clone();
        let prev_state = state.state.clone();
        let prev_total_fees = state.total_fees;
        let prev_end_status = state.end_status;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(prev_balance, compute_phase.original_balance);
        // Message must be accepted.
        assert!(compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(prev_end_status, state.end_status);
        // No actions must be produced.
        assert_eq!(
            compute_phase.actions,
            CellBuilder::build_from(0xdeafbeafu32)?
        );
        // Fees must be paid.
        let expected_gas_fee = Tokens::new(config.gas_prices.flat_gas_price as _);
        assert_eq!(state.total_fees, prev_total_fees + expected_gas_fee);
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(state.balance.tokens, prev_balance.tokens - expected_gas_fee);

        let ComputePhase::Executed(compute_phase) = compute_phase.compute_phase else {
            panic!("expected executed compute phase");
        };

        assert!(compute_phase.success);
        assert!(!compute_phase.msg_state_used);
        assert!(!compute_phase.account_activated);
        assert_eq!(compute_phase.gas_fees, expected_gas_fee);
        assert_eq!(compute_phase.gas_used, 650);
        assert_eq!(compute_phase.gas_limit, VarUint56::ZERO);
        assert_eq!(compute_phase.gas_credit, Some(VarUint24::new(10_000)));
        assert_eq!(compute_phase.exit_code, 0);
        assert_eq!(compute_phase.exit_arg, None);
        assert_eq!(compute_phase.vm_steps, 7);

        Ok(())
    }

    #[test]
    fn internal_accept_simple() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_active(
            &params,
            &config,
            &STUB_ADDR,
            OK_BALANCE,
            Cell::empty_cell(),
            tvmasm!("ACCEPT"),
        );

        let msg =
            state.receive_in_msg(empty_int_msg(&state.address, Tokens::new(1_000_000_000)))?;

        state.credit_phase(&msg)?;

        let prev_balance = state.balance.clone();
        let prev_state = state.state.clone();
        let prev_total_fees = state.total_fees;
        let prev_end_status = state.end_status;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(
            compute_phase.original_balance,
            CurrencyCollection::from(OK_BALANCE)
        );
        // Message must be accepted.
        assert!(compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(prev_end_status, state.end_status);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // Fees must be paid.
        let expected_gas_fee = Tokens::new(config.gas_prices.flat_gas_price as _);
        assert_eq!(state.total_fees, prev_total_fees + expected_gas_fee);
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(state.balance.tokens, prev_balance.tokens - expected_gas_fee);

        let ComputePhase::Executed(compute_phase) = compute_phase.compute_phase else {
            panic!("expected executed compute phase");
        };

        assert!(compute_phase.success);
        assert!(!compute_phase.msg_state_used);
        assert!(!compute_phase.account_activated);
        assert_eq!(compute_phase.gas_fees, expected_gas_fee);
        assert_eq!(compute_phase.gas_used, (10 + 16) + 5); // two 16bit opcodes + implicit ret
        assert_eq!(
            compute_phase.gas_limit,
            VarUint56::new(config.gas_prices.gas_limit)
        );
        assert_eq!(compute_phase.gas_credit, None);
        assert_eq!(compute_phase.exit_code, 0);
        assert_eq!(compute_phase.exit_arg, None);
        assert_eq!(compute_phase.vm_steps, 2); // accept, implicit ret

        Ok(())
    }

    #[test]
    fn internal_no_accept() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_active(
            &params,
            &config,
            &STUB_ADDR,
            OK_BALANCE,
            Cell::empty_cell(),
            tvmasm!("NOP"),
        );

        let msg = state.receive_in_msg(empty_int_msg(&state.address, Tokens::new(1)))?;

        state.credit_phase(&msg)?;

        let prev_balance = state.balance.clone();
        let prev_state = state.state.clone();
        let prev_total_fees = state.total_fees;
        let prev_end_status = state.end_status;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(
            compute_phase.original_balance,
            CurrencyCollection::from(OK_BALANCE)
        );
        // Message must not be accepted.
        assert!(!compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(prev_end_status, state.end_status);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // No fees must be paid when message was not accepted.
        assert_eq!(state.total_fees, prev_total_fees);
        assert_eq!(state.balance, prev_balance);

        let ComputePhase::Skipped(compute_phase) = compute_phase.compute_phase else {
            panic!("expected skipped compute phase");
        };
        assert_eq!(compute_phase.reason, ComputePhaseSkipReason::NoGas);

        Ok(())
    }

    #[test]
    fn internal_no_accept_empty_balance() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_active(
            &params,
            &config,
            &STUB_ADDR,
            Tokens::ZERO,
            Cell::empty_cell(),
            tvmasm!("NOP"),
        );

        let msg = state.receive_in_msg(empty_int_msg(&state.address, Tokens::ZERO))?;

        state.credit_phase(&msg)?;

        let prev_balance = state.balance.clone();
        let prev_state = state.state.clone();
        let prev_total_fees = state.total_fees;
        let prev_end_status = state.end_status;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(compute_phase.original_balance, CurrencyCollection::ZERO);
        // Message must not be accepted.
        assert!(!compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(prev_end_status, state.end_status);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // No fees must be paid when message was not accepted.
        assert_eq!(state.total_fees, prev_total_fees);
        assert_eq!(state.balance, prev_balance);

        let ComputePhase::Skipped(compute_phase) = compute_phase.compute_phase else {
            panic!("expected skipped compute phase");
        };
        assert_eq!(compute_phase.reason, ComputePhaseSkipReason::NoGas);

        Ok(())
    }

    #[test]
    fn ext_in_deploy_account() -> Result<()> {
        let state_init = simple_state(tvmasm!("ACCEPT"));
        let state_init_hash = *CellBuilder::build_from(&state_init)?.repr_hash();
        let addr = StdAddr::new(0, state_init_hash);

        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_uninit(&params, &config, &addr, OK_BALANCE);

        let msg = state.receive_in_msg(make_message(
            ExtInMsgInfo {
                dst: addr.clone().into(),
                ..Default::default()
            },
            Some(state_init.clone()),
            None,
        ))?;

        let prev_balance = state.balance.clone();
        let prev_total_fees = state.total_fees;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(
            compute_phase.original_balance,
            CurrencyCollection::from(OK_BALANCE - prev_total_fees)
        );
        // Message must be accepted.
        assert!(compute_phase.accepted);
        // State must change.
        assert_eq!(state.state, AccountState::Active(state_init));
        // Status must change.
        assert_eq!(state.end_status, AccountStatus::Active);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // Fees must be paid.
        let expected_gas_fee = Tokens::new(config.gas_prices.flat_gas_price as _);
        assert_eq!(state.total_fees, prev_total_fees + expected_gas_fee);
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(state.balance.tokens, prev_balance.tokens - expected_gas_fee);

        let ComputePhase::Executed(compute_phase) = compute_phase.compute_phase else {
            panic!("expected executed compute phase");
        };

        assert!(compute_phase.success);
        assert!(compute_phase.msg_state_used);
        assert!(compute_phase.account_activated);
        assert_eq!(compute_phase.gas_fees, expected_gas_fee);
        assert_eq!(compute_phase.gas_used, (10 + 16) + 5); // two 16bit opcodes + implicit ret
        assert_eq!(compute_phase.gas_limit, VarUint56::ZERO);
        assert_eq!(compute_phase.gas_credit, Some(VarUint24::new(10_000)));
        assert_eq!(compute_phase.exit_code, 0);
        assert_eq!(compute_phase.exit_arg, None);
        assert_eq!(compute_phase.vm_steps, 2); // accept, implicit ret

        Ok(())
    }

    #[test]
    fn internal_deploy_account() -> Result<()> {
        let state_init = simple_state(tvmasm!("ACCEPT"));
        let state_init_hash = *CellBuilder::build_from(&state_init)?.repr_hash();
        let addr = StdAddr::new(0, state_init_hash);

        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_uninit(&params, &config, &addr, OK_BALANCE);

        let msg = state.receive_in_msg(make_message(
            IntMsgInfo {
                src: addr.clone().into(),
                dst: addr.clone().into(),
                value: Tokens::new(1_000_000_000).into(),
                ..Default::default()
            },
            Some(state_init.clone()),
            None,
        ))?;

        state.credit_phase(&msg)?;

        let prev_balance = state.balance.clone();
        let prev_total_fees = state.total_fees;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(
            compute_phase.original_balance,
            CurrencyCollection::from(OK_BALANCE)
        );
        // Message must be accepted.
        assert!(compute_phase.accepted);
        // State must change.
        assert_eq!(state.state, AccountState::Active(state_init));
        // Status must change.
        assert_eq!(state.end_status, AccountStatus::Active);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // Fees must be paid.
        let expected_gas_fee = Tokens::new(config.gas_prices.flat_gas_price as _);
        assert_eq!(state.total_fees, prev_total_fees + expected_gas_fee);
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(state.balance.tokens, prev_balance.tokens - expected_gas_fee);

        let ComputePhase::Executed(compute_phase) = compute_phase.compute_phase else {
            panic!("expected executed compute phase");
        };

        assert!(compute_phase.success);
        assert!(compute_phase.msg_state_used);
        assert!(compute_phase.account_activated);
        assert_eq!(compute_phase.gas_fees, expected_gas_fee);
        assert_eq!(compute_phase.gas_used, (10 + 16) + 5); // two 16bit opcodes + implicit ret
        assert_eq!(
            compute_phase.gas_limit,
            VarUint56::new(config.gas_prices.gas_limit)
        );
        assert_eq!(compute_phase.gas_credit, None);
        assert_eq!(compute_phase.exit_code, 0);
        assert_eq!(compute_phase.exit_arg, None);
        assert_eq!(compute_phase.vm_steps, 2); // accept, implicit ret

        Ok(())
    }

    #[test]
    fn ext_in_unfreeze_account() -> Result<()> {
        let state_init = simple_state(tvmasm!("ACCEPT"));
        let state_init_hash = *CellBuilder::build_from(&state_init)?.repr_hash();

        let params = make_default_params();
        let config = make_default_config();
        let mut state =
            ExecutorState::new_frozen(&params, &config, &STUB_ADDR, OK_BALANCE, state_init_hash);

        let msg = state.receive_in_msg(make_message(
            ExtInMsgInfo {
                dst: STUB_ADDR.into(),
                ..Default::default()
            },
            Some(state_init.clone()),
            None,
        ))?;

        let prev_balance = state.balance.clone();
        let prev_total_fees = state.total_fees;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(
            compute_phase.original_balance,
            CurrencyCollection::from(OK_BALANCE - prev_total_fees)
        );
        // Message must be accepted.
        assert!(compute_phase.accepted);
        // State must change.
        assert_eq!(state.state, AccountState::Active(state_init));
        // Status must change.
        assert_eq!(state.end_status, AccountStatus::Active);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // Fees must be paid.
        let expected_gas_fee = Tokens::new(config.gas_prices.flat_gas_price as _);
        assert_eq!(state.total_fees, prev_total_fees + expected_gas_fee);
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(state.balance.tokens, prev_balance.tokens - expected_gas_fee);

        let ComputePhase::Executed(compute_phase) = compute_phase.compute_phase else {
            panic!("expected executed compute phase");
        };

        assert!(compute_phase.success);
        assert!(compute_phase.msg_state_used);
        assert!(compute_phase.account_activated);
        assert_eq!(compute_phase.gas_fees, expected_gas_fee);
        assert_eq!(compute_phase.gas_used, (10 + 16) + 5); // two 16bit opcodes + implicit ret
        assert_eq!(compute_phase.gas_limit, VarUint56::ZERO);
        assert_eq!(compute_phase.gas_credit, Some(VarUint24::new(10_000)));
        assert_eq!(compute_phase.exit_code, 0);
        assert_eq!(compute_phase.exit_arg, None);
        assert_eq!(compute_phase.vm_steps, 2); // accept, implicit ret

        Ok(())
    }

    #[test]
    fn internal_unfreeze_account() -> Result<()> {
        let state_init = simple_state(tvmasm!("ACCEPT"));
        let state_init_hash = *CellBuilder::build_from(&state_init)?.repr_hash();

        let params = make_default_params();
        let config = make_default_config();
        let mut state =
            ExecutorState::new_frozen(&params, &config, &STUB_ADDR, Tokens::ZERO, state_init_hash);

        let msg = state.receive_in_msg(make_message(
            IntMsgInfo {
                src: STUB_ADDR.into(),
                dst: STUB_ADDR.into(),
                value: Tokens::new(1_000_000_000).into(),
                ..Default::default()
            },
            Some(state_init.clone()),
            None,
        ))?;

        state.credit_phase(&msg)?;

        let prev_balance = state.balance.clone();
        let prev_total_fees = state.total_fees;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(compute_phase.original_balance, CurrencyCollection::ZERO);
        // Message must be accepted.
        assert!(compute_phase.accepted);
        // State must change.
        assert_eq!(state.state, AccountState::Active(state_init));
        // Status must change to active.
        assert_eq!(state.end_status, AccountStatus::Active);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // Fees must be paid.
        let expected_gas_fee = Tokens::new(config.gas_prices.flat_gas_price as _);
        assert_eq!(state.total_fees, prev_total_fees + expected_gas_fee);
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(state.balance.tokens, prev_balance.tokens - expected_gas_fee);

        let ComputePhase::Executed(compute_phase) = compute_phase.compute_phase else {
            panic!("expected executed compute phase");
        };

        assert!(compute_phase.success);
        assert!(compute_phase.msg_state_used);
        assert!(compute_phase.account_activated);
        assert_eq!(compute_phase.gas_fees, expected_gas_fee);
        assert_eq!(compute_phase.gas_used, (10 + 16) + 5); // two 16bit opcodes + implicit ret
        assert_eq!(
            compute_phase.gas_limit,
            VarUint56::new(config.gas_prices.gas_limit)
        );
        assert_eq!(compute_phase.gas_credit, None);
        assert_eq!(compute_phase.exit_code, 0);
        assert_eq!(compute_phase.exit_arg, None);
        assert_eq!(compute_phase.vm_steps, 2); // accept, implicit ret

        Ok(())
    }

    #[test]
    fn ext_in_unfreeze_hash_mismatch() -> Result<()> {
        let state_init = simple_state(tvmasm!("ACCEPT"));

        let params = make_default_params();
        let config = make_default_config();
        let mut state =
            ExecutorState::new_frozen(&params, &config, &STUB_ADDR, OK_BALANCE, HashBytes::ZERO);

        let msg = state.receive_in_msg(make_message(
            ExtInMsgInfo {
                dst: STUB_ADDR.into(),
                ..Default::default()
            },
            Some(state_init.clone()),
            None,
        ))?;

        let prev_state = state.state.clone();
        let prev_balance = state.balance.clone();
        let prev_total_fees = state.total_fees;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(
            compute_phase.original_balance,
            CurrencyCollection::from(OK_BALANCE - prev_total_fees)
        );
        // Message must not be accepted.
        assert!(!compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(state.end_status, AccountStatus::Frozen);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // Fees must not be paid.
        assert_eq!(state.total_fees, prev_total_fees);
        assert_eq!(state.balance, prev_balance);

        let ComputePhase::Skipped(compute_phase) = compute_phase.compute_phase else {
            panic!("expected skipped compute phase");
        };
        assert_eq!(compute_phase.reason, ComputePhaseSkipReason::BadState);

        Ok(())
    }

    #[test]
    fn ext_in_deploy_hash_mismatch() -> Result<()> {
        let state_init = simple_state(tvmasm!("ACCEPT"));

        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE);

        let msg = state.receive_in_msg(make_message(
            ExtInMsgInfo {
                dst: STUB_ADDR.into(),
                ..Default::default()
            },
            Some(state_init.clone()),
            None,
        ))?;

        let prev_state = state.state.clone();
        let prev_balance = state.balance.clone();
        let prev_total_fees = state.total_fees;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(
            compute_phase.original_balance,
            CurrencyCollection::from(OK_BALANCE - prev_total_fees)
        );
        // Message must not be accepted.
        assert!(!compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(state.end_status, AccountStatus::Uninit);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // Fees must not be paid.
        assert_eq!(state.total_fees, prev_total_fees);
        assert_eq!(state.balance, prev_balance);

        let ComputePhase::Skipped(compute_phase) = compute_phase.compute_phase else {
            panic!("expected skipped compute phase");
        };
        assert_eq!(compute_phase.reason, ComputePhaseSkipReason::BadState);

        Ok(())
    }

    #[test]
    fn internal_unfreeze_hash_mismatch() -> Result<()> {
        let state_init = simple_state(tvmasm!("ACCEPT"));

        let params = make_default_params();
        let config = make_default_config();
        let mut state =
            ExecutorState::new_frozen(&params, &config, &STUB_ADDR, OK_BALANCE, HashBytes::ZERO);

        let msg = state.receive_in_msg(make_message(
            IntMsgInfo {
                src: STUB_ADDR.into(),
                dst: STUB_ADDR.into(),
                value: Tokens::new(1_000_000_000).into(),
                ..Default::default()
            },
            Some(state_init.clone()),
            None,
        ))?;

        state.credit_phase(&msg)?;

        let prev_state = state.state.clone();
        let prev_balance = state.balance.clone();
        let prev_total_fees = state.total_fees;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(
            compute_phase.original_balance,
            CurrencyCollection::from(OK_BALANCE - prev_total_fees)
        );
        // Message must not be accepted.
        assert!(!compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(state.end_status, AccountStatus::Frozen);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // Fees must not be paid.
        assert_eq!(state.total_fees, prev_total_fees);
        assert_eq!(state.balance, prev_balance);

        let ComputePhase::Skipped(compute_phase) = compute_phase.compute_phase else {
            panic!("expected skipped compute phase");
        };
        assert_eq!(compute_phase.reason, ComputePhaseSkipReason::BadState);

        Ok(())
    }

    #[test]
    fn internal_deploy_hash_mismatch() -> Result<()> {
        let state_init = simple_state(tvmasm!("ACCEPT"));

        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE);

        let msg = state.receive_in_msg(make_message(
            IntMsgInfo {
                src: STUB_ADDR.into(),
                dst: STUB_ADDR.into(),
                value: Tokens::new(1_000_000_000).into(),
                ..Default::default()
            },
            Some(state_init.clone()),
            None,
        ))?;

        state.credit_phase(&msg)?;

        let prev_state = state.state.clone();
        let prev_balance = state.balance.clone();
        let prev_total_fees = state.total_fees;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(
            compute_phase.original_balance,
            CurrencyCollection::from(OK_BALANCE - prev_total_fees)
        );
        // Message must not be accepted.
        assert!(!compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(state.end_status, AccountStatus::Uninit);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // Fees must not be paid.
        assert_eq!(state.total_fees, prev_total_fees);
        assert_eq!(state.balance, prev_balance);

        let ComputePhase::Skipped(compute_phase) = compute_phase.compute_phase else {
            panic!("expected skipped compute phase");
        };
        assert_eq!(compute_phase.reason, ComputePhaseSkipReason::BadState);

        Ok(())
    }

    #[test]
    fn tick_special() -> Result<()> {
        init_tracing();
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_active(
            &params,
            &config,
            &STUB_ADDR,
            OK_BALANCE,
            Cell::empty_cell(),
            tvmasm!("DROP THROWIF 42 ACCEPT"),
        );

        let prev_balance = state.balance.clone();
        let prev_state = state.state.clone();
        let prev_total_fees = state.total_fees;
        let prev_end_status = state.end_status;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::TickTock(TickTock::Tick),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(
            compute_phase.original_balance,
            CurrencyCollection::from(OK_BALANCE)
        );
        // Message must be accepted.
        assert!(compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(prev_end_status, state.end_status);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // Fees must be paid.
        let expected_gas_fee = Tokens::new(config.gas_prices.flat_gas_price as _);
        assert_eq!(state.total_fees, prev_total_fees + expected_gas_fee);
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(state.balance.tokens, prev_balance.tokens - expected_gas_fee);

        let ComputePhase::Executed(compute_phase) = compute_phase.compute_phase else {
            panic!("expected executed compute phase");
        };

        assert!(compute_phase.success);
        assert!(!compute_phase.msg_state_used);
        assert!(!compute_phase.account_activated);
        assert_eq!(compute_phase.gas_fees, expected_gas_fee);
        assert_eq!(compute_phase.gas_used, 75);
        assert_eq!(
            compute_phase.gas_limit,
            VarUint56::new(config.gas_prices.gas_limit)
        );
        assert_eq!(compute_phase.gas_credit, None);
        assert_eq!(compute_phase.exit_code, 0);
        assert_eq!(compute_phase.exit_arg, None);
        assert_eq!(compute_phase.vm_steps, 4);

        Ok(())
    }

    #[test]
    fn code_as_library() -> Result<()> {
        init_tracing();
        let mut params = make_default_params();
        let config = make_default_config();

        let code = Boc::decode(tvmasm!("DROP THROWIF 42 ACCEPT"))?;
        params.libraries.set(code.repr_hash(), LibDescr {
            lib: code.clone(),
            publishers: {
                let mut p = Dict::new();
                p.set(HashBytes::ZERO, ())?;
                p
            },
        })?;

        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE);
        state.state = AccountState::Active(StateInit {
            code: Some(make_lib_ref(code.as_ref())),
            ..Default::default()
        });
        state.orig_status = AccountStatus::Active;
        state.end_status = AccountStatus::Active;

        let prev_balance = state.balance.clone();
        let prev_state = state.state.clone();
        let prev_total_fees = state.total_fees;
        let prev_end_status = state.end_status;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::TickTock(TickTock::Tick),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(
            compute_phase.original_balance,
            CurrencyCollection::from(OK_BALANCE)
        );
        // Message must be accepted.
        assert!(compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(prev_end_status, state.end_status);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // Fees must be paid.
        let expected_gas_fee = Tokens::new(config.gas_prices.flat_gas_price as _);
        assert_eq!(state.total_fees, prev_total_fees + expected_gas_fee);
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(state.balance.tokens, prev_balance.tokens - expected_gas_fee);

        let ComputePhase::Executed(compute_phase) = compute_phase.compute_phase else {
            panic!("expected executed compute phase");
        };

        assert!(compute_phase.success);
        assert!(!compute_phase.msg_state_used);
        assert!(!compute_phase.account_activated);
        assert_eq!(compute_phase.gas_fees, expected_gas_fee);
        assert_eq!(compute_phase.gas_used, 285);
        assert_eq!(
            compute_phase.gas_limit,
            VarUint56::new(config.gas_prices.gas_limit)
        );
        assert_eq!(compute_phase.gas_credit, None);
        assert_eq!(compute_phase.exit_code, 0);
        assert_eq!(compute_phase.exit_arg, None);
        assert_eq!(compute_phase.vm_steps, 5);

        Ok(())
    }

    #[test]
    fn internal_use_libraries() -> Result<()> {
        init_tracing();
        let mut params = make_default_params();
        let config = make_default_config();

        let state_lib_code = Boc::decode(tvmasm!("THROWIF 42 INT 0"))?;
        let account_lib_code = Boc::decode(tvmasm!("THROWIF 43 INT -1"))?;
        let msg_lib_code = Boc::decode(tvmasm!("THROWIFNOT 44"))?;

        params.libraries.set(HashBytes::ZERO, LibDescr {
            lib: state_lib_code.clone(),
            publishers: {
                let mut p = Dict::new();
                p.set(HashBytes([0x00; 32]), ())?;
                p
            },
        })?;

        let msg_state_init = StateInit {
            libraries: {
                let mut p = Dict::new();
                p.set(HashBytes([0x22; 32]), SimpleLib {
                    public: false,
                    root: msg_lib_code,
                })?;
                p
            },
            ..Default::default()
        };
        let addr = StdAddr::new(0, *CellBuilder::build_from(&msg_state_init)?.repr_hash());

        let mut state = ExecutorState::new_uninit(&params, &config, &addr, OK_BALANCE);
        state.state = AccountState::Active(StateInit {
            code: Some(Boc::decode(tvmasm!(
                r#"
                ACCEPT
                PUSHCONT {
                    DUMPSTK
                    XLOAD
                    CTOS
                    BLESS
                    EXECUTE
                }
                // Execute state lib code
                OVER
                PUSHREF @{0000000000000000000000000000000000000000000000000000000000000000}
                PUSH s2
                EXECUTE
                // Execute account lib code
                PUSHREF @{1111111111111111111111111111111111111111111111111111111111111111}
                PUSH s2
                EXECUTE
                // Execute msg lib code
                PUSHREF @{2222222222222222222222222222222222222222222222222222222222222222}
                ROT
                EXECUTE
                "#
            ))?),
            libraries: {
                let mut p = Dict::new();
                p.set(HashBytes([0x11; 32]), SimpleLib {
                    public: false,
                    root: account_lib_code,
                })?;
                p
            },
            ..Default::default()
        });
        state.orig_status = AccountStatus::Active;
        state.end_status = AccountStatus::Active;

        let msg = state.receive_in_msg(make_message(
            IntMsgInfo {
                src: addr.clone().into(),
                dst: addr.clone().into(),
                value: Tokens::new(1_000_000_000).into(),
                ..Default::default()
            },
            Some(msg_state_init),
            None,
        ))?;

        state.credit_phase(&msg)?;

        let prev_balance = state.balance.clone();
        let prev_state = state.state.clone();
        let prev_total_fees = state.total_fees;
        let prev_end_status = state.end_status;

        let compute_phase = state.compute_phase(ComputePhaseContext {
            input: TransactionInput::Ordinary(&msg),
            storage_fee: Tokens::ZERO,
            force_accept: false,
            inspector: None,
        })?;

        // Original balance must be correct.
        assert_eq!(
            compute_phase.original_balance,
            CurrencyCollection::from(OK_BALANCE)
        );
        // Message must be accepted.
        assert!(compute_phase.accepted);
        // State must not change.
        assert_eq!(state.state, prev_state);
        // Status must not change.
        assert_eq!(prev_end_status, state.end_status);
        // No actions must be produced.
        assert_eq!(compute_phase.actions, Cell::empty_cell());
        // Fees must be paid.
        let expected_gas_fee = Tokens::new(1315000);
        assert_eq!(state.total_fees, prev_total_fees + expected_gas_fee);
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(state.balance.tokens, prev_balance.tokens - expected_gas_fee);

        let ComputePhase::Executed(compute_phase) = compute_phase.compute_phase else {
            panic!("expected executed compute phase");
        };

        assert!(compute_phase.success);
        assert!(!compute_phase.msg_state_used);
        assert!(!compute_phase.account_activated);
        assert_eq!(compute_phase.gas_fees, expected_gas_fee);
        assert_eq!(compute_phase.gas_used, 1315);
        assert_eq!(
            compute_phase.gas_limit,
            VarUint56::new(config.gas_prices.gas_limit)
        );
        assert_eq!(compute_phase.gas_credit, None);
        assert_eq!(compute_phase.exit_code, 0);
        assert_eq!(compute_phase.exit_arg, None);
        assert_eq!(compute_phase.vm_steps, 39);

        Ok(())
    }
}
