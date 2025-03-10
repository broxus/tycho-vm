use anyhow::Result;
use everscale_types::models::{CurrencyCollection, IntAddr, MsgInfo, StateInit};
use everscale_types::num::Tokens;
use everscale_types::prelude::*;

use crate::util::{ExtStorageStat, StorageStatLimits};
use crate::ExecutorState;

impl ExecutorState<'_> {
    /// "Pre" phase of ordinary transactions.
    ///
    /// - Validates the inbound message cell;
    /// - For internal messages updates an LT range;
    /// - For external messages charges a fwd fee
    ///   (updates [`self.balance`] and [`self.total_fees`]).
    ///
    /// Returns a parsed received message ([`ReceivedMessage`]).
    ///
    /// Fails if the message is invalid or can't be imported.
    ///
    /// [`self.balance`]: Self::balance
    /// [`self.total_fees`]: Self::total_fees
    pub fn receive_in_msg(&mut self, msg_root: Cell) -> Result<ReceivedMessage> {
        let is_masterchain = self.address.is_masterchain();

        let is_external;
        let bounce_enabled;
        let mut msg_balance_remaining;

        // Process message header.
        let mut slice = msg_root.as_slice_allow_exotic();
        match MsgInfo::load_from(&mut slice)? {
            // Handle internal message.
            MsgInfo::Int(info) => {
                self.check_message_dst(&info.dst)?;

                // Update flags.
                is_external = false;
                bounce_enabled = info.bounce;

                // Update message balance
                msg_balance_remaining = info.value;
                msg_balance_remaining.try_add_assign_tokens(info.ihr_fee)?;

                // Adjust LT range.
                if info.created_lt >= self.start_lt {
                    self.start_lt = info.created_lt + 1;
                    self.end_lt = self.start_lt + 1;
                }
            }
            // Handle external (in) message.
            MsgInfo::ExtIn(info) => {
                self.check_message_dst(&info.dst)?;

                // Update flags.
                is_external = true;
                bounce_enabled = false;

                // Compute forwarding fees.
                let Some(mut stats) =
                    ExtStorageStat::compute_for_slice(&slice, StorageStatLimits {
                        bit_count: self.config.size_limits.max_msg_bits,
                        cell_count: self.config.size_limits.max_msg_cells,
                    })
                else {
                    anyhow::bail!("inbound message limits exceeded");
                };

                stats.cell_count -= 1; // root cell is ignored.
                stats.bit_count -= slice.size_bits() as u64; // bits in the root cells are free.

                let fwd_fee = if self.is_special {
                    // Importing external messages on special accounts is free.
                    // NOTE: We still need to compute and check `ExtStorageStat`.
                    Tokens::ZERO
                } else {
                    self.config
                        .fwd_prices(is_masterchain)
                        .compute_fwd_fee(stats)
                };

                // Deduct fees.
                if self.balance.tokens < fwd_fee {
                    anyhow::bail!("cannot pay for importing an external message");
                }
                self.balance.tokens -= fwd_fee;
                self.total_fees.try_add_assign(fwd_fee)?;

                // External message cannot carry value.
                msg_balance_remaining = CurrencyCollection::ZERO;
            }
            // Reject all other message types.
            MsgInfo::ExtOut(_) => anyhow::bail!("unexpected incoming ExtOut message"),
        }

        // Process message state init.
        let init = if slice.load_bit()? {
            Some(if slice.load_bit()? {
                // State init as reference.
                let state_root = slice.load_reference()?;
                anyhow::ensure!(
                    !state_root.is_exotic(),
                    "state init must be an ordinary cell"
                );

                let mut slice = state_root.as_slice_allow_exotic();
                let parsed = StateInit::load_from(&mut slice)?;
                anyhow::ensure!(slice.is_empty(), "state init contains extra data");

                MsgStateInit {
                    hash: *state_root.repr_hash(),
                    parsed,
                }
            } else {
                // Inline state init.
                let mut state_init_cs = slice;

                // Read StateInit.
                let parsed = StateInit::load_from(&mut slice)?;
                // Rebuild it as cell to get hash.
                state_init_cs.skip_last(slice.size_bits(), slice.size_refs())?;
                let state_root = CellBuilder::build_from(state_init_cs)?;

                MsgStateInit {
                    hash: *state_root.repr_hash(),
                    parsed,
                }
            })
        } else {
            None
        };

        // Process message body.
        let body = if slice.load_bit()? {
            // Body as cell.
            let body_cell = slice.load_reference_cloned()?;
            anyhow::ensure!(slice.is_empty(), "message contains extra data");

            let body_range = CellSliceRange::full(body_cell.as_ref());
            (body_cell, body_range)
        } else {
            // Inline body.
            let body_range = slice.range();
            (msg_root.clone(), body_range)
        };

        // Done
        Ok(ReceivedMessage {
            root: msg_root,
            init,
            body,
            is_external,
            bounce_enabled,
            balance_remaining: msg_balance_remaining,
        })
    }

    fn check_message_dst(&self, dst: &IntAddr) -> Result<()> {
        match dst {
            IntAddr::Std(dst) => {
                anyhow::ensure!(dst.anycast.is_none(), "anycast is not supported");
                anyhow::ensure!(*dst == self.address, "message destination address mismatch");
                Ok(())
            }
            IntAddr::Var(_) => anyhow::bail!("`addr_var` is not supported"),
        }
    }
}

/// Parsed inbound message.
#[derive(Debug, Clone)]
pub struct ReceivedMessage {
    /// Message root cell.
    pub root: Cell,
    /// Parsed message [`StateInit`].
    pub init: Option<MsgStateInit>,
    /// Message body.
    pub body: CellSliceParts,

    /// Whether this message is an `ExtIn`.
    pub is_external: bool,
    /// Whether this message can be bounced back on error.
    pub bounce_enabled: bool,

    /// The remaining attached value of the received message.
    /// NOTE: Always zero for external messages.
    pub balance_remaining: CurrencyCollection,
}

/// Message state init.
#[derive(Debug, Clone)]
pub struct MsgStateInit {
    /// [`StateInit`] hash.
    pub hash: HashBytes,
    /// Parsed [`StateInit`].
    pub parsed: StateInit,
}

#[cfg(test)]
mod tests {

    use everscale_types::models::{ExtInMsgInfo, ExtOutMsgInfo, IntMsgInfo, StdAddr};
    use everscale_types::num::Tokens;

    use super::*;
    use crate::tests::{make_big_tree, make_default_config, make_default_params, make_message};

    const OK_BALANCE: Tokens = Tokens::new(10_000_000_000);
    const STUB_ADDR: StdAddr = StdAddr::new(0, HashBytes::ZERO);

    fn apply_cs((cell, range): &CellSliceParts) -> CellSlice<'_> {
        range.apply_allow_exotic(cell)
    }

    // === Positive ===

    #[test]
    fn receive_ext_in_works() {
        let params = make_default_params();
        let config = make_default_config();

        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE);
        let prev_start_lt = state.start_lt;
        let prev_end_lt = state.end_lt;
        let prev_balance = state.balance.clone();
        let prev_acc_state = state.state.clone();

        let msg_root = make_message(
            ExtInMsgInfo {
                dst: STUB_ADDR.into(),
                ..Default::default()
            },
            Some(StateInit::default()),
            None,
        );
        let msg = state.receive_in_msg(msg_root.clone()).unwrap();
        // Received message must be parsed correctly.
        assert!(msg.is_external);
        assert!(!msg.bounce_enabled);
        {
            let init = msg.init.unwrap();
            let target = StateInit::default();
            assert_eq!(init.parsed, target);
            let target_hash = *CellBuilder::build_from(&target).unwrap().repr_hash();
            assert_eq!(init.hash, target_hash);
        }
        assert!(msg.body.1.is_empty());
        assert_eq!(msg.balance_remaining, CurrencyCollection::ZERO);

        // LT must not change.
        assert_eq!(state.start_lt, prev_start_lt);
        assert_eq!(state.end_lt, prev_end_lt);
        // This simple external message has no child cells,
        // so it consumes only the fixed amount for fwd_fee.
        assert_eq!(
            state.total_fees,
            Tokens::new(config.fwd_prices.lump_price as _)
        );
        // Extra currencies must not change.
        assert_eq!(state.balance.other, prev_balance.other);
        // Forward fee must be withdrawn from the account balance.
        assert_eq!(state.balance.tokens, prev_balance.tokens - state.total_fees);
        // Account state must not change.
        assert_eq!(state.state, prev_acc_state);
    }

    #[test]
    fn receive_int_to_non_existent() {
        let params = make_default_params();
        let config = make_default_config();

        let mut state = ExecutorState::new_non_existent(&params, &config, &STUB_ADDR);
        let prev_start_lt = state.start_lt;
        assert_eq!(prev_start_lt, 0);
        let prev_balance = state.balance.clone();
        let prev_acc_state = state.state.clone();

        let msg_lt = 1000;
        let msg_root = make_message(
            IntMsgInfo {
                dst: STUB_ADDR.into(),
                value: OK_BALANCE.into(),
                bounce: true,
                created_lt: msg_lt,
                ..Default::default()
            },
            None,
            Some({
                let mut b = CellBuilder::new();
                b.store_u32(0xdeafbeaf).unwrap();
                b
            }),
        );
        let msg = state.receive_in_msg(msg_root.clone()).unwrap();
        // Received message must be parsed correctly.
        assert!(!msg.is_external);
        assert!(msg.bounce_enabled);
        assert!(msg.init.is_none());
        assert_eq!(apply_cs(&msg.body).load_u32().unwrap(), 0xdeafbeaf);
        assert_eq!(msg.balance_remaining, OK_BALANCE.into());

        // LT must change to the message LT.
        assert_eq!(state.start_lt, msg_lt + 1);
        assert_eq!(state.end_lt, state.start_lt + 1);
        // Internal message dous not require any fwd_fee on receive.
        assert_eq!(state.total_fees, Tokens::ZERO);
        // Balance must not change (it will change on a credit phase).
        assert_eq!(state.balance, prev_balance);
        // Account state must not change.
        assert_eq!(state.state, prev_acc_state);
    }

    // === Negative ===

    #[test]
    fn receive_ext_out() {
        let params = make_default_params();
        let config = make_default_config();

        ExecutorState::new_non_existent(&params, &config, &STUB_ADDR)
            .receive_in_msg(make_message(
                ExtOutMsgInfo {
                    dst: None,
                    src: STUB_ADDR.into(),
                    created_at: 1,
                    created_lt: 1,
                },
                None,
                None,
            ))
            .inspect_err(|e| println!("{e}"))
            .unwrap_err();
    }

    #[test]
    fn receive_ext_in_on_non_existent() {
        let params = make_default_params();
        let config = make_default_config();

        ExecutorState::new_non_existent(&params, &config, &STUB_ADDR)
            .receive_in_msg(make_message(
                ExtInMsgInfo {
                    dst: STUB_ADDR.into(),
                    ..Default::default()
                },
                None,
                None,
            ))
            .inspect_err(|e| println!("{e}"))
            .unwrap_err();
    }

    #[test]
    fn receive_ext_in_not_enough_balance() {
        let params = make_default_params();
        let config = make_default_config();

        ExecutorState::new_uninit(&params, &config, &STUB_ADDR, Tokens::new(1))
            .receive_in_msg(make_message(
                ExtInMsgInfo {
                    dst: STUB_ADDR.into(),
                    ..Default::default()
                },
                None,
                None,
            ))
            .inspect_err(|e| println!("{e}"))
            .unwrap_err();
    }

    #[test]
    fn receive_internal_balance_overflow() {
        let params = make_default_params();
        let config = make_default_config();

        ExecutorState::new_uninit(&params, &config, &STUB_ADDR, Tokens::MAX)
            .receive_in_msg(make_message(
                IntMsgInfo {
                    dst: STUB_ADDR.into(),
                    value: Tokens::MAX.into(),
                    ihr_fee: Tokens::MAX,
                    ..Default::default()
                },
                None,
                None,
            ))
            .inspect_err(|e| println!("{e}"))
            .unwrap_err();
    }

    #[test]
    fn receive_with_invalid_dst() {
        let params = make_default_params();
        let config = make_default_config();

        let other_addr = StdAddr::new(0, HashBytes([1; 32]));

        // External
        ExecutorState::new_non_existent(&params, &config, &STUB_ADDR)
            .receive_in_msg(make_message(
                ExtInMsgInfo {
                    dst: other_addr.clone().into(),
                    ..Default::default()
                },
                None,
                None,
            ))
            .inspect_err(|e| println!("{e}"))
            .unwrap_err();

        // Internal
        ExecutorState::new_non_existent(&params, &config, &STUB_ADDR)
            .receive_in_msg(make_message(
                IntMsgInfo {
                    dst: other_addr.clone().into(),
                    ..Default::default()
                },
                None,
                None,
            ))
            .inspect_err(|e| println!("{e}"))
            .unwrap_err();
    }

    #[test]
    fn invalid_message_structure() -> anyhow::Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let cx = Cell::empty_context();

        let run_on_uninit = |msg| {
            ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE)
                .receive_in_msg(msg)
                .inspect_err(|e| println!("{e}"))
                .unwrap_err();
        };

        // Invalid msg info
        run_on_uninit(CellBuilder::build_from(0xdeafbeafu32)?);

        // Invalid state init.
        run_on_uninit({
            let mut b = CellBuilder::new();
            // MsgInfo
            MsgInfo::Int(IntMsgInfo {
                dst: STUB_ADDR.into(),
                ..Default::default()
            })
            .store_into(&mut b, cx)?;

            // just$1 (right$1 ^StateInit)
            b.store_bit_one()?;
            b.store_bit_one()?;
            b.store_reference(CellBuilder::build_from(0xdeafbeafu32)?)?;

            // left$0 X
            b.store_bit_zero()?;

            //
            b.build()?
        });

        // State init with extra data.
        run_on_uninit({
            let mut b = CellBuilder::new();
            // MsgInfo
            MsgInfo::Int(IntMsgInfo {
                dst: STUB_ADDR.into(),
                ..Default::default()
            })
            .store_into(&mut b, cx)?;

            // just$1 (right$1 ^StateInit)
            b.store_bit_one()?;
            b.store_bit_one()?;
            b.store_reference({
                let mut b = CellBuilder::new();
                StateInit::default().store_into(&mut b, cx)?;
                b.store_u32(0xdeafbeaf)?;
                b.build()?
            })?;

            // left$0 X
            b.store_bit_zero()?;

            //
            b.build()?
        });

        // Body with extra data.
        run_on_uninit({
            let mut b = CellBuilder::new();
            // MsgInfo
            MsgInfo::Int(IntMsgInfo {
                dst: STUB_ADDR.into(),
                ..Default::default()
            })
            .store_into(&mut b, cx)?;

            // nont$0
            b.store_bit_zero()?;

            // left$1 ^X
            b.store_bit_one()?;
            b.store_reference(Cell::empty_cell())?;
            b.store_u32(0xdeafbeaf)?;

            //
            b.build()?
        });

        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn msg_out_of_limits() {
        let params = make_default_params();
        let config = make_default_config();

        let body = make_big_tree(8, &mut 0, config.size_limits.max_msg_cells as u16 + 10);

        ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE)
            .receive_in_msg(make_message(
                ExtInMsgInfo {
                    dst: STUB_ADDR.into(),
                    ..Default::default()
                },
                None,
                Some({
                    let mut b = CellBuilder::new();
                    b.store_slice(body.as_slice_allow_exotic()).unwrap();
                    b
                }),
            ))
            .inspect_err(|e| println!("{e}"))
            .unwrap_err();
    }
}
