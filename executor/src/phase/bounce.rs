use anyhow::Result;
use tycho_types::cell::{Cell, CellBuilder, CellFamily, Lazy, Store};
use tycho_types::models::{
    BouncePhase, ExecutedBouncePhase, MsgInfo, NoFundsBouncePhase, StorageUsedShort,
};
use tycho_types::num::Tokens;

use crate::ExecutorState;
use crate::phase::receive::ReceivedMessage;
use crate::util::{
    ExtStorageStat, StorageStatLimits, check_rewrite_dst_addr, new_varuint56_truncate,
};

/// Bounce phase input context.
pub struct BouncePhaseContext<'a> {
    /// Gas fees from the compute phase (if any).
    pub gas_fees: Tokens,
    /// Action fine from the action phase (if any).
    pub action_fine: Tokens,
    /// Received message (internal only).
    pub received_message: &'a ReceivedMessage,
}

impl ExecutorState<'_> {
    /// Bounce phase of ordinary transactions.
    ///
    /// - Tries to send an inbound message back to the sender;
    /// - Defined only for internal inbound messages;
    /// - Remaining message balance is substracted from the account balance;
    /// - Fees are paid using the remaining inbound message balance;
    ///
    /// Returns an executed [`BouncePhase`].
    ///
    /// Fails if the origin workchain of the message doesn't exist or
    /// disabled. Can also fail on [`total_fees`] overflow, but this should
    /// not happen on networks with valid value flow.
    ///
    /// [`total_fees`]: Self::total_fees
    pub fn bounce_phase(&mut self, ctx: BouncePhaseContext<'_>) -> Result<BouncePhase> {
        let mut info = ctx.received_message.root.parse::<MsgInfo>()?;
        let MsgInfo::Int(int_msg_info) = &mut info else {
            anyhow::bail!("bounce phase is defined only for internal messages");
        };

        // Reverse message direction.
        std::mem::swap(&mut int_msg_info.src, &mut int_msg_info.dst);
        if !check_rewrite_dst_addr(&self.config.workchains, &mut int_msg_info.dst) {
            // FIXME: Just ignore this phase in that case? What if we disable
            // the message origin workchain and this message bounces? However,
            // for that we should at least have other workchains .
            anyhow::bail!("invalid destination address in a bounced message");
        }

        // Compute additional full body cell.
        let full_body = if self.params.full_body_in_bounced {
            let (range, cell) = &ctx.received_message.body;
            Some(if range.is_full(cell) {
                cell.clone()
            } else {
                CellBuilder::build_from(range.apply_allow_exotic(cell))?
            })
        } else {
            None
        };

        // Overwrite msg balance.
        let mut msg_value = ctx.received_message.balance_remaining.clone();

        // Authority marks cannot be bounced back.
        if self.params.authority_marks_enabled
            && let Some(marks) = &self.config.authority_marks
        {
            marks.remove_authority_marks_in(&mut msg_value)?;
        }

        // Compute message storage stats.
        let stats = 'stats: {
            let mut stats = ExtStorageStat::with_limits(StorageStatLimits {
                bit_count: self.config.size_limits.max_msg_bits,
                cell_count: self.config.size_limits.max_msg_cells,
            });

            // Root cell is free, but all children must be accounted.
            'valid: {
                // Msg value can contain some cells.
                if let Some(extra_currencies) = msg_value.other.as_dict().root()
                    && !stats.add_cell(extra_currencies.as_ref())
                {
                    break 'valid;
                }

                // We must also include a msg body if `params.full_body_in_bounce` is enabled.
                if let Some(body) = &full_body
                    && !stats.add_cell(body.as_ref())
                {
                    break 'valid;
                }

                // Exit this block with a valid storage stats info.
                break 'stats stats.stats();
            }

            // Fallback to NoFunds if the returned message cannot fit into the limits.
            // We require an "infinite" amount of tokens here if storage overflows.
            let stats = stats.stats();
            return Ok(BouncePhase::NoFunds(NoFundsBouncePhase {
                msg_size: StorageUsedShort {
                    bits: new_varuint56_truncate(stats.bit_count),
                    cells: new_varuint56_truncate(stats.cell_count),
                },
                req_fwd_fees: Tokens::MAX,
            }));
        };

        // Compute forwarding fee.
        let use_mc_prices = self.address.is_masterchain() || int_msg_info.dst.is_masterchain();
        let prices = self.config.fwd_prices(use_mc_prices);

        let mut fwd_fees = prices.compute_fwd_fee(stats);
        let msg_size = StorageUsedShort {
            cells: new_varuint56_truncate(stats.cell_count),
            bits: new_varuint56_truncate(stats.bit_count),
        };

        // Try to substract all fees from the remaining message balance.
        msg_value.tokens = match msg_value
            .tokens
            .checked_sub(ctx.gas_fees)
            .and_then(|t| t.checked_sub(ctx.action_fine))
        {
            Some(msg_balance) if msg_balance >= fwd_fees => msg_balance,
            msg_balance => {
                return Ok(BouncePhase::NoFunds(NoFundsBouncePhase {
                    msg_size,
                    req_fwd_fees: fwd_fees - msg_balance.unwrap_or_default(),
                }));
            }
        };

        // Take message balance back from the account balance.
        self.balance.try_sub_assign(&msg_value)?;

        // Take forwarding fee from the message balance.
        msg_value.tokens -= fwd_fees;

        // Split forwarding fee.
        let msg_fees = prices.get_first_part(fwd_fees);
        fwd_fees -= msg_fees;
        self.total_fees.try_add_assign(msg_fees)?;

        // Finalize message.
        int_msg_info.ihr_disabled = true;
        int_msg_info.bounce = false;
        int_msg_info.bounced = true;
        int_msg_info.value = msg_value;
        int_msg_info.ihr_fee = Tokens::ZERO;
        int_msg_info.fwd_fee = fwd_fees;
        int_msg_info.created_lt = self.end_lt;
        int_msg_info.created_at = self.params.block_unixtime;

        let msg = {
            const ROOT_BODY_BITS: u16 = 256;
            const BOUNCE_SELECTOR: u32 = u32::MAX;

            let body_prefix = {
                let (range, cell) = &ctx.received_message.body;
                range.apply_allow_exotic(cell).get_prefix(ROOT_BODY_BITS, 0)
            };

            let c = Cell::empty_context();
            let mut b = CellBuilder::new();
            info.store_into(&mut b, c)?;
            b.store_bit_zero()?; // init:(Maybe ...) -> nothing$0

            if b.has_capacity(body_prefix.size_bits() + 33, 0) {
                b.store_bit_zero()?; // body:(Either X ^X) -> left$0 X
                b.store_u32(BOUNCE_SELECTOR)?;
                b.store_slice_data(body_prefix)?;
                if let Some(full_body) = full_body {
                    b.store_reference(full_body)?;
                }
            } else {
                let child = {
                    let mut b = CellBuilder::new();
                    b.store_u32(BOUNCE_SELECTOR)?;
                    b.store_slice_data(body_prefix)?;
                    if let Some(full_body) = full_body {
                        b.store_reference(full_body)?;
                    }
                    b.build()?
                };

                b.store_bit_one()?; // body:(Either X ^X) -> right$1 ^X
                b.store_reference(child)?
            }

            // SAFETY: `b` is an ordinary cell.
            unsafe { Lazy::from_raw_unchecked(b.build()?) }
        };

        // Add message to output.
        self.out_msgs.push(msg);
        self.end_lt += 1;

        // Done
        Ok(BouncePhase::Executed(ExecutedBouncePhase {
            msg_size,
            msg_fees,
            fwd_fees,
        }))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use tycho_types::models::{AuthorityMarksConfig, CurrencyCollection, IntMsgInfo, StdAddr};
    use tycho_types::num::VarUint248;
    use tycho_types::prelude::*;

    use super::*;
    use crate::ExecutorParams;
    use crate::tests::{
        make_custom_config, make_default_config, make_default_params, make_message,
    };

    #[test]
    fn bounce_with_enough_funds() {
        let mut params = make_default_params();
        params.full_body_in_bounced = false;

        let config = make_default_config();

        let src_addr = StdAddr::new(0, HashBytes([0; 32]));
        let dst_addr = StdAddr::new(0, HashBytes([1; 32]));

        let gas_fees = Tokens::new(100);
        let action_fine = Tokens::new(200);

        let mut state =
            ExecutorState::new_uninit(&params, &config, &dst_addr, Tokens::new(1_000_000_000));
        state.balance.tokens -= gas_fees;
        state.balance.tokens -= action_fine;
        let prev_balance = state.balance.clone();
        let prev_total_fees = state.total_fees;
        let prev_start_lt = state.start_lt;

        let received_msg = state
            .receive_in_msg(make_message(
                IntMsgInfo {
                    src: src_addr.clone().into(),
                    dst: dst_addr.clone().into(),
                    value: Tokens::new(1_000_000_000).into(),
                    bounce: true,
                    created_lt: prev_start_lt + 1000,
                    ..Default::default()
                },
                None,
                None,
            ))
            .unwrap();
        assert_eq!(state.start_lt, prev_start_lt + 1000 + 1);
        assert_eq!(state.end_lt, prev_start_lt + 1000 + 2);

        let bounce_phase = state
            .bounce_phase(BouncePhaseContext {
                gas_fees,
                action_fine,
                received_message: &received_msg,
            })
            .unwrap();

        let BouncePhase::Executed(bounce_phase) = bounce_phase else {
            panic!("expected bounce phase to execute")
        };

        // Only msg fees are collected during the transaction.
        let full_fwd_fee = Tokens::new(config.fwd_prices.lump_price as _);
        let collected_fees = config.fwd_prices.get_first_part(full_fwd_fee);
        assert_eq!(state.total_fees, prev_total_fees + collected_fees);
        assert_eq!(state.total_fees, prev_total_fees + bounce_phase.msg_fees);
        assert_eq!(bounce_phase.fwd_fees, full_fwd_fee - collected_fees);

        // There were no extra currencies in the inbound message.
        assert_eq!(state.out_msgs.len(), 1);
        let bounced_msg = state.out_msgs.last().unwrap().load().unwrap();
        assert!(bounced_msg.init.is_none());
        assert_eq!(bounced_msg.body.0.size_bits(), 32);
        assert_eq!(
            CellSlice::apply(&bounced_msg.body)
                .unwrap()
                .load_u32()
                .unwrap(),
            u32::MAX
        );

        let MsgInfo::Int(bounced_msg_info) = bounced_msg.info else {
            panic!("expected bounced internal message");
        };
        assert_eq!(state.balance.other, prev_balance.other);
        assert!(bounced_msg_info.value.other.is_empty());
        assert_eq!(
            state.balance.tokens,
            prev_balance.tokens - (received_msg.balance_remaining.tokens - gas_fees - action_fine)
        );
        assert_eq!(
            bounced_msg_info.value.tokens,
            received_msg.balance_remaining.tokens - gas_fees - action_fine - full_fwd_fee
        );
        assert!(bounced_msg_info.ihr_disabled);
        assert!(!bounced_msg_info.bounce);
        assert!(bounced_msg_info.bounced);
        assert_eq!(bounced_msg_info.src, dst_addr.clone().into());
        assert_eq!(bounced_msg_info.dst, src_addr.clone().into());
        assert_eq!(bounced_msg_info.ihr_fee, Tokens::ZERO);
        assert_eq!(bounced_msg_info.fwd_fee, bounce_phase.fwd_fees);
        assert_eq!(bounced_msg_info.created_at, params.block_unixtime);
        assert_eq!(bounced_msg_info.created_lt, prev_start_lt + 1000 + 2);

        // Root cell is free and the bounced message has no child cells.
        assert_eq!(bounce_phase.msg_size, StorageUsedShort {
            bits: Default::default(),
            cells: Default::default()
        });

        // End LT must increase.
        assert_eq!(state.end_lt, prev_start_lt + 1000 + 3);
    }

    #[test]
    fn bounce_does_not_return_marks() {
        let params = ExecutorParams {
            authority_marks_enabled: true,
            ..make_default_params()
        };
        let config = make_custom_config(|config| {
            config.set_authority_marks_config(&AuthorityMarksConfig {
                authority_addresses: BTreeMap::from_iter([(HashBytes::ZERO, ())]).try_into()?,
                black_mark_id: 100,
                white_mark_id: 101,
            })?;
            Ok(())
        });

        let src_addr = StdAddr::new(0, HashBytes([123; 32]));
        let dst_addr = StdAddr::new(-1, HashBytes::ZERO);

        let gas_fees = Tokens::new(100);
        let action_fine = Tokens::new(200);

        let mut state =
            ExecutorState::new_uninit(&params, &config, &dst_addr, CurrencyCollection {
                tokens: Tokens::new(1_000_000_000),
                other: BTreeMap::from_iter([
                    (100u32, VarUint248::new(1000)), // more black barks than white
                    (101u32, VarUint248::new(100)),
                ])
                .try_into()
                .unwrap(),
            });
        state.balance.tokens -= gas_fees;
        state.balance.tokens -= action_fine;
        let prev_balance = state.balance.clone();
        let prev_total_fees = state.total_fees;
        let prev_start_lt = state.start_lt;

        let msg_balance = CurrencyCollection {
            tokens: Tokens::new(1_000_000_000),
            other: BTreeMap::from_iter([(100u32, VarUint248::new(1))])
                .try_into()
                .unwrap(),
        };
        let received_msg = state
            .receive_in_msg(make_message(
                IntMsgInfo {
                    src: src_addr.clone().into(),
                    dst: dst_addr.clone().into(),
                    value: msg_balance.clone(),
                    bounce: true,
                    created_lt: prev_start_lt + 1000,
                    ..Default::default()
                },
                None,
                None,
            ))
            .unwrap();
        assert_eq!(state.start_lt, prev_start_lt + 1000 + 1);
        assert_eq!(state.end_lt, prev_start_lt + 1000 + 2);

        let credit_phase = state.credit_phase(&received_msg).unwrap();
        assert_eq!(credit_phase.credit, msg_balance);

        let bounce_phase = state
            .bounce_phase(BouncePhaseContext {
                gas_fees,
                action_fine,
                received_message: &received_msg,
            })
            .unwrap();

        let BouncePhase::Executed(bounce_phase) = bounce_phase else {
            panic!("expected bounce phase to execute")
        };

        // Only msg fees are collected during the transaction.
        let full_fwd_fee = Tokens::new(config.mc_fwd_prices.lump_price as _);
        let collected_fees = config.mc_fwd_prices.get_first_part(full_fwd_fee);
        assert_eq!(state.total_fees, prev_total_fees + collected_fees);
        assert_eq!(state.total_fees, prev_total_fees + bounce_phase.msg_fees);
        assert_eq!(bounce_phase.fwd_fees, full_fwd_fee - collected_fees);

        // There were no extra currencies in the inbound message.
        assert_eq!(state.out_msgs.len(), 1);
        let bounced_msg = state.out_msgs.last().unwrap().load().unwrap();
        assert!(bounced_msg.init.is_none());
        assert_eq!(bounced_msg.body.0.size_bits(), 32);
        assert_eq!(
            CellSlice::apply(&bounced_msg.body)
                .unwrap()
                .load_u32()
                .unwrap(),
            u32::MAX
        );

        let MsgInfo::Int(bounced_msg_info) = bounced_msg.info else {
            panic!("expected bounced internal message");
        };
        assert_eq!(
            state.balance.other,
            prev_balance.other.checked_add(&msg_balance.other).unwrap()
        );
        assert!(bounced_msg_info.value.other.is_empty());
        assert_eq!(
            state.balance.tokens,
            prev_balance.tokens + gas_fees + action_fine
        );
        assert_eq!(
            bounced_msg_info.value.tokens,
            received_msg.balance_remaining.tokens - gas_fees - action_fine - full_fwd_fee
        );
        assert!(bounced_msg_info.ihr_disabled);
        assert!(!bounced_msg_info.bounce);
        assert!(bounced_msg_info.bounced);
        assert_eq!(bounced_msg_info.src, dst_addr.clone().into());
        assert_eq!(bounced_msg_info.dst, src_addr.clone().into());
        assert_eq!(bounced_msg_info.ihr_fee, Tokens::ZERO);
        assert_eq!(bounced_msg_info.fwd_fee, bounce_phase.fwd_fees);
        assert_eq!(bounced_msg_info.created_at, params.block_unixtime);
        assert_eq!(bounced_msg_info.created_lt, prev_start_lt + 1000 + 2);

        // Root cell is free and the bounced message has no child cells.
        assert_eq!(bounce_phase.msg_size, StorageUsedShort {
            bits: Default::default(),
            cells: Default::default()
        });

        // End LT must increase.
        assert_eq!(state.end_lt, prev_start_lt + 1000 + 3);
    }

    #[test]
    fn bounce_with_no_funds() {
        let mut params = make_default_params();
        params.full_body_in_bounced = false;

        let config = make_default_config();

        let src_addr = StdAddr::new(0, HashBytes([0; 32]));
        let dst_addr = StdAddr::new(0, HashBytes([1; 32]));

        let mut state =
            ExecutorState::new_uninit(&params, &config, &dst_addr, Tokens::new(1_000_000_001));
        let prev_balance = state.balance.clone();
        let prev_total_fees = state.total_fees;
        let prev_start_lt = state.start_lt;

        let received_msg = state
            .receive_in_msg(make_message(
                IntMsgInfo {
                    src: src_addr.clone().into(),
                    dst: dst_addr.clone().into(),
                    value: Tokens::new(1).into(),
                    bounce: true,
                    created_lt: prev_start_lt + 1000,
                    ..Default::default()
                },
                None,
                None,
            ))
            .unwrap();
        assert_eq!(state.start_lt, prev_start_lt + 1000 + 1);
        assert_eq!(state.end_lt, prev_start_lt + 1000 + 2);

        let bounce_phase = state
            .bounce_phase(BouncePhaseContext {
                gas_fees: Tokens::ZERO,
                action_fine: Tokens::ZERO,
                received_message: &received_msg,
            })
            .unwrap();

        let BouncePhase::NoFunds(bounce_phase) = bounce_phase else {
            panic!("expected bounce phase to execute")
        };

        // Balance must not change.
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(state.balance.tokens, prev_balance.tokens);
        assert_eq!(state.total_fees, prev_total_fees);

        // Required fees must be computed correctly.
        let full_fwd_fee = Tokens::new(config.fwd_prices.lump_price as _);
        assert_eq!(
            bounce_phase.req_fwd_fees,
            full_fwd_fee - received_msg.balance_remaining.tokens
        );

        // Root cell is free and the bounced message has no child cells.
        assert_eq!(bounce_phase.msg_size, StorageUsedShort {
            bits: Default::default(),
            cells: Default::default()
        });

        // No messages must be produced.
        assert_eq!(state.out_msgs.len(), 0);

        // End LT must not change.
        assert_eq!(state.end_lt, prev_start_lt + 1000 + 2);
    }
}
