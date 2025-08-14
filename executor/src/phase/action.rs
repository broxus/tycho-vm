use anyhow::Result;
use sha2::{Digest, Sha256};
use tycho_types::cell::{CellTreeStats, Lazy};
use tycho_types::error::Error;
use tycho_types::models::{
    AccountState, AccountStatus, AccountStatusChange, ActionPhase, ChangeLibraryMode,
    CurrencyCollection, ExecutedComputePhase, ExtraCurrencyCollection, LibRef, OutAction,
    OwnedMessage, OwnedRelaxedMessage, RelaxedMsgInfo, ReserveCurrencyFlags, SendMsgFlags,
    SimpleLib, StateInit, StorageUsedShort,
};
use tycho_types::num::{Tokens, VarUint56};
use tycho_types::prelude::*;

use crate::phase::receive::ReceivedMessage;
use crate::util::{
    check_rewrite_dst_addr, check_rewrite_src_addr, check_state_limits, check_state_limits_diff,
    ExtStorageStat, StateLimitsResult, StorageStatLimits,
};
use crate::{ExecutorInspector, ExecutorState, PublicLibraryChange};

/// Action phase input context.
pub struct ActionPhaseContext<'a, 'e> {
    /// Received message (external or internal).
    pub received_message: Option<&'a mut ReceivedMessage>,
    /// Original account balance before the compute phase.
    pub original_balance: CurrencyCollection,
    /// New account state to apply.
    pub new_state: StateInit,
    /// Actions list.
    pub actions: Cell,
    /// Successfully executed compute phase.
    pub compute_phase: &'a ExecutedComputePhase,
    /// Executor inspector.
    pub inspector: Option<&'a mut ExecutorInspector<'e>>,
}

/// Executed action phase with additional info.
#[derive(Debug)]
pub struct ActionPhaseFull {
    /// Resulting action phase.
    pub action_phase: ActionPhase,
    /// Additional fee in case of failure.
    pub action_fine: Tokens,
    /// Whether state can't be updated due to limits.
    pub state_exceeds_limits: bool,
    /// Whether bounce phase is required.
    pub bounce: bool,
}

impl ExecutorState<'_> {
    pub fn action_phase(&mut self, mut ctx: ActionPhaseContext<'_, '_>) -> Result<ActionPhaseFull> {
        const MAX_ACTIONS: u16 = 255;

        let mut res = ActionPhaseFull {
            action_phase: ActionPhase {
                success: false,
                valid: false,
                no_funds: false,
                status_change: AccountStatusChange::Unchanged,
                total_fwd_fees: None,
                total_action_fees: None,
                result_code: -1,
                result_arg: None,
                total_actions: 0,
                special_actions: 0,
                skipped_actions: 0,
                messages_created: 0,
                action_list_hash: *ctx.actions.repr_hash(),
                total_message_size: StorageUsedShort::ZERO,
            },
            action_fine: Tokens::ZERO,
            state_exceeds_limits: false,
            bounce: false,
        };

        // Unpack actions list.
        let mut action_idx = 0u16;

        let mut list = Vec::new();
        let mut actions = ctx.actions.as_ref();
        loop {
            if actions.is_exotic() {
                // Actions list item must be an ordinary cell.
                res.action_phase.result_code = ResultCode::ActionListInvalid as i32;
                res.action_phase.result_arg = Some(action_idx as _);
                res.action_phase.valid = false;
                return Ok(res);
            }

            // NOTE: We have checked that this cell is an ordinary.
            let mut cs = actions.as_slice_allow_exotic();
            if cs.is_empty() {
                // Actions list terminates with an empty cell.
                break;
            }

            list.push(actions);

            actions = match cs.load_reference() {
                Ok(child) => child,
                Err(_) => {
                    // Each action must contain at least one reference.
                    res.action_phase.result_code = ResultCode::ActionListInvalid as i32;
                    res.action_phase.result_arg = Some(action_idx as _);
                    res.action_phase.valid = false;
                    return Ok(res);
                }
            };

            action_idx += 1;
            if action_idx > MAX_ACTIONS {
                // There can be at most N actions.
                res.action_phase.result_code = ResultCode::TooManyActions as i32;
                res.action_phase.result_arg = Some(action_idx as _);
                res.action_phase.valid = false;
                return Ok(res);
            }
        }

        res.action_phase.total_actions = action_idx;

        // Parse actions.
        let mut parsed_list = Vec::with_capacity(list.len());
        for (action_idx, item) in list.into_iter().rev().enumerate() {
            let mut cs = item.as_slice_allow_exotic();
            cs.load_reference().ok(); // Skip first reference.

            // Try to parse one action.
            let mut cs_parsed = cs;
            if let Ok(item) = OutAction::load_from(&mut cs_parsed) {
                if cs_parsed.is_empty() {
                    // Add this action if slices contained it exclusively.
                    parsed_list.push(Some(item));
                    continue;
                }
            }

            // Special brhaviour for `SendMsg` action when we can at least parse its flags.
            if cs.size_bits() >= 40 && cs.load_u32()? == OutAction::TAG_SEND_MSG {
                let mode = SendMsgFlags::from_bits_retain(cs.load_u8()?);
                if mode.contains(SendMsgFlags::IGNORE_ERROR) {
                    // "IGNORE_ERROR" flag means that we can just skip this action.
                    res.action_phase.skipped_actions += 1;
                    parsed_list.push(None);
                    continue;
                } else if mode.contains(SendMsgFlags::BOUNCE_ON_ERROR) {
                    // "BOUNCE_ON_ERROR" flag means that we fail the action phase,
                    // but require a bounce phase to run afterwards.
                    res.bounce = true;
                }
            }

            res.action_phase.result_code = ResultCode::ActionInvalid as i32;
            res.action_phase.result_arg = Some(action_idx as _);
            res.action_phase.valid = false;
            return Ok(res);
        }

        // Action list itself is ok.
        res.action_phase.valid = true;

        // Execute actions.
        let mut action_ctx = ActionContext {
            need_bounce_on_fail: false,
            strict_extra_currency: self.params.strict_extra_currency,
            received_message: ctx.received_message,
            original_balance: &ctx.original_balance,
            remaining_balance: self.balance.clone(),
            reserved_balance: CurrencyCollection::ZERO,
            action_fine: &mut res.action_fine,
            new_state: &mut ctx.new_state,
            end_lt: self.end_lt,
            out_msgs: Vec::new(),
            delete_account: false,
            public_libs_diff: ctx.inspector.is_some().then(Vec::new),
            compute_phase: ctx.compute_phase,
            action_phase: &mut res.action_phase,
        };

        for (action_idx, action) in parsed_list.into_iter().enumerate() {
            let Some(action) = action else {
                continue;
            };

            action_ctx.need_bounce_on_fail = false;
            action_ctx.action_phase.result_code = -1;
            action_ctx.action_phase.result_arg = Some(action_idx as _);

            let action = match action {
                OutAction::SendMsg { mode, out_msg } => {
                    let mut rewrite = None;
                    loop {
                        match self.do_send_message(mode, &out_msg, &mut action_ctx, rewrite) {
                            Ok(SendMsgResult::Sent) => break Ok(()),
                            Ok(SendMsgResult::Rewrite(r)) => rewrite = Some(r),
                            Err(e) => break Err(e),
                        }
                    }
                }
                OutAction::SetCode { new_code } => self.do_set_code(new_code, &mut action_ctx),
                OutAction::ReserveCurrency { mode, value } => {
                    self.do_reserve_currency(mode, value, &mut action_ctx)
                }
                OutAction::ChangeLibrary { mode, lib } => {
                    self.do_change_library(mode, lib, &mut action_ctx)
                }
            };

            if let Err(ActionFailed) = action {
                let result_code = &mut action_ctx.action_phase.result_code;
                if *result_code == -1 {
                    *result_code = ResultCode::ActionInvalid as i32;
                }
                if *result_code == ResultCode::NotEnoughBalance as i32
                    || *result_code == ResultCode::NotEnoughExtraBalance as i32
                {
                    action_ctx.action_phase.no_funds = true;
                }

                // TODO: Enforce state limits here if we want to persist
                // library changes even if action phase fails. This is
                // not the case for now, but this is how the reference
                // implementation works.

                // Apply action fine to the balance.
                action_ctx.apply_fine_on_error(
                    &mut self.balance,
                    &mut self.total_fees,
                    self.params.charge_action_fees_on_fail,
                )?;

                // Apply flags.
                res.bounce |= action_ctx.need_bounce_on_fail;

                // Ignore all other action.
                return Ok(res);
            }
        }

        // Check that the new state does not exceed size limits.
        // TODO: Ignore this step if account is going to be deleted anyway?
        if !self.is_special {
            let limits = &self.config.size_limits;
            let is_masterchain = self.address.is_masterchain();
            let check = match &self.state {
                AccountState::Active(current_state) => check_state_limits_diff(
                    current_state,
                    action_ctx.new_state,
                    limits,
                    is_masterchain,
                    &mut self.cached_storage_stat,
                ),
                AccountState::Uninit | AccountState::Frozen(_) => check_state_limits(
                    action_ctx.new_state.code.as_ref(),
                    action_ctx.new_state.data.as_ref(),
                    &action_ctx.new_state.libraries,
                    limits,
                    is_masterchain,
                    &mut self.cached_storage_stat,
                ),
            };

            if matches!(check, StateLimitsResult::Exceeds) {
                // Apply action fine to the balance.
                action_ctx.apply_fine_on_error(
                    &mut self.balance,
                    &mut self.total_fees,
                    self.params.charge_action_fees_on_fail,
                )?;

                // Apply flags.
                res.bounce |= action_ctx.need_bounce_on_fail;
                res.action_phase.result_code = ResultCode::StateOutOfLimits as i32;
                res.state_exceeds_limits = true;
                return Ok(res);
            }

            // NOTE: At this point if the state was successfully updated
            // (`check_state_limits[_diff]` returned `StateLimitsResult::Fits`)
            // cached storage stat will contain all visited cells for it.
        }

        if !action_ctx.action_fine.is_zero() {
            action_ctx
                .action_phase
                .total_action_fees
                .get_or_insert_default()
                .try_add_assign(*action_ctx.action_fine)?;
        }

        action_ctx
            .remaining_balance
            .try_add_assign(&action_ctx.reserved_balance)?;

        action_ctx.action_phase.result_code = 0;
        action_ctx.action_phase.result_arg = None;
        action_ctx.action_phase.success = true;

        if action_ctx.delete_account {
            if self.params.strict_extra_currency {
                // Require only native balance to be zero for strict EC behaviour.
                debug_assert!(action_ctx.remaining_balance.tokens.is_zero());
            } else {
                // Otherwise account must have a completely empty balance.
                debug_assert!(action_ctx.remaining_balance.is_zero());
            }
            action_ctx.action_phase.status_change = AccountStatusChange::Deleted;
            self.end_status = if action_ctx.remaining_balance.is_zero() {
                // Delete account only if its balance is completely empty
                // (both native and extra currency balance is zero).
                AccountStatus::NotExists
            } else {
                // Leave account as uninit if it still has some extra currencies.
                AccountStatus::Uninit
            };
            self.cached_storage_stat = None;
        }

        if let Some(fees) = action_ctx.action_phase.total_action_fees {
            // NOTE: Forwarding fees are not collected here.
            self.total_fees.try_add_assign(fees)?;
        }
        self.balance = action_ctx.remaining_balance;

        if let Some(inspector) = ctx.inspector {
            inspector.public_libs_diff = action_ctx.public_libs_diff.unwrap_or_default();
        }

        self.out_msgs = action_ctx.out_msgs;
        self.end_lt = action_ctx.end_lt;
        self.state = AccountState::Active(ctx.new_state);

        Ok(res)
    }

    /// `SendMsg` action.
    fn do_send_message(
        &self,
        mode: SendMsgFlags,
        out_msg: &Lazy<OwnedRelaxedMessage>,
        ctx: &mut ActionContext<'_>,
        mut rewrite: Option<MessageRewrite>,
    ) -> Result<SendMsgResult, ActionFailed> {
        const MASK: u8 = SendMsgFlags::all().bits();
        const INVALID_MASK: SendMsgFlags =
            SendMsgFlags::ALL_BALANCE.union(SendMsgFlags::WITH_REMAINING_BALANCE);
        const EXT_MSG_MASK: u8 = SendMsgFlags::PAY_FEE_SEPARATELY
            .union(SendMsgFlags::IGNORE_ERROR)
            .union(SendMsgFlags::BOUNCE_ON_ERROR)
            .bits();
        const DELETE_MASK: SendMsgFlags =
            SendMsgFlags::ALL_BALANCE.union(SendMsgFlags::DELETE_IF_EMPTY);

        // Check and apply mode flags.
        if mode.contains(SendMsgFlags::BOUNCE_ON_ERROR) {
            ctx.need_bounce_on_fail = true;
        }

        if mode.bits() & !MASK != 0 || mode.contains(INVALID_MASK) {
            // - Mode has some unknown bits;
            // - Or "ALL_BALANCE" flag was used with "WITH_REMAINING_BALANCE".
            return Err(ActionFailed);
        }

        // We should only skip if at least the mode is correct.
        let skip_invalid = mode.contains(SendMsgFlags::IGNORE_ERROR);
        let check_skip_invalid = |e: ResultCode, ctx: &mut ActionContext<'_>| {
            if skip_invalid {
                ctx.action_phase.skipped_actions += 1;
                Ok(SendMsgResult::Sent)
            } else {
                ctx.action_phase.result_code = e as i32;
                Err(ActionFailed)
            }
        };

        // Output message must be an ordinary cell.
        if out_msg.is_exotic() {
            return Err(ActionFailed);
        }

        // Unpack message.
        let mut relaxed_info;
        let mut state_init_cs;
        let mut body_cs;

        {
            let mut cs = out_msg.as_slice_allow_exotic();

            relaxed_info = RelaxedMsgInfo::load_from(&mut cs)?;
            state_init_cs = load_state_init_as_slice(&mut cs)?;
            body_cs = load_body_as_slice(&mut cs)?;

            if !cs.is_empty() {
                // Any remaining data in the message slice is treated as malicious data.
                return Err(ActionFailed);
            }
        }

        // Apply rewrite.
        let rewritten_state_init_cb;
        if let Some(MessageRewrite::StateInitToCell) = rewrite {
            if state_init_cs.size_refs() >= 2 {
                // Move state init to cell if it is more optimal.
                rewritten_state_init_cb = rewrite_state_init_to_cell(state_init_cs);
                state_init_cs = rewritten_state_init_cb.as_full_slice();
            } else {
                // Or try to move body to cell instead.
                rewrite = Some(MessageRewrite::BodyToCell);
            }
        }

        let rewritten_body_cs;
        if let Some(MessageRewrite::BodyToCell) = rewrite {
            if body_cs.size_bits() > 1 && !body_cs.get_bit(0).unwrap() {
                // Try to move a non-empty plain body to cell.
                rewritten_body_cs = rewrite_body_to_cell(body_cs);
                body_cs = rewritten_body_cs.as_full_slice();
            }
        }

        // Check info.
        let mut use_mc_prices = self.address.is_masterchain();
        match &mut relaxed_info {
            // Check internal outbound message.
            RelaxedMsgInfo::Int(info) => {
                // Rewrite source address.
                if !check_rewrite_src_addr(&self.address, &mut info.src) {
                    // NOTE: For some reason we are not ignoring this error.
                    ctx.action_phase.result_code = ResultCode::InvalidSrcAddr as i32;
                    return Err(ActionFailed);
                };

                // Rewrite destination address.
                if !check_rewrite_dst_addr(&self.config.workchains, &mut info.dst) {
                    return check_skip_invalid(ResultCode::InvalidDstAddr, ctx);
                }
                use_mc_prices |= info.dst.is_masterchain();

                // Rewrite extra currencies.
                if self.params.strict_extra_currency {
                    match normalize_extra_balance(
                        std::mem::take(&mut info.value.other),
                        MAX_MSG_EXTRA_CURRENCIES,
                    ) {
                        Ok(other) => info.value.other = other,
                        Err(BalanceExtraError::InvalidDict(_)) => {
                            return check_skip_invalid(ResultCode::NotEnoughBalance, ctx);
                        }
                        Err(BalanceExtraError::OutOfLimit) => {
                            return check_skip_invalid(ResultCode::TooManyExtraCurrencies, ctx);
                        }
                    }
                }

                // Reset fees.
                info.ihr_fee = {
                    let mut hasher = Sha256::new();
                    hasher.update(self.params.rand_seed.as_slice());
                    hasher.update(&info.created_lt.to_be_bytes());
                    let hash = hasher.finalize();

                    let mut bytes = [0u8; 4];
                    bytes.copy_from_slice(&hash[..4]);

                    let value = u32::from_be_bytes(bytes);
                    Tokens::new(value as u128)
                };
                info.fwd_fee = Tokens::ZERO;

                // Rewrite message timings.
                info.created_at = self.params.block_unixtime;
                info.created_lt = ctx.end_lt;

                // Clear flags.
                info.ihr_disabled = true;
                info.bounced = false;
            }
            // Check external outbound message.
            RelaxedMsgInfo::ExtOut(info) => {
                if mode.bits() & !EXT_MSG_MASK != 0 {
                    // Invalid mode for an outgoing external message.
                    return Err(ActionFailed);
                }

                // Rewrite source address.
                if !check_rewrite_src_addr(&self.address, &mut info.src) {
                    ctx.action_phase.result_code = ResultCode::InvalidSrcAddr as i32;
                    return Err(ActionFailed);
                }

                // Rewrite message timings.
                info.created_at = self.params.block_unixtime;
                info.created_lt = ctx.end_lt;
            }
        };

        // Compute fine per cell. Account is required to pay it for every visited cell.
        let prices = self.config.fwd_prices(use_mc_prices);
        let mut max_cell_count = self.config.size_limits.max_msg_cells;
        let fine_per_cell;
        if self.is_special {
            fine_per_cell = 0;
        } else {
            fine_per_cell = (prices.cell_price >> 16) / 4;

            let mut funds = ctx.remaining_balance.tokens;
            if let RelaxedMsgInfo::Int(info) = &relaxed_info {
                if !mode.contains(SendMsgFlags::ALL_BALANCE)
                    && !mode.contains(SendMsgFlags::PAY_FEE_SEPARATELY)
                {
                    let mut new_funds = info.value.tokens;

                    if mode.contains(SendMsgFlags::WITH_REMAINING_BALANCE)
                        && (|| {
                            let msg_balance_remaining = match &ctx.received_message {
                                Some(msg) => msg.balance_remaining.tokens,
                                None => Tokens::ZERO,
                            };
                            new_funds.try_add_assign(msg_balance_remaining)?;
                            new_funds.try_sub_assign(ctx.compute_phase.gas_fees)?;
                            new_funds.try_sub_assign(*ctx.action_fine)?;

                            Ok::<_, tycho_types::error::Error>(())
                        })()
                        .is_err()
                    {
                        return check_skip_invalid(ResultCode::NotEnoughBalance, ctx);
                    }

                    funds = std::cmp::min(funds, new_funds);
                }
            }

            if funds < Tokens::new(max_cell_count as u128 * fine_per_cell as u128) {
                debug_assert_ne!(fine_per_cell, 0);
                max_cell_count = (funds.into_inner() / fine_per_cell as u128)
                    .try_into()
                    .unwrap_or(u32::MAX);
            }
        }

        let collect_fine = |cells: u32, ctx: &mut ActionContext<'_>| {
            let mut fine = Tokens::new(
                fine_per_cell.saturating_mul(std::cmp::min(max_cell_count, cells) as u64) as _,
            );
            fine = std::cmp::min(fine, ctx.remaining_balance.tokens);
            ctx.action_fine.try_add_assign(fine)?;
            ctx.remaining_balance.try_sub_assign_tokens(fine)
        };

        // Compute size of the message.
        let stats = 'stats: {
            let mut stats = ExtStorageStat::with_limits(StorageStatLimits {
                bit_count: self.config.size_limits.max_msg_bits,
                cell_count: max_cell_count,
            });

            'valid: {
                for cell in state_init_cs.references() {
                    if !stats.add_cell(cell) {
                        break 'valid;
                    }
                }

                for cell in body_cs.references() {
                    if !stats.add_cell(cell) {
                        break 'valid;
                    }
                }

                // Add EC dict when `strict` behaviour is disabled.
                if !self.params.strict_extra_currency {
                    if let RelaxedMsgInfo::Int(int) = &relaxed_info {
                        if let Some(cell) = int.value.other.as_dict().root() {
                            if !stats.add_cell(cell.as_ref()) {
                                break 'valid;
                            }
                        }
                    }
                }

                break 'stats stats.stats();
            }

            collect_fine(stats.cells, ctx)?;
            return check_skip_invalid(ResultCode::MessageOutOfLimits, ctx);
        };

        // Make sure that `check_skip_invalid` will collect fine.
        let check_skip_invalid = move |e: ResultCode, ctx: &mut ActionContext<'_>| {
            collect_fine(stats.cell_count as _, ctx)?;
            check_skip_invalid(e, ctx)
        };

        // Compute forwarding fees.
        let fwd_fee = if self.is_special {
            Tokens::ZERO
        } else {
            prices.compute_fwd_fee(stats)
        };

        // Finalize message.
        let msg;
        let fees_collected;
        match &mut relaxed_info {
            RelaxedMsgInfo::Int(info) => {
                // Rewrite message value and compute how much will be withdwarn.
                let value_to_pay = match ctx.rewrite_message_value(&mut info.value, mode, fwd_fee) {
                    Ok(total_value) => total_value,
                    Err(_) => return check_skip_invalid(ResultCode::NotEnoughBalance, ctx),
                };

                // Check if remaining balance is enough to pay `total_value`.
                if ctx.remaining_balance.tokens < value_to_pay {
                    return check_skip_invalid(ResultCode::NotEnoughBalance, ctx);
                }

                // Check that the number of extra currencies is whithin the limit.
                if self.params.strict_extra_currency
                    && !check_extra_balance(&info.value.other, MAX_MSG_EXTRA_CURRENCIES)
                {
                    return check_skip_invalid(ResultCode::TooManyExtraCurrencies, ctx);
                }

                // Try to withdraw extra currencies from the remaining balance.
                let other = match ctx.remaining_balance.other.checked_sub(&info.value.other) {
                    Ok(other) => other,
                    Err(_) => return check_skip_invalid(ResultCode::NotEnoughExtraBalance, ctx),
                };

                // Split forwarding fee.
                fees_collected = prices.get_first_part(fwd_fee);
                info.fwd_fee = fwd_fee - fees_collected;

                // Finalize message.
                msg = match build_message(&relaxed_info, &state_init_cs, &body_cs) {
                    Ok(msg) => msg,
                    Err(_) => match MessageRewrite::next(rewrite) {
                        Some(rewrite) => return Ok(SendMsgResult::Rewrite(rewrite)),
                        None => return check_skip_invalid(ResultCode::FailedToFitMessage, ctx),
                    },
                };

                // Clear message balance if it was used.
                if let Some(msg) = &mut ctx.received_message {
                    if mode.contains(SendMsgFlags::ALL_BALANCE)
                        || mode.contains(SendMsgFlags::WITH_REMAINING_BALANCE)
                    {
                        if self.params.strict_extra_currency {
                            // Only native balance was used.
                            msg.balance_remaining.tokens = Tokens::ZERO;
                        } else {
                            // All balance was used.
                            msg.balance_remaining = CurrencyCollection::ZERO;
                        }
                    }
                }

                // Update the remaining balance.
                ctx.remaining_balance.tokens -= value_to_pay;
                ctx.remaining_balance.other = other;
            }
            RelaxedMsgInfo::ExtOut(_) => {
                // Check if the remaining balance is enough to pay forwarding fees.
                if ctx.remaining_balance.tokens < fwd_fee {
                    return check_skip_invalid(ResultCode::NotEnoughBalance, ctx);
                }

                // Finalize message.
                msg = match build_message(&relaxed_info, &state_init_cs, &body_cs) {
                    Ok(msg) => msg,
                    Err(_) => match MessageRewrite::next(rewrite) {
                        Some(rewrite) => return Ok(SendMsgResult::Rewrite(rewrite)),
                        None => return check_skip_invalid(ResultCode::FailedToFitMessage, ctx),
                    },
                };

                // Update the remaining balance.
                ctx.remaining_balance.tokens -= fwd_fee;
                fees_collected = fwd_fee;
            }
        }

        update_total_msg_stat(
            &mut ctx.action_phase.total_message_size,
            stats,
            msg.bit_len(),
        );

        ctx.action_phase.messages_created += 1;
        ctx.end_lt += 1;

        ctx.out_msgs.push(msg);

        *ctx.action_phase.total_action_fees.get_or_insert_default() += fees_collected;
        *ctx.action_phase.total_fwd_fees.get_or_insert_default() += fwd_fee;

        if mode.contains(DELETE_MASK) {
            ctx.delete_account = if self.params.strict_extra_currency {
                // Delete when native balance was used.
                debug_assert!(ctx.remaining_balance.tokens.is_zero());
                ctx.reserved_balance.tokens.is_zero()
            } else {
                // Delete when full balance was used.
                debug_assert!(ctx.remaining_balance.is_zero());
                ctx.reserved_balance.is_zero()
            };
        }

        Ok(SendMsgResult::Sent)
    }

    /// `SetCode` action.
    fn do_set_code(&self, new_code: Cell, ctx: &mut ActionContext<'_>) -> Result<(), ActionFailed> {
        // Update context.
        ctx.new_state.code = Some(new_code);
        ctx.action_phase.special_actions += 1;

        // Done
        Ok(())
    }

    /// `ReserveCurrency` action.
    fn do_reserve_currency(
        &self,
        mode: ReserveCurrencyFlags,
        mut reserve: CurrencyCollection,
        ctx: &mut ActionContext<'_>,
    ) -> Result<(), ActionFailed> {
        const MASK: u8 = ReserveCurrencyFlags::all().bits();

        // Check and apply mode flags.
        if mode.contains(ReserveCurrencyFlags::BOUNCE_ON_ERROR) {
            ctx.need_bounce_on_fail = true;
        }

        if mode.bits() & !MASK != 0 {
            // Invalid mode.
            return Err(ActionFailed);
        }

        if self.params.strict_extra_currency && !reserve.other.is_empty() {
            // Cannot reserve extra currencies when strict behaviour is enabled.
            return Err(ActionFailed);
        }

        if mode.contains(ReserveCurrencyFlags::WITH_ORIGINAL_BALANCE) {
            if mode.contains(ReserveCurrencyFlags::REVERSE) {
                if self.params.strict_extra_currency {
                    reserve.tokens = ctx
                        .original_balance
                        .tokens
                        .checked_sub(reserve.tokens)
                        .ok_or(ActionFailed)?;
                } else {
                    reserve = ctx.original_balance.checked_sub(&reserve)?;
                }
            } else if self.params.strict_extra_currency {
                reserve.try_add_assign_tokens(ctx.original_balance.tokens)?;
            } else {
                reserve.try_add_assign(ctx.original_balance)?;
            }
        } else if mode.contains(ReserveCurrencyFlags::REVERSE) {
            // Invalid mode.
            return Err(ActionFailed);
        }

        if mode.contains(ReserveCurrencyFlags::IGNORE_ERROR) {
            // Clamp balance.
            reserve = reserve.checked_clamp(&ctx.remaining_balance)?;
        }

        // Reserve balance.
        let mut new_balance = CurrencyCollection {
            tokens: match ctx.remaining_balance.tokens.checked_sub(reserve.tokens) {
                Some(tokens) => tokens,
                None => {
                    ctx.action_phase.result_code = ResultCode::NotEnoughBalance as i32;
                    return Err(ActionFailed);
                }
            },
            other: match ctx.remaining_balance.other.checked_sub(&reserve.other) {
                Ok(other) => other,
                Err(_) => {
                    ctx.action_phase.result_code = ResultCode::NotEnoughExtraBalance as i32;
                    return Err(ActionFailed);
                }
            },
        };

        // Always normalize reserved balance.
        reserve.other.normalize()?;

        // Apply "ALL_BUT" flag. Leave only "new_balance", reserve everything else.
        if mode.contains(ReserveCurrencyFlags::ALL_BUT) {
            if self.params.strict_extra_currency {
                std::mem::swap(&mut new_balance.tokens, &mut reserve.tokens);
            } else {
                std::mem::swap(&mut new_balance, &mut reserve);
            }
        }

        // Update context.
        ctx.remaining_balance = new_balance;
        ctx.reserved_balance.try_add_assign(&reserve)?;
        ctx.action_phase.special_actions += 1;

        // Done
        Ok(())
    }

    /// `ChangeLibrary` action.
    fn do_change_library(
        &self,
        mode: ChangeLibraryMode,
        mut lib: LibRef,
        ctx: &mut ActionContext<'_>,
    ) -> Result<(), ActionFailed> {
        // Having both "ADD_PRIVATE" and "ADD_PUBLIC" flags is invalid.
        const INVALID_MODE: ChangeLibraryMode = ChangeLibraryMode::from_bits_retain(
            ChangeLibraryMode::ADD_PRIVATE.bits() | ChangeLibraryMode::ADD_PUBLIC.bits(),
        );

        // Check and apply mode flags.
        if mode.contains(ChangeLibraryMode::BOUNCE_ON_ERROR) {
            ctx.need_bounce_on_fail = true;
        }

        if mode.contains(INVALID_MODE) {
            return Err(ActionFailed);
        }

        let hash = match &lib {
            LibRef::Cell(cell) => cell.repr_hash(),
            LibRef::Hash(hash) => hash,
        };

        let is_masterchain = self.address.is_masterchain();

        let add_public = mode.contains(ChangeLibraryMode::ADD_PUBLIC);
        if add_public || mode.contains(ChangeLibraryMode::ADD_PRIVATE) {
            // Add new library.
            let mut was_public = None;
            if let Ok(Some(prev)) = ctx.new_state.libraries.get(hash) {
                if prev.public == add_public {
                    // Do nothing if library already exists with the same `public` flag.
                    ctx.action_phase.special_actions += 1;
                    return Ok(());
                } else {
                    // If library exists allow changing its `public` flag when `LibRef::Hash` was used.
                    was_public = Some(prev.public);
                    lib = LibRef::Cell(prev.root);
                }
            }

            let LibRef::Cell(root) = lib else {
                ctx.action_phase.result_code = ResultCode::NoLibCode as i32;
                return Err(ActionFailed);
            };

            let mut stats = ExtStorageStat::with_limits(StorageStatLimits {
                bit_count: u32::MAX,
                cell_count: self.config.size_limits.max_library_cells,
            });
            if !stats.add_cell(root.as_ref()) {
                ctx.action_phase.result_code = ResultCode::LibOutOfLimits as i32;
                return Err(ActionFailed);
            }

            // Add library.
            match ctx.new_state.libraries.set(*root.repr_hash(), SimpleLib {
                public: add_public,
                root: root.clone(),
            }) {
                // Track removed public libs by an inspector for masterchain accounts.
                Ok(_) if is_masterchain => {
                    // Track removed or added public libs by an inspector.
                    if let Some(diff) = &mut ctx.public_libs_diff {
                        match (was_public, add_public) {
                            // Add new public libraries.
                            (None, true) | (Some(false), true) => {
                                diff.push(PublicLibraryChange::Add(root))
                            }
                            // Remove public libraries
                            (Some(true), false) => {
                                diff.push(PublicLibraryChange::Remove(*root.repr_hash()));
                            }
                            // Ignore unchanged or private libraries.
                            _ => {}
                        }
                    }
                }
                Ok(_) => {}
                Err(_) => {
                    ctx.action_phase.result_code = ResultCode::InvalidLibrariesDict as i32;
                    return Err(ActionFailed);
                }
            }
        } else {
            // Remove library.
            match ctx.new_state.libraries.remove(hash) {
                // Track removed public libs by an inspector for masterchain accounts.
                Ok(Some(lib)) if is_masterchain && lib.public => {
                    if let Some(diff) = &mut ctx.public_libs_diff {
                        diff.push(PublicLibraryChange::Remove(*hash));
                    }
                }
                Ok(_) => {}
                Err(_) => {
                    ctx.action_phase.result_code = ResultCode::InvalidLibrariesDict as i32;
                    return Err(ActionFailed);
                }
            }
        }

        // Update context.
        ctx.action_phase.special_actions += 1;

        // Done
        Ok(())
    }
}

struct ActionContext<'a> {
    need_bounce_on_fail: bool,
    strict_extra_currency: bool,
    received_message: Option<&'a mut ReceivedMessage>,
    original_balance: &'a CurrencyCollection,
    remaining_balance: CurrencyCollection,
    reserved_balance: CurrencyCollection,
    action_fine: &'a mut Tokens,
    new_state: &'a mut StateInit,
    end_lt: u64,
    out_msgs: Vec<Lazy<OwnedMessage>>,
    delete_account: bool,
    public_libs_diff: Option<Vec<PublicLibraryChange>>,

    compute_phase: &'a ExecutedComputePhase,
    action_phase: &'a mut ActionPhase,
}

impl ActionContext<'_> {
    fn apply_fine_on_error(
        &mut self,
        balance: &mut CurrencyCollection,
        total_fees: &mut Tokens,
        charge_action_fees: bool,
    ) -> Result<(), Error> {
        // Compute the resulting action fine (it must not be greater than the account balance).
        if charge_action_fees {
            self.action_fine
                .try_add_assign(self.action_phase.total_action_fees.unwrap_or_default())?;
        }

        // Reset forwarding fee since no messages were actually sent.
        // NOTE: This behaviour is not present in the reference implementation
        //       but it seems to be more correct.
        self.action_phase.total_fwd_fees = None;

        // Charge the account balance for the action fine.
        self.action_phase.total_action_fees = Some(*self.action_fine).filter(|t| !t.is_zero());

        balance.tokens.try_sub_assign(*self.action_fine)?;
        total_fees.try_add_assign(*self.action_fine)
    }

    fn rewrite_message_value(
        &self,
        value: &mut CurrencyCollection,
        mut mode: SendMsgFlags,
        fees_total: Tokens,
    ) -> Result<Tokens, ActionFailed> {
        // Update `value` based on flags.
        if mode.contains(SendMsgFlags::ALL_BALANCE) {
            // Attach all remaining balance to the message.
            if self.strict_extra_currency {
                // Attach only native balance when strict behaviour is enabled.
                value.tokens = self.remaining_balance.tokens;
            } else {
                // Attach both native and extra currencies otherwise.
                *value = self.remaining_balance.clone();
            };
            // Pay fees from the attached value.
            mode.remove(SendMsgFlags::PAY_FEE_SEPARATELY);
        } else if mode.contains(SendMsgFlags::WITH_REMAINING_BALANCE) {
            if let Some(msg) = &self.received_message {
                // Attach all remaining balance of the inbound message.
                // (in addition to the original value).
                if self.strict_extra_currency {
                    // Attach only native balance when strict behaviour is enabled.
                    value.try_add_assign_tokens(msg.balance_remaining.tokens)?;
                } else {
                    // Attach both native and extra currencies otherwise.
                    value.try_add_assign(&msg.balance_remaining)?;
                }
            }

            if !mode.contains(SendMsgFlags::PAY_FEE_SEPARATELY) {
                // Try to exclude fees from the attached value.
                value.try_sub_assign_tokens(*self.action_fine)?;
                value.try_sub_assign_tokens(self.compute_phase.gas_fees)?;
            }
        }

        // Compute `value + fees`.
        let mut total = value.tokens;
        if mode.contains(SendMsgFlags::PAY_FEE_SEPARATELY) {
            total.try_add_assign(fees_total)?;
        } else {
            value.tokens.try_sub_assign(fees_total)?;
        }

        // Done
        Ok(total)
    }
}

struct ActionFailed;

impl From<anyhow::Error> for ActionFailed {
    #[inline]
    fn from(_: anyhow::Error) -> Self {
        Self
    }
}

impl From<Error> for ActionFailed {
    #[inline]
    fn from(_: Error) -> Self {
        Self
    }
}

#[derive(Debug, Clone, Copy)]
enum SendMsgResult {
    Sent,
    Rewrite(MessageRewrite),
}

#[derive(Debug, Clone, Copy)]
enum MessageRewrite {
    StateInitToCell,
    BodyToCell,
}

impl MessageRewrite {
    pub fn next(rewrite: Option<Self>) -> Option<Self> {
        match rewrite {
            None => Some(Self::StateInitToCell),
            Some(Self::StateInitToCell) => Some(Self::BodyToCell),
            Some(Self::BodyToCell) => None,
        }
    }
}

fn load_state_init_as_slice<'a>(cs: &mut CellSlice<'a>) -> Result<CellSlice<'a>, Error> {
    let mut res_cs = *cs;

    // (Maybe (Either StateInit ^StateInit))
    if cs.load_bit()? {
        if cs.load_bit()? {
            // right$1 ^StateInit
            let state_root = cs.load_reference()?;
            if state_root.is_exotic() {
                // Only ordinary cells are allowed as state init.
                return Err(Error::InvalidData);
            }

            // Validate `StateInit` by reading.
            let mut cs = state_root.as_slice_allow_exotic();
            StateInit::load_from(&mut cs)?;

            // And ensure that nothing more was left.
            if !cs.is_empty() {
                return Err(Error::CellOverflow);
            }
        } else {
            // left$0 StateInit

            // Validate `StateInit` by reading.
            StateInit::load_from(cs)?;
        }
    }

    res_cs.skip_last(cs.size_bits(), cs.size_refs())?;
    Ok(res_cs)
}

fn load_body_as_slice<'a>(cs: &mut CellSlice<'a>) -> Result<CellSlice<'a>, Error> {
    let res_cs = *cs;

    if cs.load_bit()? {
        // right$1 ^X
        cs.skip_first(0, 1)?;
    } else {
        // left$0 X
        cs.load_remaining();
    }

    Ok(res_cs)
}

fn rewrite_state_init_to_cell(mut cs: CellSlice<'_>) -> CellBuilder {
    // Skip prefix `just$1 (left$0 ...)`.
    let prefix = cs.load_small_uint(2).unwrap();
    debug_assert_eq!(prefix, 0b10);

    // Build ^StateInit.
    let cell = CellBuilder::build_from(cs).unwrap();

    // Build `just$1 (right$1 ^StateInit)`.
    let mut b = CellBuilder::new();
    b.store_small_uint(0b11, 2).unwrap();
    b.store_reference(cell).unwrap();

    // Done
    b
}

fn rewrite_body_to_cell(mut cs: CellSlice<'_>) -> CellBuilder {
    // Skip prefix `left$0 ...`.
    let prefix = cs.load_bit().unwrap();
    debug_assert!(!prefix);

    // Build ^X.
    let cell = CellBuilder::build_from(cs).unwrap();

    // Build `right$1 ^X`.
    let mut b = CellBuilder::new();
    b.store_bit_one().unwrap();
    b.store_reference(cell).unwrap();

    // Done
    b
}

fn build_message(
    info: &RelaxedMsgInfo,
    state_init_cs: &CellSlice<'_>,
    body_cs: &CellSlice<'_>,
) -> Result<Lazy<OwnedMessage>, Error> {
    CellBuilder::build_from((info, state_init_cs, body_cs)).map(|cell| {
        // SAFETY: Tuple is always built as ordinary cell.
        unsafe { Lazy::from_raw_unchecked(cell) }
    })
}

fn update_total_msg_stat(
    total_message_size: &mut StorageUsedShort,
    stats: CellTreeStats,
    root_bits: u16,
) {
    let bits_diff = VarUint56::new(stats.bit_count.saturating_add(root_bits as _));
    let cells_diff = VarUint56::new(stats.cell_count.saturating_add(1));

    total_message_size.bits = total_message_size.bits.saturating_add(bits_diff);
    total_message_size.cells = total_message_size.cells.saturating_add(cells_diff);
}

fn check_extra_balance(value: &ExtraCurrencyCollection, limit: usize) -> bool {
    for (i, entry) in value.as_dict().iter().enumerate() {
        if i > limit || entry.is_err() {
            return false;
        }
    }
    true
}

fn normalize_extra_balance(
    value: ExtraCurrencyCollection,
    limit: usize,
) -> Result<ExtraCurrencyCollection, BalanceExtraError> {
    let mut result = value.clone();
    for (i, entry) in value.as_dict().iter().enumerate() {
        if i > limit {
            return Err(BalanceExtraError::OutOfLimit);
        }
        let (currency_id, other) = entry.map_err(BalanceExtraError::InvalidDict)?;
        if other.is_zero() {
            result
                .as_dict_mut()
                .remove(currency_id)
                .map_err(BalanceExtraError::InvalidDict)?;
        }
    }
    Ok(result)
}

enum BalanceExtraError {
    OutOfLimit,
    InvalidDict(#[allow(unused)] Error),
}

#[repr(i32)]
#[derive(Debug, thiserror::Error)]
enum ResultCode {
    #[error("invalid action list")]
    ActionListInvalid = 32,
    #[error("too many actions")]
    TooManyActions = 33,
    #[error("invalid or unsupported action")]
    ActionInvalid = 34,
    #[error("invalid source address")]
    InvalidSrcAddr = 35,
    #[error("invalid destination address")]
    InvalidDstAddr = 36,
    #[error("not enough balance (base currency)")]
    NotEnoughBalance = 37,
    #[error("not enough balance (extra currency)")]
    NotEnoughExtraBalance = 38,
    #[error("failed to fit message into cell")]
    FailedToFitMessage = 39,
    #[error("message exceeds limits")]
    MessageOutOfLimits = 40,
    #[error("library code not found")]
    NoLibCode = 41,
    #[error("failed to change libraries dict")]
    InvalidLibrariesDict = 42,
    #[error("too many library cells")]
    LibOutOfLimits = 43,
    #[error("too many extra currencies")]
    TooManyExtraCurrencies = 44,
    #[error("state exceeds limits")]
    StateOutOfLimits = 50,
}

// TODO: Move into config parm 43.
const MAX_MSG_EXTRA_CURRENCIES: usize = 2;

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use tycho_asm_macros::tvmasm;
    use tycho_types::merkle::MerkleProof;
    use tycho_types::models::{
        Anycast, IntAddr, MessageLayout, MsgInfo, RelaxedIntMsgInfo, RelaxedMessage, StdAddr,
        VarAddr,
    };
    use tycho_types::num::{Uint9, VarUint248};

    use super::*;
    use crate::tests::{make_default_config, make_default_params};
    use crate::ExecutorParams;

    const STUB_ADDR: StdAddr = StdAddr::new(0, HashBytes::ZERO);
    const OK_BALANCE: Tokens = Tokens::new(1_000_000_000);
    const OK_GAS: Tokens = Tokens::new(1_000_000);

    fn stub_compute_phase(gas_fees: Tokens) -> ExecutedComputePhase {
        ExecutedComputePhase {
            success: true,
            msg_state_used: false,
            account_activated: false,
            gas_fees,
            gas_used: Default::default(),
            gas_limit: Default::default(),
            gas_credit: None,
            mode: 0,
            exit_code: 0,
            exit_arg: None,
            vm_steps: 0,
            vm_init_state_hash: Default::default(),
            vm_final_state_hash: Default::default(),
        }
    }

    fn empty_action_phase() -> ActionPhase {
        ActionPhase {
            success: true,
            valid: true,
            no_funds: false,
            status_change: AccountStatusChange::Unchanged,
            total_fwd_fees: None,
            total_action_fees: None,
            result_code: 0,
            result_arg: None,
            total_actions: 0,
            special_actions: 0,
            skipped_actions: 0,
            messages_created: 0,
            action_list_hash: *Cell::empty_cell_ref().repr_hash(),
            total_message_size: Default::default(),
        }
    }

    fn make_action_list<I: IntoIterator<Item: Store>>(actions: I) -> Cell {
        let mut root = Cell::default();
        for action in actions {
            root = CellBuilder::build_from((root, action)).unwrap();
        }
        root
    }

    fn make_relaxed_message(
        info: impl Into<RelaxedMsgInfo>,
        init: Option<StateInit>,
        body: Option<CellBuilder>,
    ) -> Lazy<OwnedRelaxedMessage> {
        let body = match &body {
            None => Cell::empty_cell_ref().as_slice_allow_exotic(),
            Some(cell) => cell.as_full_slice(),
        };
        Lazy::new(&RelaxedMessage {
            info: info.into(),
            init,
            body,
            layout: None,
        })
        .unwrap()
        .cast_into()
    }

    fn compute_full_stats(msg: &Lazy<OwnedMessage>, params: &ExecutorParams) -> StorageUsedShort {
        let msg = 'cell: {
            if params.strict_extra_currency {
                let mut parsed = msg.load().unwrap();
                if let MsgInfo::Int(int) = &mut parsed.info {
                    if !int.value.other.is_empty() {
                        int.value.other = ExtraCurrencyCollection::new();
                        break 'cell CellBuilder::build_from(parsed).unwrap();
                    }
                }
            }
            msg.inner().clone()
        };

        let stats = {
            let mut stats = ExtStorageStat::with_limits(StorageStatLimits::UNLIMITED);
            assert!(stats.add_cell(msg.as_ref()));
            stats.stats()
        };
        StorageUsedShort {
            cells: VarUint56::new(stats.cell_count),
            bits: VarUint56::new(stats.bit_count),
        }
    }

    fn original_balance(
        state: &ExecutorState<'_>,
        compute_phase: &ExecutedComputePhase,
    ) -> CurrencyCollection {
        state
            .balance
            .clone()
            .checked_add(&compute_phase.gas_fees.into())
            .unwrap()
    }

    #[test]
    fn empty_actions() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE);

        let compute_phase = stub_compute_phase(OK_GAS);
        let prev_total_fees = state.total_fees;
        let prev_balance = state.balance.clone();
        let prev_end_lt = state.end_lt;

        let ActionPhaseFull {
            action_phase,
            action_fine,
            state_exceeds_limits,
            bounce,
        } = state.action_phase(ActionPhaseContext {
            received_message: None,
            original_balance: original_balance(&state, &compute_phase),
            new_state: StateInit::default(),
            actions: Cell::empty_cell(),
            compute_phase: &compute_phase,
            inspector: None,
        })?;

        assert_eq!(action_phase, empty_action_phase());
        assert_eq!(action_fine, Tokens::ZERO);
        assert!(!state_exceeds_limits);
        assert!(!bounce);
        assert_eq!(state.total_fees, prev_total_fees);
        assert_eq!(state.balance, prev_balance);
        assert_eq!(state.end_lt, prev_end_lt);
        Ok(())
    }

    #[test]
    fn too_many_actions() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE);

        let compute_phase = stub_compute_phase(OK_GAS);
        let prev_total_fees = state.total_fees;
        let prev_balance = state.balance.clone();
        let prev_end_lt = state.end_lt;

        let actions = make_action_list(
            std::iter::repeat_with(|| OutAction::SetCode {
                new_code: Cell::empty_cell(),
            })
            .take(300),
        );

        let ActionPhaseFull {
            action_phase,
            action_fine,
            state_exceeds_limits,
            bounce,
        } = state.action_phase(ActionPhaseContext {
            received_message: None,
            original_balance: original_balance(&state, &compute_phase),
            new_state: StateInit::default(),
            actions: actions.clone(),
            compute_phase: &compute_phase,
            inspector: None,
        })?;

        assert_eq!(action_phase, ActionPhase {
            success: false,
            valid: false,
            result_code: ResultCode::TooManyActions as i32,
            result_arg: Some(256),
            action_list_hash: *actions.repr_hash(),
            ..empty_action_phase()
        });
        assert_eq!(action_fine, Tokens::ZERO);
        assert!(!state_exceeds_limits);
        assert!(!bounce);
        assert_eq!(state.total_fees, prev_total_fees);
        assert_eq!(state.balance, prev_balance);
        assert_eq!(state.end_lt, prev_end_lt);
        Ok(())
    }

    #[test]
    fn invalid_action_list() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE);

        let compute_phase = stub_compute_phase(OK_GAS);
        let prev_total_fees = state.total_fees;
        let prev_balance = state.balance.clone();
        let prev_end_lt = state.end_lt;

        let actions = CellBuilder::build_from((
            CellBuilder::build_from(MerkleProof::default())?,
            OutAction::SetCode {
                new_code: Cell::default(),
            },
        ))?;

        let ActionPhaseFull {
            action_phase,
            action_fine,
            state_exceeds_limits,
            bounce,
        } = state.action_phase(ActionPhaseContext {
            received_message: None,
            original_balance: original_balance(&state, &compute_phase),
            new_state: StateInit::default(),
            actions: actions.clone(),
            compute_phase: &compute_phase,
            inspector: None,
        })?;

        assert_eq!(action_phase, ActionPhase {
            success: false,
            valid: false,
            result_code: ResultCode::ActionListInvalid as i32,
            result_arg: Some(1),
            action_list_hash: *actions.repr_hash(),
            ..empty_action_phase()
        });
        assert_eq!(action_fine, Tokens::ZERO);
        assert!(!state_exceeds_limits);
        assert!(!bounce);
        assert_eq!(state.total_fees, prev_total_fees);
        assert_eq!(state.balance, prev_balance);
        assert_eq!(state.end_lt, prev_end_lt);
        Ok(())
    }

    #[test]
    fn invalid_action() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE);

        let compute_phase = stub_compute_phase(OK_GAS);
        let prev_total_fees = state.total_fees;
        let prev_balance = state.balance.clone();
        let prev_end_lt = state.end_lt;

        let set_code_action = {
            let mut b = CellBuilder::new();
            OutAction::SetCode {
                new_code: Cell::empty_cell(),
            }
            .store_into(&mut b, Cell::empty_context())?;
            b
        };
        let invalid_action = {
            let mut b = CellBuilder::new();
            b.store_u32(0xdeafbeaf)?;
            b
        };

        let actions = make_action_list([
            set_code_action.as_full_slice(),
            set_code_action.as_full_slice(),
            invalid_action.as_full_slice(),
            set_code_action.as_full_slice(),
            set_code_action.as_full_slice(),
        ]);

        let ActionPhaseFull {
            action_phase,
            action_fine,
            state_exceeds_limits,
            bounce,
        } = state.action_phase(ActionPhaseContext {
            received_message: None,
            original_balance: original_balance(&state, &compute_phase),
            new_state: StateInit::default(),
            actions: actions.clone(),
            compute_phase: &compute_phase,
            inspector: None,
        })?;

        assert_eq!(action_phase, ActionPhase {
            success: false,
            valid: false,
            result_code: ResultCode::ActionInvalid as i32,
            result_arg: Some(2),
            action_list_hash: *actions.repr_hash(),
            total_actions: 5,
            ..empty_action_phase()
        });
        assert_eq!(action_fine, Tokens::ZERO);
        assert!(!state_exceeds_limits);
        assert!(!bounce);
        assert_eq!(state.total_fees, prev_total_fees);
        assert_eq!(state.balance, prev_balance);
        assert_eq!(state.end_lt, prev_end_lt);
        Ok(())
    }

    #[test]
    fn strict_reserve_extra_currency() -> Result<()> {
        let mut params = make_default_params();
        params.strict_extra_currency = true;
        let config = make_default_config();
        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE);
        let prev_balance = state.balance.clone();

        let compute_phase = stub_compute_phase(OK_GAS);
        let prev_total_fees = state.total_fees;
        let prev_end_lt = state.end_lt;

        let actions = make_action_list([OutAction::ReserveCurrency {
            mode: ReserveCurrencyFlags::empty(),
            value: CurrencyCollection {
                tokens: Tokens::ZERO,
                other: BTreeMap::from_iter([(123u32, VarUint248::new(10))]).try_into()?,
            },
        }]);

        let ActionPhaseFull {
            action_phase,
            action_fine,
            state_exceeds_limits,
            bounce,
        } = state.action_phase(ActionPhaseContext {
            received_message: None,
            original_balance: original_balance(&state, &compute_phase),
            new_state: StateInit::default(),
            actions: actions.clone(),
            compute_phase: &compute_phase,
            inspector: None,
        })?;

        assert_eq!(action_phase, ActionPhase {
            success: false,
            valid: true,
            result_code: ResultCode::ActionInvalid as i32,
            result_arg: Some(0),
            action_list_hash: *actions.repr_hash(),
            total_actions: 1,
            ..empty_action_phase()
        });
        assert_eq!(action_fine, Tokens::ZERO);
        assert!(!state_exceeds_limits);
        assert!(!bounce);
        assert_eq!(state.total_fees, prev_total_fees);
        assert_eq!(state.balance, prev_balance);
        assert_eq!(state.end_lt, prev_end_lt);
        Ok(())
    }

    #[test]
    fn send_single_message() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE);

        let compute_phase = stub_compute_phase(OK_GAS);
        let prev_total_fees = state.total_fees;
        let prev_balance = state.balance.clone();
        let prev_end_lt = state.end_lt;

        let msg_value = Tokens::new(500_000_000);

        let actions = make_action_list([OutAction::SendMsg {
            mode: SendMsgFlags::empty(),
            out_msg: make_relaxed_message(
                RelaxedIntMsgInfo {
                    dst: STUB_ADDR.into(),
                    value: msg_value.into(),
                    ..Default::default()
                },
                None,
                None,
            ),
        }]);

        let ActionPhaseFull {
            action_phase,
            action_fine,
            state_exceeds_limits,
            bounce,
        } = state.action_phase(ActionPhaseContext {
            received_message: None,
            original_balance: original_balance(&state, &compute_phase),
            new_state: StateInit::default(),
            actions: actions.clone(),
            compute_phase: &compute_phase,
            inspector: None,
        })?;

        assert_eq!(action_fine, Tokens::ZERO);
        assert!(!state_exceeds_limits);
        assert!(!bounce);

        assert_eq!(state.out_msgs.len(), 1);
        assert_eq!(state.end_lt, prev_end_lt + 1);
        let last_msg = state.out_msgs.last().unwrap();

        let msg_info = {
            let msg = last_msg.load()?;
            assert!(msg.init.is_none());
            assert_eq!(msg.body, Default::default());
            match msg.info {
                MsgInfo::Int(info) => info,
                e => panic!("unexpected msg info {e:?}"),
            }
        };
        assert_eq!(msg_info.src, STUB_ADDR.into());
        assert_eq!(msg_info.dst, STUB_ADDR.into());
        assert!(msg_info.ihr_disabled);
        assert!(!msg_info.bounce);
        assert!(!msg_info.bounced);
        assert_eq!(msg_info.created_at, params.block_unixtime);
        assert_eq!(msg_info.created_lt, prev_end_lt);

        let expected_fwd_fees = Tokens::new(config.fwd_prices.lump_price as _);
        let expected_first_frac = config.fwd_prices.get_first_part(expected_fwd_fees);

        assert_eq!(msg_info.value, (msg_value - expected_fwd_fees).into());
        assert_eq!(msg_info.fwd_fee, expected_fwd_fees - expected_first_frac);
        assert_eq!(msg_info.ihr_fee, Tokens::ZERO);

        assert_eq!(action_phase, ActionPhase {
            total_fwd_fees: Some(expected_fwd_fees),
            total_action_fees: Some(expected_first_frac),
            total_actions: 1,
            messages_created: 1,
            action_list_hash: *actions.repr_hash(),
            total_message_size: compute_full_stats(last_msg, &params),
            ..empty_action_phase()
        });

        assert_eq!(state.total_fees, prev_total_fees + expected_first_frac);
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(state.balance.tokens, prev_balance.tokens - msg_value);

        Ok(())
    }

    #[test]
    fn send_all_balance() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE);

        let compute_phase = stub_compute_phase(OK_GAS);
        let prev_total_fees = state.total_fees;
        let prev_balance = state.balance.clone();
        let prev_end_lt = state.end_lt;

        let actions = make_action_list([OutAction::SendMsg {
            mode: SendMsgFlags::ALL_BALANCE,
            out_msg: make_relaxed_message(
                RelaxedIntMsgInfo {
                    dst: STUB_ADDR.into(),
                    value: CurrencyCollection::ZERO,
                    ..Default::default()
                },
                None,
                None,
            ),
        }]);

        let ActionPhaseFull {
            action_phase,
            action_fine,
            state_exceeds_limits,
            bounce,
        } = state.action_phase(ActionPhaseContext {
            received_message: None,
            original_balance: original_balance(&state, &compute_phase),
            new_state: StateInit::default(),
            actions: actions.clone(),
            compute_phase: &compute_phase,
            inspector: None,
        })?;

        assert_eq!(action_fine, Tokens::ZERO);
        assert!(!state_exceeds_limits);
        assert!(!bounce);

        assert_eq!(state.out_msgs.len(), 1);
        assert_eq!(state.end_lt, prev_end_lt + 1);
        let last_msg = state.out_msgs.last().unwrap();

        let msg_info = {
            let msg = last_msg.load()?;
            assert!(msg.init.is_none());
            assert_eq!(msg.body, Default::default());
            match msg.info {
                MsgInfo::Int(info) => info,
                e => panic!("unexpected msg info {e:?}"),
            }
        };
        assert_eq!(msg_info.src, STUB_ADDR.into());
        assert_eq!(msg_info.dst, STUB_ADDR.into());
        assert!(msg_info.ihr_disabled);
        assert!(!msg_info.bounce);
        assert!(!msg_info.bounced);
        assert_eq!(msg_info.created_at, params.block_unixtime);
        assert_eq!(msg_info.created_lt, prev_end_lt);

        let expected_fwd_fees = Tokens::new(config.fwd_prices.lump_price as _);
        let expected_first_frac = config.fwd_prices.get_first_part(expected_fwd_fees);

        assert_eq!(
            msg_info.value,
            (prev_balance.tokens - expected_fwd_fees).into()
        );
        assert_eq!(msg_info.fwd_fee, expected_fwd_fees - expected_first_frac);
        assert_eq!(msg_info.ihr_fee, Tokens::ZERO);

        assert_eq!(action_phase, ActionPhase {
            total_fwd_fees: Some(expected_fwd_fees),
            total_action_fees: Some(expected_first_frac),
            total_actions: 1,
            messages_created: 1,
            action_list_hash: *actions.repr_hash(),
            total_message_size: compute_full_stats(last_msg, &params),
            ..empty_action_phase()
        });

        assert_eq!(state.total_fees, prev_total_fees + expected_first_frac);
        assert_eq!(state.balance, CurrencyCollection::ZERO);

        Ok(())
    }

    #[test]
    fn strict_send_all_balance() -> Result<()> {
        let mut params = make_default_params();
        params.strict_extra_currency = true;
        let config = make_default_config();

        let mut state =
            ExecutorState::new_uninit(&params, &config, &STUB_ADDR, CurrencyCollection {
                tokens: OK_BALANCE,
                other: BTreeMap::from_iter([(0u32, VarUint248::new(1000))]).try_into()?,
            });

        let compute_phase = stub_compute_phase(OK_GAS);
        let prev_total_fees = state.total_fees;
        let prev_balance = state.balance.clone();
        let prev_end_lt = state.end_lt;

        let sent_value = CurrencyCollection {
            tokens: Tokens::ZERO,
            other: BTreeMap::from_iter([(0u32, VarUint248::new(1))]).try_into()?,
        };

        let actions = make_action_list([OutAction::SendMsg {
            mode: SendMsgFlags::ALL_BALANCE,
            out_msg: make_relaxed_message(
                RelaxedIntMsgInfo {
                    dst: STUB_ADDR.into(),
                    value: sent_value.clone(),
                    ..Default::default()
                },
                None,
                None,
            ),
        }]);

        let ActionPhaseFull {
            action_phase,
            action_fine,
            state_exceeds_limits,
            bounce,
        } = state.action_phase(ActionPhaseContext {
            received_message: None,
            original_balance: original_balance(&state, &compute_phase),
            new_state: StateInit::default(),
            actions: actions.clone(),
            compute_phase: &compute_phase,
            inspector: None,
        })?;

        assert_eq!(action_fine, Tokens::ZERO);
        assert!(!state_exceeds_limits);
        assert!(!bounce);

        assert_eq!(state.out_msgs.len(), 1);
        assert_eq!(state.end_lt, prev_end_lt + 1);
        let last_msg = state.out_msgs.last().unwrap();

        let msg_info = {
            let msg = last_msg.load()?;
            assert!(msg.init.is_none());
            assert_eq!(msg.body, Default::default());
            match msg.info {
                MsgInfo::Int(info) => info,
                e => panic!("unexpected msg info {e:?}"),
            }
        };
        assert_eq!(msg_info.src, STUB_ADDR.into());
        assert_eq!(msg_info.dst, STUB_ADDR.into());
        assert!(msg_info.ihr_disabled);
        assert!(!msg_info.bounce);
        assert!(!msg_info.bounced);
        assert_eq!(msg_info.created_at, params.block_unixtime);
        assert_eq!(msg_info.created_lt, prev_end_lt);

        let expected_fwd_fees = Tokens::new(config.fwd_prices.lump_price as _);
        let expected_first_frac = config.fwd_prices.get_first_part(expected_fwd_fees);

        assert_eq!(msg_info.value, CurrencyCollection {
            tokens: prev_balance.tokens - expected_fwd_fees,
            other: sent_value.other.clone(),
        });
        assert_eq!(msg_info.fwd_fee, expected_fwd_fees - expected_first_frac);
        assert_eq!(msg_info.ihr_fee, Tokens::ZERO);

        assert_eq!(action_phase, ActionPhase {
            total_fwd_fees: Some(expected_fwd_fees),
            total_action_fees: Some(expected_first_frac),
            total_actions: 1,
            messages_created: 1,
            action_list_hash: *actions.repr_hash(),
            total_message_size: compute_full_stats(last_msg, &params),
            ..empty_action_phase()
        });

        assert_eq!(state.total_fees, prev_total_fees + expected_first_frac);
        assert_eq!(state.balance.tokens, Tokens::ZERO);
        assert_eq!(
            state.balance.other,
            prev_balance.other.checked_sub(&sent_value.other)?
        );

        Ok(())
    }

    #[test]
    fn strict_send_all_balance_destroy() -> Result<()> {
        struct TestCase {
            balance: CurrencyCollection,
            to_send: CurrencyCollection,
            expected_end_status: AccountStatus,
        }

        let mut params = make_default_params();
        params.strict_extra_currency = true;
        let config = make_default_config();

        for TestCase {
            balance,
            to_send,
            expected_end_status,
        } in [
            // Simple send all + delete
            TestCase {
                balance: OK_BALANCE.into(),
                to_send: CurrencyCollection::ZERO,
                expected_end_status: AccountStatus::NotExists,
            },
            // Simple send all but account has some extra currencies
            TestCase {
                balance: CurrencyCollection {
                    tokens: OK_BALANCE,
                    other: BTreeMap::from_iter([(0u32, VarUint248::new(1000))]).try_into()?,
                },
                to_send: CurrencyCollection::ZERO,
                expected_end_status: AccountStatus::Uninit,
            },
            // Simple send all but account has some extra currencies
            TestCase {
                balance: CurrencyCollection {
                    tokens: OK_BALANCE,
                    other: BTreeMap::from_iter([(0u32, VarUint248::new(1000))]).try_into()?,
                },
                to_send: CurrencyCollection::ZERO,
                expected_end_status: AccountStatus::Uninit,
            },
            // Send all native + some extra but account still has some more extra currencies
            TestCase {
                balance: CurrencyCollection {
                    tokens: OK_BALANCE,
                    other: BTreeMap::from_iter([(0u32, VarUint248::new(1000))]).try_into()?,
                },
                to_send: CurrencyCollection {
                    tokens: OK_BALANCE,
                    other: BTreeMap::from_iter([(0u32, VarUint248::new(1))]).try_into()?,
                },
                expected_end_status: AccountStatus::Uninit,
            },
            // Send all native and all extra
            TestCase {
                balance: CurrencyCollection {
                    tokens: OK_BALANCE,
                    other: BTreeMap::from_iter([(0u32, VarUint248::new(1000))]).try_into()?,
                },
                to_send: CurrencyCollection {
                    tokens: OK_BALANCE,
                    other: BTreeMap::from_iter([(0u32, VarUint248::new(1000))]).try_into()?,
                },
                expected_end_status: AccountStatus::NotExists,
            },
        ] {
            let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, balance);

            let compute_phase = stub_compute_phase(OK_GAS);
            let prev_total_fees = state.total_fees;
            let prev_balance = state.balance.clone();
            let prev_end_lt = state.end_lt;

            let actions = make_action_list([OutAction::SendMsg {
                mode: SendMsgFlags::ALL_BALANCE | SendMsgFlags::DELETE_IF_EMPTY,
                out_msg: make_relaxed_message(
                    RelaxedIntMsgInfo {
                        dst: STUB_ADDR.into(),
                        value: to_send.clone(),
                        ..Default::default()
                    },
                    None,
                    None,
                ),
            }]);

            let ActionPhaseFull {
                action_phase,
                action_fine,
                state_exceeds_limits,
                bounce,
            } = state.action_phase(ActionPhaseContext {
                received_message: None,
                original_balance: original_balance(&state, &compute_phase),
                new_state: StateInit::default(),
                actions: actions.clone(),
                compute_phase: &compute_phase,
                inspector: None,
            })?;

            assert_eq!(action_fine, Tokens::ZERO);
            assert!(!state_exceeds_limits);
            assert!(!bounce);

            assert_eq!(state.end_status, expected_end_status);
            assert_eq!(state.out_msgs.len(), 1);
            assert_eq!(state.end_lt, prev_end_lt + 1);
            let last_msg = state.out_msgs.last().unwrap();

            let msg_info = {
                let msg = last_msg.load()?;
                assert!(msg.init.is_none());
                assert_eq!(msg.body, Default::default());
                match msg.info {
                    MsgInfo::Int(info) => info,
                    e => panic!("unexpected msg info {e:?}"),
                }
            };
            assert_eq!(msg_info.src, STUB_ADDR.into());
            assert_eq!(msg_info.dst, STUB_ADDR.into());
            assert!(msg_info.ihr_disabled);
            assert!(!msg_info.bounce);
            assert!(!msg_info.bounced);
            assert_eq!(msg_info.created_at, params.block_unixtime);
            assert_eq!(msg_info.created_lt, prev_end_lt);

            let expected_fwd_fees = Tokens::new(config.fwd_prices.lump_price as _);
            let expected_first_frac = config.fwd_prices.get_first_part(expected_fwd_fees);

            assert_eq!(msg_info.value, CurrencyCollection {
                tokens: prev_balance.tokens - expected_fwd_fees,
                other: to_send.other.clone(),
            });
            assert_eq!(msg_info.fwd_fee, expected_fwd_fees - expected_first_frac);
            assert_eq!(msg_info.ihr_fee, Tokens::ZERO);

            assert_eq!(action_phase, ActionPhase {
                total_fwd_fees: Some(expected_fwd_fees),
                total_action_fees: Some(expected_first_frac),
                total_actions: 1,
                messages_created: 1,
                action_list_hash: *actions.repr_hash(),
                total_message_size: compute_full_stats(last_msg, &params),
                status_change: AccountStatusChange::Deleted,
                ..empty_action_phase()
            });

            assert_eq!(state.total_fees, prev_total_fees + expected_first_frac);
            assert_eq!(state.balance.tokens, Tokens::ZERO);
            assert_eq!(
                state.balance.other,
                prev_balance.other.checked_sub(&to_send.other)?
            );
        }

        Ok(())
    }

    #[test]
    fn send_all_not_reserved() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE);

        let compute_phase = stub_compute_phase(OK_GAS);
        let prev_total_fees = state.total_fees;
        let prev_end_lt = state.end_lt;

        let expected_balance = CurrencyCollection::from(state.balance.tokens / 4);
        let actions = make_action_list([
            OutAction::ReserveCurrency {
                mode: ReserveCurrencyFlags::empty(),
                value: expected_balance.clone(),
            },
            OutAction::SendMsg {
                mode: SendMsgFlags::ALL_BALANCE,
                out_msg: make_relaxed_message(
                    RelaxedIntMsgInfo {
                        dst: STUB_ADDR.into(),
                        value: CurrencyCollection::ZERO,
                        ..Default::default()
                    },
                    None,
                    None,
                ),
            },
        ]);

        let ActionPhaseFull {
            action_phase,
            action_fine,
            state_exceeds_limits,
            bounce,
        } = state.action_phase(ActionPhaseContext {
            received_message: None,
            original_balance: original_balance(&state, &compute_phase),
            new_state: StateInit::default(),
            actions: actions.clone(),
            compute_phase: &compute_phase,
            inspector: None,
        })?;

        assert_eq!(state.out_msgs.len(), 1);
        assert_eq!(state.end_lt, prev_end_lt + 1);
        let last_msg = state.out_msgs.last().unwrap();

        let msg_info = {
            let msg = last_msg.load()?;
            assert!(msg.init.is_none());
            assert_eq!(msg.body, Default::default());
            match msg.info {
                MsgInfo::Int(info) => info,
                e => panic!("unexpected msg info {e:?}"),
            }
        };
        assert_eq!(msg_info.src, STUB_ADDR.into());
        assert_eq!(msg_info.dst, STUB_ADDR.into());
        assert!(msg_info.ihr_disabled);
        assert!(!msg_info.bounce);
        assert!(!msg_info.bounced);
        assert_eq!(msg_info.created_at, params.block_unixtime);
        assert_eq!(msg_info.created_lt, prev_end_lt);

        let expected_fwd_fees = Tokens::new(config.fwd_prices.lump_price as _);
        let expected_first_frac = config.fwd_prices.get_first_part(expected_fwd_fees);

        assert_eq!(
            msg_info.value,
            (OK_BALANCE * 3 / 4 - expected_fwd_fees).into()
        );
        assert_eq!(msg_info.fwd_fee, expected_fwd_fees - expected_first_frac);
        assert_eq!(msg_info.ihr_fee, Tokens::ZERO);

        assert_eq!(action_phase, ActionPhase {
            total_fwd_fees: Some(expected_fwd_fees),
            total_action_fees: Some(expected_first_frac),
            total_actions: 2,
            messages_created: 1,
            special_actions: 1,
            action_list_hash: *actions.repr_hash(),
            total_message_size: compute_full_stats(last_msg, &params),
            ..empty_action_phase()
        });
        assert_eq!(action_fine, Tokens::ZERO);
        assert!(!state_exceeds_limits);
        assert!(!bounce);

        assert_eq!(state.total_fees, prev_total_fees + expected_first_frac);
        assert_eq!(state.balance, expected_balance);
        Ok(())
    }

    #[test]
    fn set_code() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();

        let orig_data = CellBuilder::build_from(u32::MIN)?;
        let final_data = CellBuilder::build_from(u32::MAX)?;

        let temp_code = Boc::decode(tvmasm!("NOP NOP"))?;
        let final_code = Boc::decode(tvmasm!("NOP"))?;

        let mut state = ExecutorState::new_active(
            &params,
            &config,
            &STUB_ADDR,
            OK_BALANCE,
            orig_data,
            tvmasm!("ACCEPT"),
        );

        let compute_phase = stub_compute_phase(OK_GAS);
        let prev_total_fees = state.total_fees;
        let prev_balance = state.balance.clone();

        let actions = make_action_list([
            OutAction::SetCode {
                new_code: temp_code,
            },
            OutAction::SetCode {
                new_code: final_code.clone(),
            },
        ]);

        let AccountState::Active(mut new_state) = state.state.clone() else {
            panic!("unexpected account state");
        };
        new_state.data = Some(final_data.clone());

        let ActionPhaseFull {
            action_phase,
            action_fine,
            state_exceeds_limits,
            bounce,
        } = state.action_phase(ActionPhaseContext {
            received_message: None,
            original_balance: original_balance(&state, &compute_phase),
            new_state,
            actions: actions.clone(),
            compute_phase: &compute_phase,
            inspector: None,
        })?;

        assert_eq!(action_phase, ActionPhase {
            total_actions: 2,
            special_actions: 2,
            action_list_hash: *actions.repr_hash(),
            ..empty_action_phase()
        });
        assert_eq!(action_fine, Tokens::ZERO);
        assert!(!state_exceeds_limits);
        assert!(!bounce);
        assert_eq!(state.end_status, AccountStatus::Active);
        assert_eq!(
            state.state,
            AccountState::Active(StateInit {
                code: Some(final_code),
                data: Some(final_data),
                ..Default::default()
            })
        );
        assert_eq!(state.total_fees, prev_total_fees);
        assert_eq!(state.balance, prev_balance);
        Ok(())
    }

    #[test]
    fn invalid_dst_addr() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();

        let targets = [
            // Unknown workchain.
            IntAddr::Std(StdAddr::new(123, HashBytes::ZERO)),
            // With anycast.
            IntAddr::Std({
                let mut addr = STUB_ADDR;
                let mut b = CellBuilder::new();
                b.store_u16(0xaabb)?;
                addr.anycast = Some(Box::new(Anycast::from_slice(&b.as_data_slice())?));
                addr
            }),
            // Var addr.
            IntAddr::Var(VarAddr {
                anycast: None,
                address_len: Uint9::new(80),
                workchain: 0,
                address: vec![0; 10],
            }),
        ];

        for dst in targets {
            let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE);

            let compute_phase = stub_compute_phase(OK_GAS);
            let prev_total_fees = state.total_fees;
            let prev_balance = state.balance.clone();
            let prev_end_lt = state.end_lt;

            let actions = make_action_list([OutAction::SendMsg {
                mode: SendMsgFlags::ALL_BALANCE,
                out_msg: make_relaxed_message(
                    RelaxedIntMsgInfo {
                        dst,
                        ..Default::default()
                    },
                    None,
                    None,
                ),
            }]);

            let ActionPhaseFull {
                action_phase,
                action_fine,
                state_exceeds_limits,
                bounce,
            } = state.action_phase(ActionPhaseContext {
                received_message: None,
                original_balance: original_balance(&state, &compute_phase),
                new_state: StateInit::default(),
                actions: actions.clone(),
                compute_phase: &compute_phase,
                inspector: None,
            })?;

            assert_eq!(action_phase, ActionPhase {
                success: false,
                total_actions: 1,
                messages_created: 0,
                result_code: ResultCode::InvalidDstAddr as _,
                result_arg: Some(0),
                action_list_hash: *actions.repr_hash(),
                ..empty_action_phase()
            });
            assert_eq!(action_fine, Tokens::ZERO);
            assert!(!state_exceeds_limits);
            assert!(!bounce);

            assert!(state.out_msgs.is_empty());
            assert_eq!(state.end_lt, prev_end_lt);

            assert_eq!(state.total_fees, prev_total_fees);
            assert_eq!(state.balance, prev_balance);
        }
        Ok(())
    }

    #[test]
    fn cant_pay_fwd_fee() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, Tokens::new(50000));

        let compute_phase = stub_compute_phase(OK_GAS);
        let prev_balance = state.balance.clone();
        let prev_total_fee = state.total_fees;
        let prev_end_lt = state.end_lt;

        let actions = make_action_list([OutAction::SendMsg {
            mode: SendMsgFlags::PAY_FEE_SEPARATELY,
            out_msg: make_relaxed_message(
                RelaxedIntMsgInfo {
                    value: CurrencyCollection::ZERO,
                    dst: STUB_ADDR.into(),
                    ..Default::default()
                },
                None,
                Some({
                    let mut b = CellBuilder::new();
                    b.store_reference(Cell::empty_cell())?;
                    b.store_reference(CellBuilder::build_from(0xdeafbeafu32)?)?;
                    b
                }),
            ),
        }]);

        let ActionPhaseFull {
            action_phase,
            action_fine,
            state_exceeds_limits,
            bounce,
        } = state.action_phase(ActionPhaseContext {
            received_message: None,
            original_balance: original_balance(&state, &compute_phase),
            new_state: StateInit::default(),
            actions: actions.clone(),
            compute_phase: &compute_phase,
            inspector: None,
        })?;

        assert_eq!(action_phase, ActionPhase {
            success: false,
            no_funds: true,
            result_code: ResultCode::NotEnoughBalance as _,
            result_arg: Some(0),
            total_actions: 1,
            total_action_fees: Some(prev_balance.tokens),
            action_list_hash: *actions.repr_hash(),
            ..empty_action_phase()
        });
        assert_eq!(action_fine, prev_balance.tokens);
        assert!(!state_exceeds_limits);
        assert!(!bounce);

        assert_eq!(state.balance, CurrencyCollection::ZERO);
        assert_eq!(
            state.total_fees,
            prev_total_fee + action_phase.total_action_fees.unwrap_or_default()
        );
        assert!(state.out_msgs.is_empty());
        assert_eq!(state.end_lt, prev_end_lt);
        Ok(())
    }

    #[test]
    fn rewrite_message() -> Result<()> {
        let params = make_default_params();
        let config = make_default_config();
        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, OK_BALANCE);

        let compute_phase = stub_compute_phase(OK_GAS);
        let prev_balance = state.balance.clone();
        let prev_total_fee = state.total_fees;
        let prev_end_lt = state.end_lt;

        let msg_body = {
            let mut b = CellBuilder::new();
            b.store_zeros(600)?;
            b.store_reference(Cell::empty_cell())?;
            b
        };

        let actions = make_action_list([OutAction::SendMsg {
            mode: SendMsgFlags::PAY_FEE_SEPARATELY,
            out_msg: make_relaxed_message(
                RelaxedIntMsgInfo {
                    value: CurrencyCollection::ZERO,
                    dst: STUB_ADDR.into(),
                    ..Default::default()
                },
                None,
                Some(msg_body.clone()),
            ),
        }]);

        let ActionPhaseFull {
            action_phase,
            action_fine,
            state_exceeds_limits,
            bounce,
        } = state.action_phase(ActionPhaseContext {
            received_message: None,
            original_balance: original_balance(&state, &compute_phase),
            new_state: StateInit::default(),
            actions: actions.clone(),
            compute_phase: &compute_phase,
            inspector: None,
        })?;

        assert_eq!(state.out_msgs.len(), 1);
        let last_msg = state.out_msgs.last().unwrap();
        let msg = last_msg.load()?;
        assert_eq!(
            msg.layout,
            Some(MessageLayout {
                init_to_cell: false,
                body_to_cell: true,
            })
        );
        assert_eq!(msg.body.1, msg_body.build()?);

        let MsgInfo::Int(info) = msg.info else {
            panic!("expected an internal message");
        };

        let expected_fwd_fees = config.fwd_prices.compute_fwd_fee(CellTreeStats {
            bit_count: 600,
            cell_count: 2,
        });
        let first_frac = config.fwd_prices.get_first_part(expected_fwd_fees);

        assert_eq!(action_phase, ActionPhase {
            total_actions: 1,
            messages_created: 1,
            total_fwd_fees: Some(expected_fwd_fees),
            total_action_fees: Some(first_frac),
            action_list_hash: *actions.repr_hash(),
            total_message_size: compute_full_stats(last_msg, &params),
            ..empty_action_phase()
        });
        assert_eq!(action_fine, Tokens::ZERO);
        assert!(!state_exceeds_limits);
        assert!(!bounce);

        assert_eq!(state.end_lt, prev_end_lt + 1);
        assert_eq!(
            state.total_fees,
            prev_total_fee + action_phase.total_action_fees.unwrap_or_default()
        );
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(
            state.balance.tokens,
            prev_balance.tokens - info.value.tokens - expected_fwd_fees
        );
        Ok(())
    }

    #[test]
    fn change_lib() -> Result<()> {
        struct TestCase {
            libraries: Dict<HashBytes, SimpleLib>,
            target: Dict<HashBytes, SimpleLib>,
            changes: Vec<(ChangeLibraryMode, LibRef)>,
            diff: Vec<PublicLibraryChange>,
        }

        fn make_lib(id: u32) -> Cell {
            CellBuilder::build_from(id).unwrap()
        }

        fn make_lib_hash(id: u32) -> HashBytes {
            *CellBuilder::build_from(id).unwrap().repr_hash()
        }

        fn make_libs<I>(items: I) -> Dict<HashBytes, SimpleLib>
        where
            I: IntoIterator<Item = (u32, bool)>,
        {
            let mut items = items
                .into_iter()
                .map(|(id, public)| {
                    let root = make_lib(id);
                    (*root.repr_hash(), SimpleLib { root, public })
                })
                .collect::<Vec<_>>();
            items.sort_by(|(a, _), (b, _)| a.cmp(b));
            Dict::try_from_sorted_slice(&items).unwrap()
        }

        let params = make_default_params();
        let config = make_default_config();

        let test_cases = vec![
            // The simplest case with no libs.
            TestCase {
                libraries: Dict::new(),
                target: Dict::new(),
                changes: Vec::new(),
                diff: Vec::new(),
            },
            // Add private libs.
            TestCase {
                libraries: Dict::new(),
                target: make_libs([(123, false)]),
                changes: vec![(ChangeLibraryMode::ADD_PRIVATE, LibRef::Cell(make_lib(123)))],
                diff: Vec::new(),
            },
            TestCase {
                libraries: Dict::new(),
                target: make_libs([(123, false), (234, false)]),
                changes: vec![
                    (ChangeLibraryMode::ADD_PRIVATE, LibRef::Cell(make_lib(123))),
                    (ChangeLibraryMode::ADD_PRIVATE, LibRef::Cell(make_lib(234))),
                ],
                diff: Vec::new(),
            },
            TestCase {
                libraries: make_libs([(123, false)]),
                target: make_libs([(123, false)]),
                changes: vec![(ChangeLibraryMode::ADD_PRIVATE, LibRef::Cell(make_lib(123)))],
                diff: Vec::new(),
            },
            TestCase {
                libraries: make_libs([(123, false)]),
                target: make_libs([(123, false)]),
                changes: vec![(
                    ChangeLibraryMode::ADD_PRIVATE,
                    LibRef::Hash(make_lib_hash(123)),
                )],
                diff: Vec::new(),
            },
            // Add public libs.
            TestCase {
                libraries: Dict::new(),
                target: make_libs([(123, true)]),
                changes: vec![(ChangeLibraryMode::ADD_PUBLIC, LibRef::Cell(make_lib(123)))],
                diff: vec![PublicLibraryChange::Add(make_lib(123))],
            },
            TestCase {
                libraries: Dict::new(),
                target: make_libs([(123, true), (234, true)]),
                changes: vec![
                    (ChangeLibraryMode::ADD_PUBLIC, LibRef::Cell(make_lib(123))),
                    (ChangeLibraryMode::ADD_PUBLIC, LibRef::Cell(make_lib(234))),
                ],
                diff: vec![
                    PublicLibraryChange::Add(make_lib(123)),
                    PublicLibraryChange::Add(make_lib(234)),
                ],
            },
            TestCase {
                libraries: make_libs([(123, true)]),
                target: make_libs([(123, true)]),
                changes: vec![(ChangeLibraryMode::ADD_PUBLIC, LibRef::Cell(make_lib(123)))],
                diff: Vec::new(),
            },
            TestCase {
                libraries: make_libs([(123, true)]),
                target: make_libs([(123, true)]),
                changes: vec![(
                    ChangeLibraryMode::ADD_PUBLIC,
                    LibRef::Hash(make_lib_hash(123)),
                )],
                diff: Vec::new(),
            },
            // Remove public libs.
            TestCase {
                libraries: Dict::new(),
                target: Dict::new(),
                // Non-existing by cell.
                changes: vec![(ChangeLibraryMode::REMOVE, LibRef::Cell(make_lib(123)))],
                diff: Vec::new(),
            },
            TestCase {
                libraries: Dict::new(),
                target: Dict::new(),
                // Non-existing by hash.
                changes: vec![(ChangeLibraryMode::REMOVE, LibRef::Hash(make_lib_hash(123)))],
                diff: Vec::new(),
            },
            TestCase {
                libraries: make_libs([(123, false)]),
                target: Dict::new(),
                changes: vec![(ChangeLibraryMode::REMOVE, LibRef::Cell(make_lib(123)))],
                diff: Vec::new(),
            },
            TestCase {
                libraries: make_libs([(123, false)]),
                target: Dict::new(),
                changes: vec![(ChangeLibraryMode::REMOVE, LibRef::Hash(make_lib_hash(123)))],
                diff: Vec::new(),
            },
            TestCase {
                libraries: make_libs([(123, true)]),
                target: Dict::new(),
                changes: vec![(ChangeLibraryMode::REMOVE, LibRef::Cell(make_lib(123)))],
                diff: vec![PublicLibraryChange::Remove(make_lib_hash(123))],
            },
            // Update public libs.
            TestCase {
                libraries: make_libs([(123, false)]),
                target: make_libs([(123, true)]),
                changes: vec![(ChangeLibraryMode::ADD_PUBLIC, LibRef::Cell(make_lib(123)))],
                diff: vec![PublicLibraryChange::Add(make_lib(123))],
            },
            TestCase {
                libraries: make_libs([(123, false)]),
                target: make_libs([(123, true)]),
                changes: vec![(
                    ChangeLibraryMode::ADD_PUBLIC,
                    LibRef::Hash(make_lib_hash(123)),
                )],
                diff: vec![PublicLibraryChange::Add(make_lib(123))],
            },
            TestCase {
                libraries: make_libs([(123, true)]),
                target: make_libs([(123, false)]),
                changes: vec![(ChangeLibraryMode::ADD_PRIVATE, LibRef::Cell(make_lib(123)))],
                diff: vec![PublicLibraryChange::Remove(make_lib_hash(123))],
            },
            TestCase {
                libraries: make_libs([(123, true)]),
                target: make_libs([(123, false)]),
                changes: vec![(
                    ChangeLibraryMode::ADD_PRIVATE,
                    LibRef::Hash(make_lib_hash(123)),
                )],
                diff: vec![PublicLibraryChange::Remove(make_lib_hash(123))],
            },
        ];

        for TestCase {
            libraries,
            target,
            changes,
            diff,
        } in test_cases
        {
            let mut state = ExecutorState::new_active(
                &params,
                &config,
                &StdAddr::new(-1, HashBytes::ZERO),
                OK_BALANCE,
                Cell::empty_cell(),
                tvmasm!("ACCEPT"),
            );

            let target_state_init = match &mut state.state {
                AccountState::Active(state_init) => {
                    state_init.libraries = libraries;
                    StateInit {
                        libraries: target,
                        ..state_init.clone()
                    }
                }
                AccountState::Uninit | AccountState::Frozen(..) => panic!("invalid initial state"),
            };

            let compute_phase = stub_compute_phase(OK_GAS);
            let prev_total_fees = state.total_fees;
            let prev_balance = state.balance.clone();

            let change_count = changes.len();
            let actions = make_action_list(
                changes
                    .into_iter()
                    .map(|(mode, lib)| OutAction::ChangeLibrary { mode, lib }),
            );

            let mut inspector = ExecutorInspector::default();

            let ActionPhaseFull {
                action_phase,
                action_fine,
                state_exceeds_limits,
                bounce,
            } = state.action_phase(ActionPhaseContext {
                received_message: None,
                original_balance: original_balance(&state, &compute_phase),
                new_state: match state.state.clone() {
                    AccountState::Active(state_init) => state_init,
                    AccountState::Uninit | AccountState::Frozen(..) => Default::default(),
                },
                actions: actions.clone(),
                compute_phase: &compute_phase,
                inspector: Some(&mut inspector),
            })?;

            assert_eq!(action_phase, ActionPhase {
                total_actions: change_count as u16,
                special_actions: change_count as u16,
                action_list_hash: *actions.repr_hash(),
                ..empty_action_phase()
            });
            assert_eq!(action_fine, Tokens::ZERO);
            assert!(!state_exceeds_limits);
            assert!(!bounce);
            assert_eq!(state.end_status, AccountStatus::Active);
            assert_eq!(state.state, AccountState::Active(target_state_init));
            assert_eq!(state.total_fees, prev_total_fees);
            assert_eq!(state.balance, prev_balance);
            assert_eq!(inspector.public_libs_diff, diff);
        }
        Ok(())
    }
}
