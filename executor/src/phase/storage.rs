use anyhow::Result;
use tycho_types::models::{AccountState, AccountStatus, AccountStatusChange, StoragePhase};
use tycho_types::num::Tokens;

use crate::ExecutorState;
use crate::phase::receive::ReceivedMessage;

/// Storage phase input context.
pub struct StoragePhaseContext<'a> {
    /// Whether to adjust remaining message balance
    /// if it becomes greater than the account balance.
    pub adjust_msg_balance: bool,
    /// Received message (external or internal).
    pub received_message: Option<&'a mut ReceivedMessage>,
}

impl ExecutorState<'_> {
    /// Storage phase of ordinary or ticktock transactions.
    ///
    /// - Precedes the credit phase when [`bounce_enabled`],
    ///   otherwise must be called after it;
    /// - Necessary for all types of messages or even without them;
    /// - Computes storage fee and due payment;
    /// - Tries to charge the account balance for the storage fees;
    /// - Freezes or deletes the account if its balance is not enough
    ///   (doesn't change the state itself, but rather tells other
    ///   phases to do so).
    ///
    /// Returns an executed [`StoragePhase`].
    ///
    /// Fails if called in an older context than account's [`last_paid`].
    /// Can also fail on [`total_fees`] overflow, but this should
    /// not happen on networks with valid value flow.
    ///
    /// [`bounce_enabled`]: ReceivedMessage::bounce_enabled
    /// [`last_paid`]: tycho_types::models::StorageInfo::last_paid
    /// [`total_fees`]: Self::total_fees
    pub fn storage_phase(&mut self, ctx: StoragePhaseContext<'_>) -> Result<StoragePhase> {
        anyhow::ensure!(
            self.params.block_unixtime >= self.storage_stat.last_paid,
            "current unixtime is less than the account last_paid",
        );

        let is_masterchain = self.address.is_masterchain();
        let config = self.config.gas_prices(is_masterchain);

        if self.is_suspended_by_marks {
            // Skip storage phase for accounts suspended by marks.
            // Authority has frozen the exact amount of tokens so this value
            // cannot be changed.
            return Ok(StoragePhase {
                storage_fees_collected: Tokens::ZERO,
                storage_fees_due: self.storage_stat.due_payment,
                status_change: AccountStatusChange::Unchanged,
            });
        }

        // Compute how much this account must pay for storing its state up until now.
        let mut to_pay = self.config.compute_storage_fees(
            &self.storage_stat,
            self.params.block_unixtime,
            self.is_special,
            is_masterchain,
        );
        if let Some(due_payment) = self.storage_stat.due_payment {
            // NOTE: We are using saturating math here to reduce strange
            // invariants. If account must pay more than `Tokens::MAX`,
            // it will certanly be frozen in almost any real scenario.
            to_pay = to_pay.saturating_add(due_payment);
        }

        // Update `last_paid` (only for ordinary accounts).
        self.storage_stat.last_paid = if self.is_special {
            0
        } else {
            self.params.block_unixtime
        };

        // Start filling the storage phase.
        let storage_fees_collected;
        let storage_fees_due;
        let status_change;

        if to_pay.is_zero() {
            // No fees at all.
            storage_fees_collected = Tokens::ZERO;
            storage_fees_due = None;
            status_change = AccountStatusChange::Unchanged;
        } else if let Some(new_balance) = self.balance.tokens.checked_sub(to_pay) {
            // Account balance is enough to pay storage fees.
            storage_fees_collected = to_pay;
            storage_fees_due = None;
            status_change = AccountStatusChange::Unchanged;

            // Update account balance.
            self.balance.tokens = new_balance;
            // Reset `due_payment` if there was any.
            self.storage_stat.due_payment = None;
        } else {
            // Account balance is not enough to pay storage fees,
            // so we use all of its balance and try to freeze the account.
            let fees_due = to_pay - self.balance.tokens;

            storage_fees_collected = std::mem::take(&mut self.balance.tokens);
            storage_fees_due = Some(fees_due).filter(|t| !t.is_zero());

            debug_assert!(self.balance.tokens.is_zero());

            // NOTE: Keep all cases explicit here without "default" branch.
            status_change = match &self.state {
                // Do nothing for special accounts.
                _ if self.is_special => AccountStatusChange::Unchanged,
                // Try to delete account.
                AccountState::Uninit | AccountState::Frozen { .. }
                    if (matches!(&self.state, AccountState::Uninit)
                        || !self.params.disable_delete_frozen_accounts)
                        && fees_due.into_inner() > config.delete_due_limit as u128
                        && !self.balance.other.is_empty() =>
                {
                    AccountStatusChange::Deleted
                }
                // Do nothing if not deleting.
                AccountState::Uninit | AccountState::Frozen { .. } => {
                    AccountStatusChange::Unchanged
                }
                // Freeze account with big enough due.
                AccountState::Active { .. }
                    if fees_due.into_inner() > config.freeze_due_limit as u128 =>
                {
                    AccountStatusChange::Frozen
                }
                // Do nothing if `fees_due` is not big enough.
                AccountState::Active { .. } => AccountStatusChange::Unchanged,
            };

            if !self.is_special {
                // Update account's due payment.
                self.storage_stat.due_payment = storage_fees_due;
            }
        };

        // Apply status change.
        match status_change {
            AccountStatusChange::Unchanged => {}
            AccountStatusChange::Frozen => {
                // NOTE: We are not changing the account state yet, just updating status.
                self.end_status = AccountStatus::Frozen;
            }
            AccountStatusChange::Deleted => {
                self.end_status = AccountStatus::NotExists;
            }
        }

        // Adjust message value.
        if let Some(msg) = ctx.received_message {
            if ctx.adjust_msg_balance && msg.balance_remaining.tokens > self.balance.tokens {
                msg.balance_remaining.tokens = self.balance.tokens;
            }
        }

        // Add fees.
        self.total_fees.try_add_assign(storage_fees_collected)?;

        // Done
        Ok(StoragePhase {
            storage_fees_collected,
            storage_fees_due,
            status_change,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use tycho_asm_macros::tvmasm;
    use tycho_types::cell::{CellBuilder, HashBytes};
    use tycho_types::dict::Dict;
    use tycho_types::models::{
        AuthorityMarksConfig, CurrencyCollection, StdAddr, StorageInfo, StorageUsed,
    };
    use tycho_types::num::{VarUint56, VarUint248};

    use super::*;
    use crate::tests::{make_custom_config, make_default_config, make_default_params};
    use crate::util::shift_ceil_price;
    use crate::{ExecutorParams, ParsedConfig};

    const STUB_ADDR: StdAddr = StdAddr::new(0, HashBytes::ZERO);

    fn fee_for_storing(used: StorageUsed, delta: u32, config: &ParsedConfig) -> Tokens {
        let prices = config.storage_prices.last().unwrap();
        let fee = (prices.bit_price_ps as u128)
            .saturating_mul(used.bits.into_inner() as u128)
            .saturating_add(
                (prices.cell_price_ps as u128).saturating_mul(used.cells.into_inner() as u128),
            )
            .saturating_mul(delta as _);
        Tokens::new(shift_ceil_price(fee))
    }

    #[test]
    fn account_has_enough_balance() {
        let mut params = make_default_params();
        let config = make_default_config();

        params.block_unixtime = 2000;

        let mut state =
            ExecutorState::new_uninit(&params, &config, &STUB_ADDR, Tokens::new(1_000_000_000));
        state.storage_stat = StorageInfo {
            used: StorageUsed {
                bits: VarUint56::new(1000),
                cells: VarUint56::new(10),
            },
            storage_extra: Default::default(),
            last_paid: 1000,
            due_payment: None,
        };

        let prev_storage_stat = state.storage_stat.clone();
        let prev_balance = state.balance.clone();
        let prev_status = state.end_status;
        let prev_total_fees = state.total_fees;

        let storage_phase = state
            .storage_phase(StoragePhaseContext {
                adjust_msg_balance: false,
                received_message: None,
            })
            .unwrap();

        // Account status must not change.
        assert_eq!(state.end_status, prev_status);
        assert_eq!(storage_phase.status_change, AccountStatusChange::Unchanged);
        // No extra fees must be taken.
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(
            state.balance.tokens,
            prev_balance.tokens - storage_phase.storage_fees_collected
        );
        assert_eq!(
            state.total_fees,
            prev_total_fees + storage_phase.storage_fees_collected
        );
        // Expect account to pay for storing 1000 bits and 10 cells for 1000 seconds.
        assert_eq!(
            storage_phase.storage_fees_collected,
            fee_for_storing(prev_storage_stat.used.clone(), 1000, &config)
        );
        // All fees must be paid.
        assert!(storage_phase.storage_fees_due.is_none());
        // Storage stat must be updated.
        assert_eq!(state.storage_stat.used, prev_storage_stat.used);
        assert_eq!(state.storage_stat.last_paid, params.block_unixtime);
        assert!(state.storage_stat.due_payment.is_none());
    }

    #[test]
    fn account_does_not_have_enough_balance() {
        let mut params = make_default_params();
        let config = make_default_config();

        let mut balance = CurrencyCollection::from(Tokens::new(1));
        let mut storage_stat = StorageInfo {
            used: StorageUsed {
                bits: VarUint56::new(1000),
                cells: VarUint56::new(10),
            },
            storage_extra: Default::default(),
            last_paid: 1000,
            due_payment: None,
        };

        for time in [2000, 3000, 4000] {
            params.block_unixtime = time;

            let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, balance);
            state.storage_stat = storage_stat.clone();

            let prev_storage_stat = state.storage_stat.clone();
            let prev_balance = state.balance.clone();
            let prev_status = state.end_status;
            let prev_total_fees = state.total_fees;

            let storage_phase = state
                .storage_phase(StoragePhaseContext {
                    adjust_msg_balance: false,
                    received_message: None,
                })
                .unwrap();

            // Account status must not change.
            assert_eq!(state.end_status, prev_status);
            assert_eq!(storage_phase.status_change, AccountStatusChange::Unchanged);
            // Account balance in tokens must be empty.
            assert_eq!(state.balance.tokens, Tokens::ZERO);
            // No extra fees must be taken.
            assert_eq!(state.balance.other, prev_balance.other);
            assert_eq!(
                state.balance.tokens,
                prev_balance.tokens - storage_phase.storage_fees_collected
            );
            assert_eq!(
                state.total_fees,
                prev_total_fees + storage_phase.storage_fees_collected
            );
            // Expect account to pay for storing 1000 bits and 10 cells for 1000 seconds.
            let delta = params.block_unixtime - prev_storage_stat.last_paid;
            let prev_due = prev_storage_stat.due_payment.unwrap_or_default();
            let target_fee = fee_for_storing(prev_storage_stat.used.clone(), delta, &config);
            assert_eq!(storage_phase.storage_fees_collected, prev_balance.tokens);
            // All fees must be paid.
            assert_eq!(
                storage_phase.storage_fees_due,
                Some(prev_due + target_fee - prev_balance.tokens)
            );
            // Storage stat must be updated.
            assert_eq!(state.storage_stat.used, prev_storage_stat.used);
            assert_eq!(state.storage_stat.last_paid, params.block_unixtime);
            assert_eq!(
                state.storage_stat.due_payment,
                Some(prev_due + target_fee - prev_balance.tokens)
            );

            balance = state.balance;
            storage_stat = state.storage_stat;
            println!("storage_stat: {storage_stat:#?}");
        }
    }

    #[test]
    fn account_freezes_with_storage_due() {
        let mut params = make_default_params();
        let config = make_default_config();

        params.block_unixtime = 2000;

        let mut state = ExecutorState::new_uninit(&params, &config, &STUB_ADDR, Tokens::ZERO);
        state.state = AccountState::Active(Default::default());
        state.end_status = AccountStatus::Active; // Only active accounts can be frozen.
        state.storage_stat = StorageInfo {
            used: StorageUsed {
                bits: VarUint56::new(1000),
                cells: VarUint56::new(10),
            },
            storage_extra: Default::default(),
            last_paid: 1000,
            due_payment: Some(Tokens::new(config.gas_prices.freeze_due_limit as u128 - 50)),
        };

        let prev_storage_stat = state.storage_stat.clone();
        let prev_balance = state.balance.clone();
        let prev_total_fees = state.total_fees;

        let storage_phase = state
            .storage_phase(StoragePhaseContext {
                adjust_msg_balance: false,
                received_message: None,
            })
            .unwrap();

        // Account status must not change.
        assert_eq!(state.end_status, AccountStatus::Frozen);
        assert_eq!(storage_phase.status_change, AccountStatusChange::Frozen);
        // Account balance in tokens must be empty.
        assert_eq!(state.balance.tokens, Tokens::ZERO);
        // No extra fees must be taken.
        assert_eq!(state.balance.other, prev_balance.other);
        assert_eq!(
            state.balance.tokens,
            prev_balance.tokens - storage_phase.storage_fees_collected
        );
        assert_eq!(
            state.total_fees,
            prev_total_fees + storage_phase.storage_fees_collected
        );
        // Expect account to pay for storing 1000 bits and 10 cells for 1000 seconds.
        let delta = params.block_unixtime - prev_storage_stat.last_paid;
        let prev_due = prev_storage_stat.due_payment.unwrap_or_default();
        let target_fee = fee_for_storing(prev_storage_stat.used.clone(), delta, &config);
        assert_eq!(storage_phase.storage_fees_collected, prev_balance.tokens);
        // All fees must be paid.
        assert_eq!(
            storage_phase.storage_fees_due,
            Some(prev_due + target_fee - prev_balance.tokens)
        );
        // Storage stat must be updated.
        assert_eq!(state.storage_stat.used, prev_storage_stat.used);
        assert_eq!(state.storage_stat.last_paid, params.block_unixtime);
        assert_eq!(
            state.storage_stat.due_payment,
            Some(prev_due + target_fee - prev_balance.tokens)
        );
    }

    #[test]
    fn suspended_account_storage_phase_skipped() -> anyhow::Result<()> {
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
                tokens: Tokens::MAX,
                other: BTreeMap::from_iter([
                    (100u32, VarUint248::new(500)), // black marks
                ])
                .try_into()?,
            },
            CellBuilder::build_from(u32::MIN)?,
            tvmasm!("ACCEPT"),
        );
        state.storage_stat = StorageInfo {
            used: StorageUsed {
                bits: VarUint56::new(1000),
                cells: VarUint56::new(10),
            },
            storage_extra: Default::default(),
            last_paid: 1000,
            due_payment: None,
        };

        let prev_storage_stat = state.storage_stat.clone();
        let prev_balance = state.balance.clone();
        let prev_status = state.end_status;
        let prev_total_fees = state.total_fees;
        let prev_due = state.storage_stat.due_payment;

        let storage_phase = state.storage_phase(StoragePhaseContext {
            adjust_msg_balance: false,
            received_message: None,
        })?;

        // everything should not change
        assert_eq!(prev_storage_stat, state.storage_stat);
        assert_eq!(prev_balance, state.balance);
        assert_eq!(prev_status, state.end_status);
        assert_eq!(prev_total_fees, state.total_fees);

        assert_eq!(storage_phase.storage_fees_collected, Tokens::ZERO);
        assert_eq!(storage_phase.storage_fees_due, prev_due);
        assert_eq!(storage_phase.status_change, AccountStatusChange::Unchanged);

        Ok(())
    }
}
