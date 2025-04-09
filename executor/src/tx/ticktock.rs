use anyhow::Context;
use everscale_types::models::{AccountStatus, ComputePhase, TickTock, TickTockTxInfo};

use crate::error::{TxError, TxResult};
use crate::phase::{
    ActionPhaseContext, ComputePhaseContext, ComputePhaseFull, StoragePhaseContext,
    TransactionInput,
};
use crate::{ExecutorInspector, ExecutorState};

impl ExecutorState<'_> {
    pub fn run_tick_tock_transaction(
        &mut self,
        kind: TickTock,
        inspector: Option<&mut ExecutorInspector<'_>>,
    ) -> TxResult<TickTockTxInfo> {
        if self.state.status() != AccountStatus::Active {
            // Skip ticktock transactions for inactive accounts.
            return Err(TxError::Skipped);
        }

        // Run storage phase.
        let storage_phase = self
            .storage_phase(StoragePhaseContext {
                adjust_msg_balance: false,
                received_message: None,
            })
            .context("storage phase failed")?;

        // Run compute phase.
        let ComputePhaseFull {
            compute_phase,
            original_balance,
            new_state,
            actions,
            ..
        } = self
            .compute_phase(ComputePhaseContext {
                input: TransactionInput::TickTock(kind),
                storage_fee: storage_phase.storage_fees_collected,
                force_accept: false,
                inspector,
            })
            .context("compute phase failed")?;

        // Run action phase only if compute phase succeeded.
        let mut aborted = true;
        let mut destroyed = false;
        let mut action_phase = None;
        if let ComputePhase::Executed(compute_phase) = &compute_phase {
            if compute_phase.success {
                let res = self
                    .action_phase(ActionPhaseContext {
                        received_message: None,
                        original_balance,
                        new_state,
                        actions,
                        compute_phase,
                    })
                    .context("action phase failed")?;

                aborted = !res.action_phase.success;
                destroyed = self.end_status == AccountStatus::NotExists;
                action_phase = Some(res.action_phase);
            }
        }

        // Build transaction info.
        Ok(TickTockTxInfo {
            kind,
            storage_phase,
            compute_phase,
            action_phase,
            aborted,
            destroyed,
        })
    }
}
