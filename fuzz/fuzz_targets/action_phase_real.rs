#![no_main]

use std::rc::Rc;

use arbitrary::{Arbitrary, Result, Unstructured};
use everscale_types::arbitrary::SimpleBalance;
use everscale_types::boc::{Boc, BocRepr};
use everscale_types::cell::{Cell, CellBuilder, CellFamily, HashBytes};
use everscale_types::models::{
    AccountState, AccountStatus, BlockchainConfig, CurrencyCollection, ExecutedComputePhase,
    MsgInfo, OutAction, SizeLimitsConfig, StdAddr,
};
use everscale_types::num::Tokens;
use libfuzzer_sys::fuzz_target;
use tycho_executor::phase::{ActionPhaseContext, ActionPhaseFull, ReceivedMessage};
use tycho_executor::{ExecutorParams, ExecutorState, ParsedConfig};

fuzz_target!(|input: Input| {
    let params = make_default_params();
    let config = make_default_config();

    // Prepare input.
    let mut balance: CurrencyCollection = input.balance.into();
    let gas_fees: Tokens = input.gas_fees.into();
    let mut msg: Option<ReceivedMessage> = input.message.map(Into::into);

    let mut original_balance = balance.clone();
    original_balance.try_add_assign_tokens(gas_fees).unwrap();

    let mut received_amount = CurrencyCollection::ZERO;
    if let Some(msg) = &msg {
        received_amount = msg.balance_remaining.clone();
        balance.try_add_assign(&msg.balance_remaining).unwrap();
    }

    // Create state.
    let mut state = ExecutorState {
        params: &params,
        config: config.as_ref(),
        is_special: false,
        address: StdAddr::new(if input.is_masterchain { -1 } else { 0 }, HashBytes::ZERO),
        storage_stat: Default::default(),
        balance,
        state: AccountState::Uninit,
        orig_status: AccountStatus::NotExists,
        end_status: AccountStatus::Uninit,
        start_lt: 0,
        end_lt: 1,
        out_msgs: Vec::new(),
        total_fees: gas_fees,
        cached_storage_stat: None,
    };

    // Run transaction part.
    let compute_phase = stub_compute_phase(gas_fees);

    let ActionPhaseFull {
        action_phase,
        action_fine,
        state_exceeds_limits,
        bounce,
    } = state
        .action_phase(ActionPhaseContext {
            received_message: msg.as_mut(),
            original_balance: original_balance.clone(),
            new_state: Default::default(),
            actions: input.actions.into(),
            compute_phase: &compute_phase,
        })
        .unwrap();

    // Validate balance change.
    assert!(action_phase.success || state.out_msgs.is_empty());

    let mut spent_amount = CurrencyCollection::from(gas_fees);
    spent_amount
        .try_add_assign_tokens(action_phase.total_action_fees.unwrap_or_default())
        .unwrap();

    for out_msg in &state.out_msgs {
        let msg = out_msg.load().unwrap();
        if let MsgInfo::Int(info) = msg.info {
            spent_amount.try_add_assign(&info.value).unwrap();
            spent_amount.try_add_assign_tokens(info.fwd_fee).unwrap();
        }
    }

    let mut expected_balance = original_balance;
    expected_balance.try_add_assign(&received_amount).unwrap();
    expected_balance.try_sub_assign(&spent_amount).unwrap();
    assert_eq!(state.balance, expected_balance);
});

#[derive(Debug, Arbitrary)]
struct Input {
    is_masterchain: bool,
    message: Option<MessageInput>,
    gas_fees: GasFees,
    balance: SimpleBalance,
    actions: OutActions,
}

struct OutActions(Cell);

impl std::fmt::Debug for OutActions {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&Boc::encode(self.0.as_ref()), f)
    }
}

impl From<OutActions> for Cell {
    #[inline]
    fn from(value: OutActions) -> Self {
        value.0
    }
}

impl<'a> Arbitrary<'a> for OutActions {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let n = u.int_in_range(0..=300u16)?;
        let mut root = Cell::empty_cell();
        for _ in 0..n {
            let action = u.arbitrary::<OutAction>()?;
            root = CellBuilder::build_from((root, action)).unwrap();
            if root.level() != 0 {
                return Err(arbitrary::Error::IncorrectFormat);
            }
        }
        Ok(Self(root))
    }

    #[inline]
    fn size_hint(_: usize) -> (usize, Option<usize>) {
        (2, None)
    }
}

#[derive(Debug, Arbitrary)]
enum MessageInput {
    External,
    Internal {
        bounce_enabled: bool,
        balance_remaining: SimpleBalance,
    },
}

impl From<MessageInput> for ReceivedMessage {
    fn from(value: MessageInput) -> Self {
        let (is_external, bounce_enabled, balance_remaining) = match value {
            MessageInput::External => (true, false, CurrencyCollection::ZERO),
            MessageInput::Internal {
                bounce_enabled,
                balance_remaining,
            } => (false, bounce_enabled, balance_remaining.into()),
        };

        ReceivedMessage {
            root: Cell::empty_cell(),
            init: None,
            body: Default::default(),
            is_external,
            bounce_enabled,
            balance_remaining,
        }
    }
}

#[derive(Debug)]
struct GasFees(Tokens);

impl From<GasFees> for Tokens {
    #[inline]
    fn from(value: GasFees) -> Self {
        value.0
    }
}

impl<'a> Arbitrary<'a> for GasFees {
    #[inline]
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        const MAX: u128 = 1_000_000_000;

        u.int_in_range(0..=MAX).map(|b| Self(Tokens::new(b)))
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <Tokens as Arbitrary>::size_hint(depth)
    }
}

pub fn make_default_config() -> Rc<ParsedConfig> {
    thread_local! {
        pub static PARSED_CONFIG: Rc<ParsedConfig> = {
            let mut config: BlockchainConfig = BocRepr::decode(include_bytes!("../../executor/res/config.boc")).unwrap();

            config.params.set_global_id(100).unwrap();

            // TODO: Update config BOC
            config.params.set_size_limits(&SizeLimitsConfig {
                max_msg_bits: 1 << 21,
                max_msg_cells: 1 << 13,
                max_library_cells: 1000,
                max_vm_data_depth: 512,
                max_ext_msg_size: 65535,
                max_ext_msg_depth: 512,
                max_acc_state_cells: 1 << 16,
                max_acc_state_bits: (1 << 16) * 1023,
                max_acc_public_libraries: 256,
                defer_out_queue_size_limit: 256,
            }).unwrap();

            Rc::new(ParsedConfig::parse(config.params, u32::MAX).unwrap())
        };
    }

    PARSED_CONFIG.with(Clone::clone)
}

pub fn make_default_params() -> ExecutorParams {
    ExecutorParams {
        block_unixtime: 1738799198,
        full_body_in_bounced: false,
        vm_modifiers: tycho_vm::BehaviourModifiers {
            chksig_always_succeed: true,
            ..Default::default()
        },
        ..Default::default()
    }
}

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
