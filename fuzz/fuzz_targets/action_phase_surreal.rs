#![no_main]

use arbitrary::{Arbitrary, Result, Unstructured};
use libfuzzer_sys::fuzz_target;
use tycho_executor::ExecutorState;
use tycho_executor::phase::{ActionPhaseContext, ActionPhaseFull, ReceivedMessage};
use tycho_types::boc::Boc;
use tycho_types::cell::{Cell, CellFamily, HashBytes};
use tycho_types::dict::Dict;
use tycho_types::models::{
    AccountState, AccountStatus, CurrencyCollection, ExtraCurrencyCollection, MsgInfo, StdAddr,
};
use tycho_types::num::{Tokens, VarUint248};

use self::common::{GasFees, make_default_config, make_default_params, stub_compute_phase};

mod common;

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
        burned: Tokens::ZERO,
        cached_storage_stat: None,
    };

    // Run transaction part.
    let compute_phase = stub_compute_phase(gas_fees);

    let ActionPhaseFull { action_phase, .. } = state
        .action_phase(ActionPhaseContext {
            received_message: msg.as_mut(),
            original_balance: original_balance.clone(),
            new_state: Default::default(),
            actions: input.actions.into(),
            compute_phase: &compute_phase,
            inspector: None,
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
    balance: AnyBalance,
    actions: OutActions,
}

#[derive(Debug, Arbitrary)]
enum MessageInput {
    External,
    Internal {
        bounce_enabled: bool,
        balance_remaining: AnyBalance,
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
        let cell = u.arbitrary::<Cell>()?;
        if cell.level() != 0 || cell.has_max_depth() {
            return Err(arbitrary::Error::IncorrectFormat);
        }
        Ok(Self(cell))
    }

    #[inline]
    fn size_hint(_: usize) -> (usize, Option<usize>) {
        (2, None)
    }
}

#[derive(Debug)]
struct AnyBalance(pub CurrencyCollection);

impl From<AnyBalance> for CurrencyCollection {
    #[inline]
    fn from(value: AnyBalance) -> Self {
        value.0
    }
}

impl<'a> Arbitrary<'a> for AnyBalance {
    #[inline]
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        const BIG_BALANCE: u128 = 100_000_000_000_000_000_000;

        let size = u.arbitrary::<u8>()?;
        let other = if size <= 128 {
            Dict::new()
        } else {
            let mut dict = Dict::<u32, VarUint248>::new();
            for _ in 128..size {
                dict.set(
                    u.arbitrary::<u32>()?,
                    VarUint248::new(u.int_in_range(0..=BIG_BALANCE)?),
                )
                .unwrap();
            }
            dict
        };

        Ok(Self(CurrencyCollection {
            tokens: Tokens::new(u.int_in_range(0..=BIG_BALANCE)?),
            other: ExtraCurrencyCollection::from_raw(other.into_root()),
        }))
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        Self::try_size_hint(depth).unwrap_or_default()
    }

    fn try_size_hint(
        depth: usize,
    ) -> Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and(
            <Tokens as Arbitrary>::try_size_hint(depth)?,
            <ExtraCurrencyCollection as Arbitrary>::try_size_hint(depth)?,
        ))
    }
}
