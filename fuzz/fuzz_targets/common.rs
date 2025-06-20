use std::rc::Rc;

use arbitrary::{Arbitrary, Unstructured};
use everscale_types::boc::BocRepr;
use everscale_types::models::{BlockchainConfig, ExecutedComputePhase};
use everscale_types::num::Tokens;
use tycho_executor::{ExecutorParams, ParsedConfig};

#[derive(Debug)]
pub struct GasFees(pub Tokens);

impl From<GasFees> for Tokens {
    #[inline]
    fn from(value: GasFees) -> Self {
        value.0
    }
}

impl<'a> Arbitrary<'a> for GasFees {
    #[inline]
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
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
            config.params.set_size_limits(&ParsedConfig::DEFAULT_SIZE_LIMITS_CONFIG).unwrap();

            Rc::new(ParsedConfig::parse(config, u32::MAX).unwrap())
        };
    }

    PARSED_CONFIG.with(Clone::clone)
}

pub fn make_default_params() -> ExecutorParams {
    ExecutorParams {
        block_unixtime: 1738799198,
        full_body_in_bounced: false,
        strict_extra_currency: true,
        vm_modifiers: tycho_vm::BehaviourModifiers {
            chksig_always_succeed: true,
            ..Default::default()
        },
        charge_action_fees_on_fail: true,
        ..Default::default()
    }
}

pub fn stub_compute_phase(gas_fees: Tokens) -> ExecutedComputePhase {
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
