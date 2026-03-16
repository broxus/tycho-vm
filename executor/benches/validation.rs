use std::str::FromStr;

use criterion::{Criterion, criterion_group, criterion_main};
use tycho_executor::{Executor, ExecutorParams, ParsedConfig};
use tycho_types::boc::Boc;
use tycho_types::cell::{HashBytes, Lazy};
use tycho_types::models::{
    Account, AccountState, BlockchainConfig, GlobalCapability, OptionalAccount, ShardAccount,
    StdAddr,
};
use tycho_types::prelude::*;

struct BenchFixture {
    config: ParsedConfig,
    params: ExecutorParams,
    address: StdAddr,
    message: Cell,
    state: ShardAccount,
}

impl BenchFixture {
    fn new() -> Self {
        let address =
            StdAddr::from_str("0:3a34b7adfb327c96777633d2bba3414247d3b4583228ca9c878d14ae9baebaaf")
                .unwrap();

        let mut state: Account = Boc::decode(include_bytes!("data/state.boc"))
            .unwrap()
            .parse()
            .unwrap();

        // The state was captured after this message was already processed, so
        // `stored_timestamp` field equals the message timestamp — the contract would reject it.
        if let AccountState::Active(ref mut state_init) = state.state
            && let Some(data) = &state_init.data
        {
            let mut cs = data.as_ref().as_slice().unwrap();
            let pubkey: HashBytes = cs.load_u256().unwrap();
            state_init.data = Some(CellBuilder::build_from((pubkey, 0u64)).unwrap());
        }

        let message = Boc::decode(include_bytes!("data/msg.boc")).unwrap();

        let bc_config: BlockchainConfig = Boc::decode(include_bytes!("data/config.boc"))
            .unwrap()
            .parse()
            .unwrap();

        let config = ParsedConfig::parse(bc_config, u32::MAX).unwrap();
        let capabilities = config.global.capabilities;

        let params = ExecutorParams {
            block_lt: 1_564_502_000_003,
            block_unixtime: 1_771_503_454,
            disable_delete_frozen_accounts: true,
            full_body_in_bounced: capabilities.contains(GlobalCapability::CapFullBodyInBounced),
            charge_action_fees_on_fail: true,
            strict_extra_currency: true,
            authority_marks_enabled: capabilities.contains(GlobalCapability::CapSuspendByMarks),
            vm_modifiers: tycho_vm::BehaviourModifiers {
                signature_with_id: capabilities
                    .contains(GlobalCapability::CapSignatureWithId)
                    .then_some(config.global_id),
                enable_signature_domains: capabilities
                    .contains(GlobalCapability::CapSignatureDomain),
                ..Default::default()
            },
            ..Default::default()
        };

        let state = ShardAccount {
            account: Lazy::new(&OptionalAccount(Some(state))).unwrap(),
            last_trans_lt: Default::default(),
            last_trans_hash: Default::default(),
        };

        Self {
            config,
            params,
            address,
            message,
            state,
        }
    }
}

fn bench_check_ordinary(c: &mut Criterion) {
    let f = BenchFixture::new();
    let executor = Executor::new(&f.params, &f.config);

    c.bench_function("check_ordinary", |b| {
        b.iter(|| {
            let _ = executor.check_ordinary(&f.address, f.message.clone(), &f.state);
        })
    });
}

fn bench_begin_ordinary(c: &mut Criterion) {
    let f = BenchFixture::new();
    let executor = Executor::new(&f.params, &f.config);

    c.bench_function("begin_ordinary", |b| {
        b.iter(|| {
            let _ = executor.begin_ordinary(&f.address, true, f.message.clone(), &f.state);
        })
    });
}

criterion_group!(benches, bench_check_ordinary, bench_begin_ordinary);
criterion_main!(benches);
