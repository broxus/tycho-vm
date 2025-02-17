use std::str::FromStr;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use everscale_types::models::{
    AccountState, BlockchainConfig, CurrencyCollection, IntAddr, OptionalAccount, OwnedMessage,
    StdAddr,
};
use everscale_types::prelude::Boc;
use tycho_vm::{tuple, GasParams, SmcInfoBase, VmState};

fn vm_benchmark(c: &mut Criterion) {
    let message_cell = Boc::decode_base64("te6ccgECCgEAAdIAAbFIABbVmx+wnv8fS4+kTo8s1hEqmz8ZYjetoq95FUaLoFUhAAYExf4R2cGqdkxcoEzu/tW7WoYIYw/JDYAoA3HUPkxIUgt0A/wGL1+0AABky2zFLKjOex56wAEBa3DYn8mAFJOanCsVNCqqvMSOs8XJzs2kTAFvABsSPI3yUj4IlSegAAAAAAAAAAAAAAF0h26AEAIBQ4AcNkp9Jc1uMtawP3MzjPaDNfYRgoLDQpJ8RktziPDpwnADAUOAFjbz5aaxiGlDuV/FUC4FtnTzjkE4CIRE2PMqoo1nCA5wBAFDgBGIQaezWj3ozIlBQpKABWzPoIuwq/YS9RDvT1OchiNQcAUEtwYAAAAATRHHbgAAAAAAAAAAAAAAAAX14QCAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACCQgHBgAyAQAAAABNEcduAAAAAAAAAAAAAAAABfXhAAAyAAAAAABNEcduAAAAAAAAAAAAAAAABfXhAABjAAAAAAAAAAAAAAAH2QkY34AcuyyX7tchRTlCP+B0CAXdlNQ480H2mxReDUz3wKb01/AAAA==").unwrap();
    let message = message_cell.clone().parse::<OwnedMessage>().unwrap();

    let account_boc = Boc::decode(include_bytes!("dex_pair_account.boc")).unwrap();
    let account = account_boc.parse::<OptionalAccount>().unwrap().0.unwrap();

    let config_cell = Boc::decode(include_bytes!("dex_pair_config.boc")).unwrap();
    let config = config_cell.parse::<BlockchainConfig>().unwrap();

    let (code, data) = match account.state {
        AccountState::Active(state) => (state.code.unwrap(), state.data.unwrap()),
        _ => panic!(),
    };

    let addr = IntAddr::Std(
        StdAddr::from_str("0:181317f8476706a9d931728133bbfb56ed6a18218c3f243600a00dc750f93121")
            .unwrap(),
    );

    c.bench_function("dex_pair", |b| {
        b.iter(|| {
            let smc_info = SmcInfoBase::new()
                .with_now(1732087613)
                .with_block_lt(55412433000000)
                .with_tx_lt(55412433000021)
                .with_account_balance(CurrencyCollection::new(10000000000))
                .with_account_addr(addr.clone())
                .with_config(config.params.clone())
                .require_ton_v4();

            let mut vm_state = VmState::builder()
                .with_smc_info(smc_info)
                .with_stack(tuple![
                    int 3194942419u64,
                    int 2195521791u64,
                    cell message_cell.clone(),
                    slice message.body.clone(),
                    int 0
                ])
                .with_code(code.clone())
                .with_data(data.clone())
                .with_gas(GasParams::unlimited())
                .with_init_selector(false)
                .build();

            let result = vm_state.run();
            _ = black_box(result);
        });
    });
}

criterion_group!(benches, vm_benchmark);
criterion_main!(benches);
