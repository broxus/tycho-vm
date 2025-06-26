use criterion::{Criterion, criterion_group, criterion_main};
use tycho_types::boc::Boc;
use tycho_types::models::{CurrencyCollection, IntAddr, OwnedMessage};
use tycho_vm::{GasParams, SmcInfoBase, VmState, tuple};

fn vm_benchmark(c: &mut Criterion) {
    let code = Boc::decode_base64("te6cckEBBgEA/AABFP8A9KQT9LzyyAsBAgEgAgMABNIwAubycdcBAcAA8nqDCNcY7UTQgwfXAdcLP8j4KM8WI88WyfkAA3HXAQHDAJqDB9cBURO68uBk3oBA1wGAINcBgCDXAVQWdfkQ8qj4I7vyeWa++COBBwiggQPoqFIgvLHydAIgghBM7mRsuuMPAcjL/8s/ye1UBAUAmDAC10zQ+kCDBtcBcdcBeNcB10z4AHCAEASqAhSxyMsFUAXPFlAD+gLLaSLQIc8xIddJoIQJuZgzcAHLAFjPFpcwcQHLABLM4skB+wAAPoIQFp4+EbqOEfgAApMg10qXeNcB1AL7AOjRkzLyPOI+zYS/").unwrap();
    let data = Boc::decode_base64(
        "te6ccgEBAQEAKgAAUMiw1sYIywOsoSiX5hi1n13b0Qt+KVhFxHpNZ3ILXjV1AAABk0YeykY=",
    )
    .unwrap();

    let message_cell = Boc::decode_base64("te6ccgEBBAEA0gABRYgAxgNljqstzcrTTaJ1ydjhkp4u/ZwXwz8tG7nOeonPX44MAQHhmt2/xQjjwjfYraY7Tv53Ct8o9OAtI8nD7DFB19TrG7W8wYMxQKtbXuvGvaKFoB9D0lMZwnPpZ1fEBWxaXZgtg/IsNbGCMsDrKEol+YYtZ9d29ELfilYRcR6TWdyC141dQAAAZNGIEb+Zzz2EEzuZGyACAWWADGA2WOqy3NytNNonXJ2OGSni79nBfDPy0buc56ic9fjgAAAAAAAAAAAAAAAHc1lAADgDAAA=").unwrap();
    let message = message_cell.parse::<OwnedMessage>().unwrap();

    let addr = "0:6301b2c75596e6e569a6d13ae4ec70c94f177ece0be19f968ddce73d44e7afc7"
        .parse::<IntAddr>()
        .unwrap();

    c.bench_function("ever_wallet", |b| {
        b.iter(|| {
            let smc_info = SmcInfoBase::new()
                .with_now(1732048342)
                .with_block_lt(55398352000001)
                .with_tx_lt(55398317000004)
                .with_account_balance(CurrencyCollection::new(10000000000))
                .with_account_addr(addr.clone())
                .require_ton_v4()
                .with_code(code.clone());

            let mut vm_state = VmState::builder()
                .with_smc_info(smc_info)
                .with_stack(tuple![
                    int 4989195982u64,
                    int 0,
                    cell message_cell.clone(),
                    slice message.body.clone(),
                    int -1,
                ])
                .with_code(code.clone())
                .with_data(data.clone())
                .with_gas(GasParams::getter())
                .build();

            let result = vm_state.run();
            _ = std::hint::black_box(result);
        });
    });
}

criterion_group!(benches, vm_benchmark);
criterion_main!(benches);
