## Tycho VM and Executor

Rust implementation of the TON Virtual Machine and executor.

> [!NOTE]
> This crate tries to be as close to the original implementation as possible.
> However, its main purpose is to be a core of [tycho](https://github.com/broxus/tycho), so there may be some differences.

> [!NOTE]
> This crate is still based on a WIP version of [`everscale-types`](https://github.com/broxus/everscale-types), so for now a `patch` section is required in the end-user `Cargo.toml`.
>
> ```toml
> [patch.crates-io]
> everscale-types = { git = "https://github.com/broxus/everscale-types.git", rev = "245c7f05d7a737c8ebaad7224e7a8641f0b48f68" }
> ```

## VM usage

```rust
let code = Boc::decode(tvmasm!("ACCEPT"))?;
let data = Cell::empty_cell();

let addr = "0:0000000000000000000000000000000000000000000000000000000000000000"
    .parse::<IntAddr>()?;

let smc_info = SmcInfoBase::new()
    .with_now(1733142533)
    .with_block_lt(50899537000013)
    .with_tx_lt(50899537000013)
    .with_account_balance(CurrencyCollection::new(1931553923))
    .with_account_addr(addr.clone())
    .require_ton_v4();

let mut vm_state = VmState::builder()
    .with_smc_info(smc_info)
    .with_stack(tuple![
        slice CellBuilder::build_from(&addr).map(OwnedCellSlice::new_allow_exotic)?,
        int 103289,
    ])
    .with_code(code)
    .with_data(data)
    .with_gas(GasParams::getter())
    .build();

let exit_code = vm_state.run();
```

## Development

### How to bench

```bash
cargo bench --bench dex_pair
cargo bench --bench ever_wallet
cargo bench --bench jetton
```

### How to miri check

```bash
# Add Miri component
rustup +nightly component add miri

# Run all tests with Miri
cargo +nightly miri test
```

### How to fuzz

```bash
# Install fuzzer
cargo install cargo-fuzz

# Run any of the fuzzer targets
cargo +nightly fuzz run action_phase_real -j 12
cargo +nightly fuzz run action_phase_surreal -j 12
cargo +nightly fuzz run vm_only_code -j 12
```

## Contributing

We welcome contributions to the project! If you notice any issues or errors, feel free to open an issue or submit a pull request.

## License

Licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <https://www.apache.org/licenses/LICENSE-2.0>)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or <https://opensource.org/licenses/MIT>)

at your option.
