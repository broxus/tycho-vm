#![no_main]

use libfuzzer_sys::fuzz_target;
use tycho_types::arbitrary::OrdinaryCell;
use tycho_vm::{CustomSmcInfo, GasParams, SafeRc, VmState};

fuzz_target!(|code: OrdinaryCell| {
    let OrdinaryCell(code) = code;

    let mut vm = VmState::builder()
        .with_code(code)
        .with_smc_info(CustomSmcInfo {
            version: VmState::DEFAULT_VERSION,
            c7: SafeRc::new(Vec::new()),
        })
        .with_gas(GasParams::getter())
        .build();

    _ = vm.run();
});
