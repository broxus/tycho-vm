#![no_main]

use everscale_asm::Code;
use libfuzzer_sys::{fuzz_target, Corpus};
use tycho_vm::{CustomSmcInfo, GasParams, SafeRc, VmState};

fuzz_target!(|code: String| -> Corpus {
    if !code.chars().all(|c| c.is_ascii_graphic() || c == ' ') {
        return Corpus::Reject;
    }

    let code = match Code::assemble(&code) {
        Ok(code) => code,
        Err(_) => return Corpus::Reject,
    };

    let mut vm = VmState::builder()
        .with_code(code)
        .with_smc_info(CustomSmcInfo {
            version: VmState::DEFAULT_VERSION,
            c7: SafeRc::new(Vec::new()),
        })
        .with_gas(GasParams::getter())
        .build();

    _ = vm.run();
    Corpus::Keep
});
