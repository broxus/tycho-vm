#![no_main]

use arbitrary::Arbitrary;
use everscale_types::arbitrary::OrdinaryCell;
use everscale_types::cell::CellBuilder;
use libfuzzer_sys::{fuzz_target, Corpus};
use num_bigint::BigInt;
use tycho_vm::{CustomSmcInfo, GasParams, RcStackValue, SafeRc, Stack, Tuple, VmState};

#[derive(Debug, Arbitrary)]
enum ArbitraryStackValue {
    Null,
    Int(BigInt),
    NaN,
    Cell(OrdinaryCell),
    EmptyBuilder,
    Tuple(Vec<ArbitraryStackValue>),
}

fn arbitrary_to_rc(item: ArbitraryStackValue) -> Option<RcStackValue> {
    Some(match item {
        ArbitraryStackValue::Null => Stack::make_null(),
        ArbitraryStackValue::Int(val) if val.bits() <= 256 => SafeRc::new_dyn_value(val),
        ArbitraryStackValue::NaN => Stack::make_nan(),
        ArbitraryStackValue::Cell(OrdinaryCell(cell)) => SafeRc::new_dyn_value(cell),
        ArbitraryStackValue::EmptyBuilder => SafeRc::new_dyn_value(CellBuilder::new()),
        ArbitraryStackValue::Tuple(items) => {
            let tuple_items: Tuple = items
                .into_iter()
                .map(arbitrary_to_rc)
                .collect::<Option<Vec<_>>>()?;
            SafeRc::new_dyn_value(tuple_items)
        }
        ArbitraryStackValue::Int(_) => return None,
    })
}

#[derive(Debug, Arbitrary)]
struct Input {
    code: OrdinaryCell,
    initial_stack_items: Vec<ArbitraryStackValue>,
    c7_items: Vec<ArbitraryStackValue>,
}

const MAX_ITEMS: usize = 32;

fuzz_target!(|input: Input| -> Corpus {
    if input.initial_stack_items.len() > MAX_ITEMS {
        return Corpus::Reject;
    }

    if input.c7_items.len() > MAX_ITEMS {
        return Corpus::Reject;
    }

    let OrdinaryCell(code) = input.code;

    let stack_items: Option<Vec<RcStackValue>> = input
        .initial_stack_items
        .into_iter()
        .map(arbitrary_to_rc)
        .collect();

    let stack_items = match stack_items {
        Some(items) => items,
        None => return Corpus::Reject,
    };

    let c7_rc_items: Option<Vec<RcStackValue>> =
        input.c7_items.into_iter().map(arbitrary_to_rc).collect();
    let c7_rc_items = match c7_rc_items {
        Some(items) => items,
        None => return Corpus::Reject,
    };

    let stack = Stack::with_items(stack_items);

    let start = std::time::Instant::now();
    let mut vm = VmState::builder()
        .with_code(code)
        .with_raw_stack(stack.into())
        .with_smc_info(CustomSmcInfo {
            version: VmState::DEFAULT_VERSION,
            c7: SafeRc::new(c7_rc_items),
        })
        .with_gas(GasParams::getter())
        .build();

    let _ = vm.run();
    if start.elapsed().as_millis() > 500 {
        panic!("Execution took too long");
    }

    Corpus::Keep
});
