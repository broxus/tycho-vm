#![no_main]

use std::ops::ControlFlow;

use arbitrary::{Arbitrary, Result as ArbitraryResult, Unstructured};
use everscale_types::arbitrary::OrdinaryCell;
use everscale_types::cell::CellBuilder;
use libfuzzer_sys::{fuzz_target, Corpus};
use num_bigint::{BigInt, Sign};
use tycho_vm::{CustomSmcInfo, GasParams, RcStackValue, SafeRc, Stack, Tuple, VmState};

const MAX_BIGINT_BYTES: usize = 32; // Max bytes for BigInt generation (32 bytes = 256 bits)
const MAX_TUPLE_ELEMENTS: u32 = 16;

#[derive(Debug)]
enum ArbitraryStackValue {
    Null,
    Int(BigInt),
    NaN,
    Cell(OrdinaryCell),
    EmptyBuilder,
    Tuple(Vec<ArbitraryStackValue>),
}

impl<'a> Arbitrary<'a> for ArbitraryStackValue {
    fn arbitrary(u: &mut Unstructured<'a>) -> ArbitraryResult<Self> {
        match u.int_in_range(0..=5)? {
            0 => Ok(ArbitraryStackValue::Null),
            1 => {
                let sign = match u.int_in_range(0..=2)? {
                    0 => Sign::Plus,
                    1 => Sign::Minus,
                    _ => Sign::NoSign,
                };

                let num_bytes = u.int_in_range(0..=MAX_BIGINT_BYTES)?;
                let bytes_slice: &[u8] = u.bytes(num_bytes)?;
                Ok(ArbitraryStackValue::Int(BigInt::from_bytes_be(
                    sign,
                    bytes_slice,
                )))
            }
            2 => Ok(ArbitraryStackValue::NaN),
            3 => {
                let cell: OrdinaryCell = u.arbitrary()?;
                Ok(ArbitraryStackValue::Cell(cell))
            }
            4 => Ok(ArbitraryStackValue::EmptyBuilder),
            5 => {
                // Tuple (recursive, up to MAX_TUPLE_ELEMENTS)
                let mut items = Vec::new();
                u.arbitrary_loop(None, Some(MAX_TUPLE_ELEMENTS), |u_inner| {
                    items.push(u_inner.arbitrary()?);
                    Ok(ControlFlow::Continue(()))
                })?;
                Ok(ArbitraryStackValue::Tuple(items))
            }
            _ => unreachable!(),
        }
    }
}

fn arbitrary_to_rc(item: ArbitraryStackValue) -> Option<RcStackValue> {
    Some(match item {
        ArbitraryStackValue::Null => Stack::make_null(),
        ArbitraryStackValue::Int(val) => SafeRc::new_dyn_value(val),
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
    })
}

const MAX_ITEMS: u32 = 32;

#[derive(Debug)]
struct Input {
    code: OrdinaryCell,
    initial_stack_items: Vec<ArbitraryStackValue>,
    c7_items: Vec<ArbitraryStackValue>,
}

impl<'a> Arbitrary<'a> for Input {
    fn arbitrary(u: &mut Unstructured<'a>) -> ArbitraryResult<Self> {
        let code: OrdinaryCell = u.arbitrary()?;

        let mut initial_stack_items = Vec::new();
        u.arbitrary_loop(None, Some(MAX_ITEMS), |u_inner| {
            initial_stack_items.push(u_inner.arbitrary()?);
            Ok(ControlFlow::Continue(()))
        })?;

        let mut c7_items = Vec::new();
        u.arbitrary_loop(None, Some(MAX_ITEMS), |u_inner| {
            c7_items.push(u_inner.arbitrary()?);
            Ok(ControlFlow::Continue(()))
        })?;

        Ok(Input {
            code,
            initial_stack_items,
            c7_items,
        })
    }
}

fuzz_target!(|input: Input| -> Corpus {
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

    let elapsed = start.elapsed().as_millis();
    if elapsed > 1000 {
        panic!("Execution took too long: {} ms", elapsed);
    }

    Corpus::Keep
});
