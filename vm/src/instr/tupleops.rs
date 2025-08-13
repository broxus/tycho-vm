use num_traits::Zero;
use tycho_vm_proc::vm_module;

use crate::error::VmResult;
use crate::gas::GasConsumer;
use crate::saferc::SafeRc;
use crate::stack::{RcStackValue, Stack, StackValue, StackValueType};
use crate::state::VmState;

pub struct TupleOps;

#[vm_module]
impl TupleOps {
    #[op(code = "6d", fmt = "PUSHNULL")]
    fn exec_push_null(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.push_null());
        Ok(0)
    }

    #[op(code = "6e", fmt = "ISNULL")]
    fn exec_is_null(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let top = ok!(stack.pop());
        ok!(stack.push_bool(top.is_null()));
        Ok(0)
    }

    #[op(code = "6f0i", fmt = "TUPLE {i}")]
    fn exec_mktuple(st: &mut VmState, i: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        make_tuple_impl(stack, i as _, &st.gas)
    }

    #[op(code = "6f1i", fmt = "INDEX {i}")]
    fn exec_tuple_index(st: &mut VmState, i: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        tuple_index_impl(stack, i as _)
    }

    #[op(code = "6f2i", fmt = "UNTUPLE {i}")]
    fn exec_untuple(st: &mut VmState, i: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        untuple_impl(stack, i, &st.gas)
    }

    #[op(code = "6f3i", fmt = "UNPACKFIRST {i}")]
    fn exec_untuple_first(st: &mut VmState, i: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        untuple_first_impl(stack, i, &st.gas)
    }

    #[op(code = "6f4i", fmt = "EXPLODE {i}")]
    fn exec_explode_tuple(st: &mut VmState, i: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        explode_tuple_impl(stack, i, &st.gas)
    }

    #[op(code = "6f5i", fmt = "SETINDEX {i}")]
    fn exec_tuple_set_index(st: &mut VmState, i: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        tuple_set_index_impl(stack, i as _, &st.gas)
    }

    #[op(code = "6f6i", fmt = "INDEXQ {i}")]
    fn exec_tuple_quiet_index(st: &mut VmState, i: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        tuple_index_quiet_impl(stack, i as _)
    }

    #[op(code = "6f7i", fmt = "SETINDEXQ {i}")]
    fn exec_tuple_quiet_set_index(st: &mut VmState, i: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        tuple_set_index_quiet_impl(stack, i as _, &st.gas)
    }

    #[op(code = "6f80", fmt = "TUPLEVAR")]
    fn exec_mktuple_var(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 255));
        make_tuple_impl(stack, n as _, &st.gas)
    }

    #[op(code = "6f81", fmt = "INDEXVAR")]
    fn exec_tuple_index_var(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let i = ok!(stack.pop_smallint_range(0, 254));
        tuple_index_impl(stack, i as _)
    }

    #[op(code = "6f82", fmt = "UNTUPLEVAR")]
    fn exec_untuple_var(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 255));
        untuple_impl(stack, n as _, &st.gas)
    }

    #[op(code = "6f83", fmt = "UNPACKFIRSTVAR")]
    fn exec_untuple_first_var(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 255));
        untuple_first_impl(stack, n, &st.gas)
    }

    #[op(code = "6f84", fmt = "EXPLODEVAR")]
    fn exec_explode_tuple_var(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 255));
        explode_tuple_impl(stack, n, &st.gas)
    }

    #[op(code = "6f85", fmt = "SETINDEXVAR")]
    fn exec_tuple_set_index_var(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let i = ok!(stack.pop_smallint_range(0, 254));
        tuple_set_index_impl(stack, i as usize, &st.gas)
    }

    #[op(code = "6f86", fmt = "INDEXVARQ")]
    fn exec_tuple_quiet_index_var(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let i = ok!(stack.pop_smallint_range(0, 254));
        tuple_index_quiet_impl(stack, i as _)
    }

    #[op(code = "6f87", fmt = "SETINDEXVARQ")]
    fn exec_tuple_quiet_set_index_var(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let i = ok!(stack.pop_smallint_range(0, 254));
        tuple_set_index_quiet_impl(stack, i as _, &st.gas)
    }

    #[op(code = "6f88", fmt = "TLEN")]
    fn exec_tuple_length(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let tuple = ok!(stack.pop_tuple_range(0, 255));
        ok!(stack.push_int(tuple.len()));
        Ok(0)
    }

    #[op(code = "6f89", fmt = "QTLEN")]
    fn exec_tuple_length_quiet(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let value = ok!(stack.pop());
        ok!(if let Some(value) = value.as_tuple() {
            stack.push_int(value.len())
        } else {
            stack.push_int(-1)
        });
        Ok(0)
    }

    #[op(code = "6f8a", fmt = "ISTUPLE")]
    fn exec_is_tuple(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let is_tuple = ok!(stack.pop()).is_tuple();
        ok!(stack.push_bool(is_tuple));
        Ok(0)
    }

    #[op(code = "6f8b", fmt = "LAST")]
    fn exec_tuple_last(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let tuple = ok!(stack.pop_tuple_range(1, 255));
        ok!(stack.push_raw(SafeRc::clone(
            tuple.last().expect("Should not fail due to range check")
        )));
        Ok(0)
    }

    #[op(code = "6f8c", fmt = "TPUSH")]
    fn exec_tuple_push(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let x = ok!(stack.pop());
        let mut tuple = ok!(stack.pop_tuple_range(0, 254));
        SafeRc::make_mut(&mut tuple).push(x);
        st.gas.try_consume_tuple_gas(tuple.len() as u64)?;
        ok!(stack.push_raw(tuple));
        Ok(0)
    }

    #[op(code = "6f8d", fmt = "TPOP")]
    fn exec_tuple_pop(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut tuple = ok!(stack.pop_tuple_range(1, 255));
        let x = SafeRc::make_mut(&mut tuple)
            .pop()
            .expect("Should not fail due to range check");
        st.gas.try_consume_tuple_gas(tuple.len() as u64)?;
        ok!(stack.push_raw(tuple));
        ok!(stack.push_raw(x));
        Ok(0)
    }

    #[op(code = "6f90", fmt = "ZEROSWAPIF", args(c = true, d = false))]
    #[op(code = "6f91", fmt = "ZEROSWAPIFNOT", args(c = false, d = false))]
    #[op(code = "6f92", fmt = "ZEROROTRIF", args(c = true, d = true))]
    #[op(code = "6f93", fmt = "ZEROROTRIFNOT", args(c = false, d = true))]
    fn exec_zero_swap_if(st: &mut VmState, c: bool, d: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_int());
        if x.is_zero() != c {
            ok!(stack.push_zero());
            if d {
                ok!(stack.swap(0, 1));
            }
        }
        ok!(stack.push_raw(x));
        Ok(0)
    }

    #[op(code = "6f94", fmt = "ZEROSWAPIF2", args(c = true, d = false))]
    #[op(code = "6f95", fmt = "ZEROSWAPIFNOT2", args(c = false, d = false))]
    #[op(code = "6f96", fmt = "ZEROROTRIF2", args(c = true, d = true))]
    #[op(code = "6f97", fmt = "ZEROROTRIFNOT2", args(c = false, d = true))]
    fn exec_zero_swap_if2(st: &mut VmState, c: bool, d: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_int());
        if x.is_zero() != c {
            ok!(stack.push_zero());
            ok!(stack.push_zero());
            if d {
                ok!(stack.swap(0, 2));
            }
        }
        ok!(stack.push_raw(x));
        Ok(0)
    }

    #[op(code = "6fa0", fmt = "NULLSWAPIF", args(c = true, d = false))]
    #[op(code = "6fa1", fmt = "NULLSWAPIFNOT", args(c = false, d = false))]
    #[op(code = "6fa2", fmt = "NULLROTRIF", args(c = true, d = true))]
    #[op(code = "6fa3", fmt = "NULLROTRIFNOT", args(c = false, d = true))]
    fn exec_null_swap_if(st: &mut VmState, c: bool, d: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_int());
        if x.is_zero() != c {
            ok!(stack.push_null());
            if d {
                ok!(stack.swap(0, 1));
            }
        }
        ok!(stack.push_raw(x));
        Ok(0)
    }

    #[op(code = "6fa4", fmt = "NULLSWAPIF2", args(c = true, d = false))]
    #[op(code = "6fa5", fmt = "NULLSWAPIFNOT2", args(c = false, d = false))]
    #[op(code = "6fa6", fmt = "NULLROTRIF2", args(c = true, d = true))]
    #[op(code = "6fa7", fmt = "NULLROTRIFNOT2", args(c = false, d = true))]
    fn exec_null_swap_if2(st: &mut VmState, c: bool, d: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_int());
        if x.is_zero() != c {
            ok!(stack.push_null());
            ok!(stack.push_null());
            if d {
                ok!(stack.swap(0, 2));
            }
        }
        ok!(stack.push_raw(x));
        Ok(0)
    }

    #[op(code = "6fb$iijj", fmt = "INDEX2 {i},{j}")]
    fn exec_tuple_index2(st: &mut VmState, i: u32, j: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let tuple = ok!(stack.pop_tuple_range(0, 255));

        let Some(value) = tuple.get(i as usize) else {
            vm_bail!(IntegerOutOfRange {
                actual: i.to_string(),
                min: 0,
                max: tuple.len() as _,
            });
        };

        let value = ok!(index_stack_value_as_tuple(value.as_ref(), j as usize));
        ok!(stack.push_raw(value.clone()));
        Ok(0)
    }

    #[op(code = "6f$11iijjkk", fmt = "INDEX3 {i},{j},{k}")]
    fn exec_tuple_index3(st: &mut VmState, i: u32, j: u32, k: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let tuple = ok!(stack.pop_tuple_range(0, 255));

        let Some(value) = tuple.get(i as usize) else {
            vm_bail!(IntegerOutOfRange {
                actual: i.to_string(),
                min: 0,
                max: tuple.len() as _,
            });
        };

        let value = ok!(index_stack_value_as_tuple(value.as_ref(), j as usize));
        let value = ok!(index_stack_value_as_tuple(value.as_ref(), k as usize));
        ok!(stack.push_raw(value.clone()));
        Ok(0)
    }
}

fn make_tuple_impl(stack: &mut Stack, n: usize, gas: &GasConsumer) -> VmResult<i32> {
    let Some(offset) = stack.depth().checked_sub(n) else {
        vm_bail!(StackUnderflow(n));
    };
    let tuple = SafeRc::new(stack.items.drain(offset..offset + n).collect::<Vec<_>>());
    gas.try_consume_tuple_gas(tuple.len() as u64)?;
    ok!(stack.push_raw(tuple));
    Ok(0)
}

fn tuple_index_impl(stack: &mut Stack, i: usize) -> VmResult<i32> {
    let tuple = ok!(stack.pop_tuple_range(0, 255));
    vm_ensure!(i < tuple.len(), IntegerOutOfRange {
        actual: i.to_string(),
        min: 0,
        max: tuple.len() as _,
    });
    ok!(stack.push_raw(tuple[i].clone()));
    Ok(0)
}

fn tuple_index_quiet_impl(stack: &mut Stack, i: usize) -> VmResult<i32> {
    let value = ok!(stack.pop_opt_tuple_range(0, 255)).and_then(|t| t.get(i).cloned());
    ok!(stack.push_opt_raw(value));
    Ok(0)
}

fn untuple_impl(stack: &mut Stack, n: u32, gas: &GasConsumer) -> VmResult<i32> {
    let tuple = ok!(stack.pop_tuple_range(n, n));
    ok!(do_explode_tuple(stack, tuple, n as _, gas));
    Ok(0)
}

fn untuple_first_impl(stack: &mut Stack, n: u32, gas: &GasConsumer) -> VmResult<i32> {
    let tuple = ok!(stack.pop_tuple_range(n, 255));
    ok!(do_explode_tuple(stack, tuple, n as _, gas));
    Ok(0)
}

fn explode_tuple_impl(stack: &mut Stack, n: u32, gas: &GasConsumer) -> VmResult<i32> {
    let tuple = ok!(stack.pop_tuple_range(0, n));
    let tuple_len = tuple.len();
    ok!(do_explode_tuple(stack, tuple, tuple_len, gas));
    ok!(stack.push_int(tuple_len));
    Ok(0)
}

fn do_explode_tuple(
    stack: &mut Stack,
    tuple: SafeRc<Vec<RcStackValue>>,
    n: usize,
    gas: &GasConsumer,
) -> VmResult<()> {
    stack.reserve(n);
    match SafeRc::try_unwrap(tuple) {
        Ok(tuple) => {
            for item in tuple.into_iter().take(n) {
                ok!(stack.push_raw(item));
            }
        }
        Err(tuple) => {
            for item in tuple.iter().take(n) {
                ok!(stack.push_raw(item.clone()));
            }
        }
    }
    gas.try_consume_tuple_gas(n as u64)?;
    Ok(())
}

fn tuple_set_index_impl(stack: &mut Stack, i: usize, gas: &GasConsumer) -> VmResult<i32> {
    let x = ok!(stack.pop());
    let mut tuple = ok!(stack.pop_tuple_range(0, 255));
    vm_ensure!(i < tuple.len(), IntegerOutOfRange {
        min: 0,
        max: tuple.len() as _,
        actual: i.to_string()
    });
    SafeRc::make_mut(&mut tuple)[i] = x;
    gas.try_consume_tuple_gas(tuple.len() as u64)?;
    ok!(stack.push_raw(tuple));
    Ok(0)
}

fn tuple_set_index_quiet_impl(stack: &mut Stack, i: usize, gas: &GasConsumer) -> VmResult<i32> {
    let x = ok!(stack.pop());
    let mut tuple = ok!(stack.pop_opt_tuple_range(0, 255));
    vm_ensure!(i < 255, IntegerOutOfRange {
        min: 0,
        max: 255,
        actual: i.to_string()
    });

    let updated_items = match &mut tuple {
        None if x.is_null() => 0,
        None => {
            let mut items = vec![Stack::make_null(); i + 1];
            items[i] = x;
            tuple = Some(SafeRc::new(items));
            i + 1
        }
        Some(items) if i < items.len() => {
            SafeRc::make_mut(items)[i] = x;
            items.len()
        }
        Some(_) if x.is_null() => 0,
        Some(items) => {
            let items = SafeRc::make_mut(items);
            items.resize(i + 1, Stack::make_null());
            items[i] = x;
            i + 1
        }
    };

    gas.try_consume_tuple_gas(updated_items as u64)?;

    ok!(match tuple {
        None => stack.push_null(),
        Some(value) => stack.push_raw(value),
    });

    Ok(0)
}

fn index_stack_value_as_tuple(value: &dyn StackValue, i: usize) -> VmResult<&RcStackValue> {
    let Some(tuple) = value.as_tuple_range(0, 255) else {
        vm_bail!(InvalidType {
            expected: StackValueType::Tuple as _,
            actual: value.raw_ty(),
        });
    };

    let Some(value) = tuple.get(i) else {
        vm_bail!(IntegerOutOfRange {
            actual: i.to_string(),
            min: 0,
            max: tuple.len() as _,
        });
    };

    Ok(value)
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;
    use tracing_test::traced_test;

    use crate::saferc::SafeRc;

    #[test]
    #[traced_test]
    fn swap_if_null() {
        assert_run_vm!("NULLSWAPIF", [int 0] => [int 0]);
        assert_run_vm!("NULLSWAPIF", [int -1] => [null, int -1]);

        assert_run_vm!("NULLSWAPIFNOT", [int 0] => [null, int 0]);
        assert_run_vm!("NULLSWAPIFNOT", [int -1] => [int -1]);

        assert_run_vm!("NULLROTRIF", [int 1, int 0] => [int 1, int 0]);
        assert_run_vm!("NULLROTRIF", [int 1, int -1] => [null, int 1, int -1]);

        assert_run_vm!("NULLROTRIFNOT", [int 1, int 0] => [null, int 1, int 0]);
        assert_run_vm!("NULLROTRIFNOT", [int 1, int -1] => [int 1, int -1]);
    }

    #[test]
    #[traced_test]
    fn swap_if_null_2() {
        assert_run_vm!("NULLSWAPIF2", [int 0] => [int 0]);
        assert_run_vm!("NULLSWAPIF NULLSWAPIF", [int 0] => [int 0]);
        assert_run_vm!("NULLSWAPIF2", [int -1] => [null, null, int -1]);
        assert_run_vm!("NULLSWAPIF NULLSWAPIF", [int -1] => [null, null, int -1]);

        assert_run_vm!("NULLSWAPIFNOT2", [int 0] => [null, null, int 0]);
        assert_run_vm!("NULLSWAPIFNOT NULLSWAPIFNOT", [int 0] => [null, null, int 0]);
        assert_run_vm!("NULLSWAPIFNOT2", [int -1] => [int -1]);
        assert_run_vm!("NULLSWAPIFNOT NULLSWAPIFNOT", [int -1] => [int -1]);

        assert_run_vm!("NULLROTRIF2", [int 1, int 0] => [int 1, int 0]);
        assert_run_vm!("NULLROTRIF NULLROTRIF", [int 1, int 0] => [int 1, int 0]);
        assert_run_vm!("NULLROTRIF2", [int 1, int -1] => [null, null, int 1, int -1]);
        assert_run_vm!("NULLROTRIF NULLROTRIF", [int 1, int -1] => [null, null, int 1, int -1]);

        assert_run_vm!("NULLROTRIFNOT2", [int 1, int 0] => [null, null, int 1, int 0]);
        assert_run_vm!("NULLROTRIFNOT NULLROTRIFNOT", [int 1, int 0] => [null, null, int 1, int 0]);
        assert_run_vm!("NULLROTRIFNOT2", [int 1, int -1] => [int 1, int -1]);
        assert_run_vm!("NULLROTRIFNOT NULLROTRIFNOT", [int 1, int -1] => [int 1, int -1]);
    }

    #[test]
    #[traced_test]
    fn index2() {
        let outer_tuple = SafeRc::new(tuple![
            [int 1, int 2, int 3, int 4],
            [int 5, int 6, int 7, int 8],
        ]);

        assert_run_vm!("INDEX2 0, 0", [raw outer_tuple.clone()] => [int 1]);
        assert_run_vm!("INDEX 0 INDEX 0", [raw outer_tuple.clone()] => [int 1]);
        assert_run_vm!("INDEX2 0, 1", [raw outer_tuple.clone()] => [int 2]);
        assert_run_vm!("INDEX 0 INDEX 1", [raw outer_tuple.clone()] => [int 2]);
        assert_run_vm!("INDEX2 0, 2", [raw outer_tuple.clone()] => [int 3]);
        assert_run_vm!("INDEX 0 INDEX 2", [raw outer_tuple.clone()] => [int 3]);
        assert_run_vm!("INDEX2 0, 3", [raw outer_tuple.clone()] => [int 4]);
        assert_run_vm!("INDEX 0 INDEX 3", [raw outer_tuple.clone()] => [int 4]);

        assert_run_vm!("INDEX2 1, 0", [raw outer_tuple.clone()] => [int 5]);
        assert_run_vm!("INDEX 1 INDEX 0", [raw outer_tuple.clone()] => [int 5]);
        assert_run_vm!("INDEX2 1, 1", [raw outer_tuple.clone()] => [int 6]);
        assert_run_vm!("INDEX 1 INDEX 1", [raw outer_tuple.clone()] => [int 6]);
        assert_run_vm!("INDEX2 1, 2", [raw outer_tuple.clone()] => [int 7]);
        assert_run_vm!("INDEX 1 INDEX 2", [raw outer_tuple.clone()] => [int 7]);
        assert_run_vm!("INDEX2 1, 3", [raw outer_tuple.clone()] => [int 8]);
        assert_run_vm!("INDEX 1 INDEX 3", [raw outer_tuple.clone()] => [int 8]);

        assert_run_vm!("INDEX2 0, 2", [[[int 1], [int 5]]] => [int 0], exit_code: 5);
        assert_run_vm!("INDEX2 2, 2", [[[int 1], [int 5]]] => [int 0], exit_code: 5);
    }

    #[test]
    #[traced_test]
    fn index3() {
        let tuple = {
            let mut tuple = Vec::new();
            let mut n = 0;
            for _ in 0..4 {
                let mut row = Vec::new();
                for _ in 0..4 {
                    let mut col = Vec::new();
                    for _ in 0..4 {
                        n += 1;
                        col.push(SafeRc::new_dyn_value(BigInt::from(n)));
                    }
                    row.push(SafeRc::new_dyn_value(col));
                }
                tuple.push(SafeRc::new_dyn_value(row));
            }
            SafeRc::new_dyn_value(tuple)
        };

        assert_run_vm!("INDEX3 0, 0, 0", [raw tuple.clone()] => [int 1]);
        assert_run_vm!("INDEX3 0, 0, 1", [raw tuple.clone()] => [int 2]);
        assert_run_vm!("INDEX3 0, 0, 2", [raw tuple.clone()] => [int 3]);
        assert_run_vm!("INDEX 0 INDEX 0 INDEX 2", [raw tuple.clone()] => [int 3]);
        assert_run_vm!("INDEX2 0, 0 INDEX 2", [raw tuple.clone()] => [int 3]);

        let t = 1 + 3 + 2 * 4 + 4 * 4;
        assert_run_vm!("INDEX3 1, 2, 3", [raw tuple.clone()] => [int t]);
        assert_run_vm!("INDEX 1 INDEX 2 INDEX 3", [raw tuple.clone()] => [int t]);
        assert_run_vm!("INDEX2 1, 2 INDEX 3", [raw tuple.clone()] => [int t]);

        assert_run_vm!("INDEX3 3, 3, 3", [raw tuple.clone()] => [int 64]);
        assert_run_vm!("INDEX2 3, 3 INDEX 3", [raw tuple.clone()] => [int 64]);
    }
}
