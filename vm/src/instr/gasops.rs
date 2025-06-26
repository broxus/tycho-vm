use num_traits::{Signed, ToPrimitive};
use tycho_vm_proc::vm_module;

use crate::cont::QuitCont;
use crate::error::VmResult;
use crate::saferc::SafeRc;
use crate::state::VmState;

pub struct GasOps;

#[vm_module]
impl GasOps {
    #[op(code = "f800", fmt = "ACCEPT")]
    fn exec_accept(st: &mut VmState) -> VmResult<i32> {
        exec_set_gas(st, i64::MAX as _)
    }

    #[op(code = "f801", fmt = "SETGASLIMIT")]
    fn exec_set_gas_limit(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_int());
        let limit = if x.is_positive() {
            x.magnitude().to_i64().unwrap_or(i64::MAX) as u64
        } else {
            0u64
        };

        exec_set_gas(st, limit)
    }

    #[op(code = "f802", fmt = "BUYGAS")]
    fn exec_buy_gas(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut x = ok!(stack.pop_int());
        let limit = if x.is_positive() {
            {
                let x = SafeRc::make_mut(&mut x);
                *x <<= 16;
                *x /= st.gas.price();
            }

            x.magnitude().to_i64().unwrap_or(i64::MAX) as u64
        } else {
            0u64
        };

        exec_set_gas(st, limit)
    }

    #[op(code = "f804", fmt = "GRAMTOGAS")]
    fn exec_gram_to_gas(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut x = ok!(stack.pop_int());
        if x.is_positive() {
            {
                let x = SafeRc::make_mut(&mut x);
                *x <<= 16;
                *x /= st.gas.price();
            }

            if x.magnitude().to_i64().is_some() {
                ok!(stack.push_raw(x));
            } else {
                ok!(stack.push_int(i64::MAX));
            }
        } else {
            ok!(stack.push_zero());
        }
        Ok(0)
    }

    #[op(code = "f805", fmt = "GASTOGRAM")]
    fn exec_gas_to_gram(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut g = ok!(stack.pop_int());
        {
            let g = SafeRc::make_mut(&mut g);
            *g *= st.gas.price();
            *g >>= 16;
        }
        ok!(stack.push_raw_int(g, false));
        Ok(0)
    }

    #[op(code = "f807", fmt = "GASCONSUMED")]
    fn exec_gas_consumed(st: &mut VmState) -> VmResult<i32> {
        ok!(st.version.require_ton(4..));

        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.push_int(st.gas.consumed()));
        Ok(0)
    }

    #[op(code = "f80f", fmt = "COMMIT")]
    fn exec_commit(st: &mut VmState) -> VmResult<i32> {
        st.force_commit()?;
        Ok(0)
    }
}

fn exec_set_gas(st: &mut VmState, gas_limit: u64) -> VmResult<i32> {
    vm_ensure!(gas_limit >= st.gas.consumed(), OutOfGas);
    st.gas.set_limit(gas_limit);
    if st.modifiers.stop_on_accept {
        st.jump(SafeRc::from(QuitCont { exit_code: 0 }))
    } else {
        Ok(0)
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;
    use tracing_test::traced_test;
    use tycho_types::boc::Boc;

    use crate::IntoCode;

    #[test]
    #[traced_test]
    fn gas_price_ops() {
        assert_run_vm!(
            r#"
            INT 1000 SETGASLIMIT
            INT 999 SETGASLIMIT
            INT 10000 SETGASLIMIT
            "#,
            [] => []
        );
        assert_run_vm!(
            r#"
            INT 1000 SETGASLIMIT
            INT 999 SETGASLIMIT
            INT 10000 SETGASLIMIT
            INT 0 SETGASLIMIT
            "#,
            [] => [int 224],
            exit_code: -14
        );

        assert_run_vm!("SETGASLIMIT", [int 0] => [int 26], exit_code: -14);
        assert_run_vm!("SETGASLIMIT", [int u128::MAX] => []);

        assert_run_vm!("BUYGAS", [int 0] => [int 26], exit_code: -14);
        assert_run_vm!("BUYGAS", gas: 1000, [int 999_000] => []);

        assert_run_vm!("GRAMTOGAS", [int 0] => [int 0]);
        assert_run_vm!("GRAMTOGAS", [int 1] => [int 0]);
        assert_run_vm!("GRAMTOGAS", [int -1] => [int 0]);
        assert_run_vm!("GRAMTOGAS", [int 999] => [int 0]);
        assert_run_vm!("GRAMTOGAS", [int 1000] => [int 1]);
        assert_run_vm!("GRAMTOGAS", [int 1001] => [int 1]);
        assert_run_vm!("GRAMTOGAS", [int (i64::MAX as u128) * 1000] => [int i64::MAX]);
        assert_run_vm!("GRAMTOGAS", [int (u64::MAX as u128) * 1000] => [int i64::MAX]);
        assert_run_vm!("GRAMTOGAS", [int u128::MAX] => [int i64::MAX]);

        assert_run_vm!("GASTOGRAM", [int 0] => [int 0]);
        assert_run_vm!("GASTOGRAM", [int 1] => [int 1000]);
        assert_run_vm!("GASTOGRAM", [int -1] => [int -1000]);
        assert_run_vm!("GASTOGRAM", [int u64::MAX] => [int (u64::MAX as u128) * 1000]);
        assert_run_vm!("GASTOGRAM", [int (BigInt::from(1) << 256) - 1] => [int 0], exit_code: 4);
    }

    #[test]
    #[traced_test]
    fn gas_stats() {
        assert_run_vm!("INT 10 INT 20 ADD DROP GASCONSUMED", [] => [int 106]);

        // GASCONSUMED inside RUNVM
        let child_code = Boc::decode(tvmasm!("INT 10 INT 20 ADD DROP GASCONSUMED"))
            .unwrap()
            .into_code()
            .unwrap();

        assert_run_vm!(
            r#"
            INT 100 INT 200 INT 300 MUL DIV DROP
            RUNVM 0
            GASCONSUMED
            "#,
            [int 0, slice child_code] => [int 106, int 0, int 367],
        );
    }
}
