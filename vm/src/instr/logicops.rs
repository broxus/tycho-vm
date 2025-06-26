use num_bigint::{BigInt, Sign};
use num_traits::{One, Zero};
use tycho_types::prelude::*;
use tycho_vm_proc::vm_module;

use crate::error::VmResult;
use crate::saferc::SafeRc;
use crate::state::VmState;

pub struct LogicOps;

#[vm_module]
impl LogicOps {
    #[op(code = "aayy", fmt = "LSHIFT {y}", args(y = (args & 0xff) + 1, quiet = false))]
    #[op(code = "b7aayy", fmt = "QLSHIFT {y}", args(y = (args & 0xff) + 1, quiet = true))]
    fn exec_lshift_tinyint8(st: &mut VmState, y: u32, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *SafeRc::make_mut(&mut x) <<= y;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "abyy", fmt = "RSHIFT {y}", args(y = (args & 0xff) + 1, quiet = false))]
    #[op(code = "b7abyy", fmt = "QRSHIFT {y}", args(y = (args & 0xff) + 1, quiet = true))]
    fn exec_rshift_tinyint8(st: &mut VmState, y: u32, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *SafeRc::make_mut(&mut x) >>= y;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "ac", fmt = "LSHIFT", args(quiet = false))]
    #[op(code = "b7ac", fmt = "QLSHIFT", args(quiet = true))]
    fn exec_lshift(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_smallint_range(0, 1023));
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *SafeRc::make_mut(&mut x) <<= y;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "ad", fmt = "RSHIFT", args(quiet = false))]
    #[op(code = "b7ad", fmt = "QRSHIFT", args(quiet = true))]
    fn exec_rshift(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_smallint_range(0, 1023));
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *SafeRc::make_mut(&mut x) >>= y;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "ae", fmt = "POW2", args(quiet = false))]
    #[op(code = "b7ae", fmt = "QPOW2", args(quiet = true))]
    fn exec_pow2(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_smallint_range(0, 1023));
        ok!(stack.push_raw_int(SafeRc::new(BigInt::from(1) << y), quiet));
        Ok(0)
    }

    #[op(code = "b0", fmt = "AND", args(quiet = false))]
    #[op(code = "b7b0", fmt = "QAND", args(quiet = true))]
    fn exec_and(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(y)) => {
                *SafeRc::make_mut(&mut x) &= y.as_ref();
                ok!(stack.push_raw_int(x, quiet));
            }
            (Some(x), None) | (None, Some(x)) if x.is_zero() => {
                // NOTE: Spec says that this way is only for `quiet` version,
                //       but the C++ reference implementation does this even for `AND`.
                ok!(stack.push_zero());
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "b1", fmt = "OR", args(quiet = false))]
    #[op(code = "b7b1", fmt = "QOR", args(quiet = true))]
    fn exec_or(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(y)) => {
                *SafeRc::make_mut(&mut x) |= y.as_ref();
                ok!(stack.push_raw_int(x, quiet));
            }
            (Some(x), None) | (None, Some(x))
                if x.sign() == Sign::Minus && x.magnitude().is_one() =>
            {
                // NOTE: Spec says that this way is only for `quiet` version,
                //       but the C++ reference implementation does this even for `OR`.
                ok!(stack.push_int(-1));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "b2", fmt = "XOR", args(quiet = false))]
    #[op(code = "b7b2", fmt = "QXOR", args(quiet = true))]
    fn exec_xor(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(y)) => {
                *SafeRc::make_mut(&mut x) ^= y.as_ref();
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "b3", fmt = "NOT", args(quiet = false))]
    #[op(code = "b7b3", fmt = "QNOT", args(quiet = true))]
    fn exec_not(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                {
                    let x = SafeRc::make_mut(&mut x);
                    *x = !std::mem::take(x);
                }
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "b4yy", fmt = "FITS {y}", args(y = (args & 0xff) + 1, s = true, quiet = false))]
    #[op(code = "b7b4yy", fmt = "QFITS {y}", args(y = (args & 0xff) + 1, s = true, quiet = true))]
    #[op(code = "b5yy", fmt = "UFITS {y}", args(y = (args & 0xff) + 1, s = false, quiet = false))]
    #[op(code = "b7b5yy", fmt = "QUFITS {y}", args(y = (args & 0xff) + 1, s = false, quiet = true))]
    fn exec_fits_tinyint8(st: &mut VmState, y: u32, s: bool, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(x) if x.has_correct_sign(s) && x.bitsize(s) as u32 <= y => {
                ok!(stack.push_raw(x));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "b600", fmt = "FITSX", args(s = true, quiet = false))]
    #[op(code = "b7b600", fmt = "QFITSX", args(s = true, quiet = true))]
    #[op(code = "b601", fmt = "UFITSX", args(s = false, quiet = false))]
    #[op(code = "b7b601", fmt = "QUFITSX", args(s = false, quiet = true))]
    fn exec_fits(st: &mut VmState, s: bool, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_smallint_range(0, 1023));
        match ok!(stack.pop_int_or_nan()) {
            Some(x) if x.has_correct_sign(s) && x.bitsize(s) as u32 <= y => {
                ok!(stack.push_raw(x));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "b602", fmt = "BITSIZE", args(s = true, quiet = false))]
    #[op(code = "b7b602", fmt = "QBITSIZE", args(s = true, quiet = true))]
    #[op(code = "b603", fmt = "UBITSIZE", args(s = false, quiet = false))]
    #[op(code = "b7b603", fmt = "QUBITSIZE", args(s = false, quiet = true))]
    fn exec_bitsize(st: &mut VmState, s: bool, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(x) => {
                if !x.has_correct_sign(s) {
                    vm_ensure!(quiet, IntegerOutOfRange {
                        min: 0,
                        max: isize::MAX,
                        actual: x.to_string(),
                    });
                    ok!(stack.push_nan());
                    return Ok(0);
                }
                ok!(stack.push_int(x.bitsize(s)));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }
}

#[cfg(test)]
mod tests {
    use tracing_test::traced_test;

    use super::*;

    #[test]
    #[traced_test]
    fn shiftops() {
        assert_run_vm!("LSHIFT# 5", [int 1] => [int 32]);
        assert_run_vm!("PUSHPOW2 255 LSHIFT# 10", [] => [int 0], exit_code: 4);
        assert_run_vm!("RSHIFT# 5", [int 32] => [int 1]);
        assert_run_vm!("RSHIFT# 10", [int 1] => [int 0]);

        assert_run_vm!("RSHIFT", [int 32, int 5] => [int 1]);
        assert_run_vm!("RSHIFT", [int 5] => [int 0], exit_code: 2);
        assert_run_vm!("QRSHIFT", [nan, int 5] => [nan]);

        assert_run_vm!("LSHIFT", [int 1, int 5] => [int 32]);
        assert_run_vm!("LSHIFT", [int 1, int 255] => [int (BigInt::from(1) << 255)]);
        assert_run_vm!("LSHIFT", [int 5] => [int 0], exit_code: 2);
        assert_run_vm!("QLSHIFT", [nan, int 5] => [nan]);

        assert_run_vm!("RSHIFT", [int 32, int 5] => [int 1]);
        assert_run_vm!("RSHIFT", [int 5] => [int 0], exit_code: 2);
        assert_run_vm!("QRSHIFT", [nan, int 5] => [nan]);

        assert_run_vm!("POW2", [int 1] => [int 2]);
        assert_run_vm!("POW2", [int 0] => [int 1]);
        assert_run_vm!("QPOW2", [int 1] => [int 2]);
        assert_run_vm!("QPOW2", [int 0] => [int 1]);
        assert_run_vm!("POW2", [] => [int 0], exit_code: 2);
        assert_run_vm!("QPOW2", [] => [int 0], exit_code: 2);
        assert_run_vm!("QPOW2", [int 1024] => [int 0], exit_code: 5);
        assert_run_vm!("POW2", [int 1024] => [int 0], exit_code: 5);
        assert_run_vm!("POW2", [int -1] => [int 0], exit_code: 5);
    }

    #[test]
    #[traced_test]
    fn logicops() {
        assert_run_vm!("AND", [int 0b1101, int 0b0011] => [int 0b0001]);
        assert_run_vm!("AND", [int 0, int 1] => [int 0]);
        assert_run_vm!("AND", [int 1, int 0] => [int 0]);
        assert_run_vm!("AND", [int 0, int 0] => [int 0]);
        assert_run_vm!("AND", [int 0, nan] => [int 0]);
        assert_run_vm!("AND", [nan, int 1] => [int 0], exit_code: 4);
        assert_run_vm!("QAND", [nan, int 1] => [nan]);

        assert_run_vm!("OR", [int 0b1101, int 0b0011] => [int 0b1111]);
        assert_run_vm!("OR", [int 1, int 1] => [int 1]);
        assert_run_vm!("OR", [int 0, int 1] => [int 1]);
        assert_run_vm!("OR", [int 0, int 0] => [int 0]);
        assert_run_vm!("OR", [nan, int -1] => [int -1]);
        assert_run_vm!("OR", [nan, int 1] => [int 0], exit_code: 4);
        assert_run_vm!("QOR", [nan, int 1] => [nan]);

        assert_run_vm!("XOR", [int 1, int 1] => [int 0]);
        assert_run_vm!("XOR", [int 0, int 1] => [int 1]);
        assert_run_vm!("XOR", [int 0, int 0] => [int 0]);
        assert_run_vm!("XOR", [nan, int 1] => [int 0], exit_code: 4);
        assert_run_vm!("QXOR", [nan, int 1] => [nan]);

        assert_run_vm!("NOT", [int 1] => [int -2]);
        assert_run_vm!("NOT", [int 0] => [int -1]);
        assert_run_vm!("NOT", [int 4] => [int -5]);
        assert_run_vm!("NOT", [int -4] => [int 3]);
        assert_run_vm!("NOT", [nan] => [int 0], exit_code: 4);
        assert_run_vm!("QNOT", [nan] => [nan]);
    }

    #[test]
    #[traced_test]
    fn bitops() {
        assert_run_vm!("FITS 8", [int 1] => [int 1]);
        assert_run_vm!("FITSX", [int 1, int 8] => [int 1]);
        assert_run_vm!("FITS 2", [int 1] => [int 1]);
        assert_run_vm!("FITSX", [int 1, int 2] => [int 1]);
        assert_run_vm!("FITS 1", [int 1] => [int 0], exit_code: 4);
        assert_run_vm!("FITSX", [int 1, int 1] => [int 0], exit_code: 4);
        assert_run_vm!("FITS 8", [int 123123] => [int 0], exit_code: 4);
        assert_run_vm!("FITS 256", [int int257_max()] => [int 0], exit_code: 4);
        assert_run_vm!("FITSX", [int int257_max(), int 257] => [int int257_max()]);
        assert_run_vm!("FITSX", [int int257_min(), int 257] => [int int257_min()]);
        assert_run_vm!("FITS 123", [nan] => [int 0], exit_code: 4);
        assert_run_vm!("QUIET FITS 8", [int 1] => [int 1]);
        assert_run_vm!("QUIET FITS 123", [nan] => [nan]);
        assert_run_vm!("QUIET FITS 8", [int 123123] => [nan]);
        assert_run_vm!("QUIET FITSX", [int 1, int 8] => [int 1]);
        assert_run_vm!("QUIET FITSX", [nan, int 123] => [nan]);
        assert_run_vm!("QUIET FITSX", [int 123123, int 8] => [nan]);

        assert_run_vm!("UFITS 8", [int 1] => [int 1]);
        assert_run_vm!("UFITSX", [int 1, int 8] => [int 1]);
        assert_run_vm!("UFITS 2", [int 1] => [int 1]);
        assert_run_vm!("UFITSX", [int 1, int 2] => [int 1]);
        assert_run_vm!("UFITS 1", [int 1] => [int 1]);
        assert_run_vm!("UFITSX", [int 1, int 1] => [int 1]);
        assert_run_vm!("UFITS 8", [int 123123] => [int 0], exit_code: 4);
        assert_run_vm!("UFITS 256", [int int257_max()] => [int int257_max()]);
        assert_run_vm!("UFITSX", [int int257_max(), int 257] => [int int257_max()]);
        assert_run_vm!("UFITSX", [int int257_min(), int 257] => [int 0], exit_code: 4);
        assert_run_vm!("QUIET UFITS 8", [int 1] => [int 1]);
        assert_run_vm!("QUIET UFITS 123", [nan] => [nan]);
        assert_run_vm!("QUIET UFITS 8", [int 123123] => [nan]);
        assert_run_vm!("QUIET UFITS 8", [int -1] => [nan]);
        assert_run_vm!("QUIET UFITSX", [int 1, int 8] => [int 1]);
        assert_run_vm!("QUIET UFITSX", [nan, int 123] => [nan]);
        assert_run_vm!("QUIET UFITSX", [int 123123, int 8] => [nan]);
        assert_run_vm!("QUIET UFITSX", [int -1, int 8] => [nan]);

        assert_run_vm!("BITSIZE", [int 0] => [int 0]);
        assert_run_vm!("UBITSIZE", [int 0] => [int 0]);
        assert_run_vm!("BITSIZE", [int 1] => [int 2]);
        assert_run_vm!("BITSIZE", [int -1] => [int 1]);
        assert_run_vm!("UBITSIZE", [int 1] => [int 1]);
        assert_run_vm!("BITSIZE", [int -2] => [int 2]);
        assert_run_vm!("BITSIZE", [int 3] => [int 3]);
        assert_run_vm!("UBITSIZE", [int 3] => [int 2]);
        assert_run_vm!("BITSIZE", [int -3] => [int 3]);
        assert_run_vm!("BITSIZE", [int 64] => [int 8]);
        assert_run_vm!("BITSIZE", [int -64] => [int 7]);
        assert_run_vm!("BITSIZE", [int int257_max()] => [int 257]);
        assert_run_vm!("BITSIZE", [int int257_min()] => [int 257]);
        assert_run_vm!("UBITSIZE", [int int257_max()] => [int 256]);
        assert_run_vm!("UBITSIZE", [int -1] => [int 0], exit_code: 5);
        assert_run_vm!("UBITSIZE", [int int257_min()] => [int 0], exit_code: 5);
        assert_run_vm!("QUIET BITSIZE", [int 0] => [int 0]);
        assert_run_vm!("QUIET BITSIZE", [nan] => [nan]);
        assert_run_vm!("QUIET UBITSIZE", [int -1] => [nan]);
    }

    fn int257_min() -> BigInt {
        BigInt::from(-1) << 256
    }

    fn int257_max() -> BigInt {
        (BigInt::from(1) << 256) - 1
    }
}
