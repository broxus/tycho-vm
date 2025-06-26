use std::cmp::Ordering;

use num_bigint::{BigInt, Sign};
use num_integer::Integer;
use num_traits::Zero;
#[cfg(feature = "dump")]
use tycho_types::prelude::*;
use tycho_vm_proc::vm_module;

#[cfg(feature = "dump")]
use crate::dispatch::DumpOutput;
use crate::error::VmResult;
#[cfg(feature = "dump")]
use crate::error::{DumpError, DumpResult};
use crate::saferc::SafeRc;
use crate::state::VmState;

pub struct ArithOps;

#[vm_module]
impl ArithOps {
    // === Int constants ===

    #[op(code = "7x", fmt = "PUSHINT {x}", args(x = ((args as i32 + 5) & 0xf) - 5))]
    #[op(code = "80xx", fmt = "PUSHINT {x}", args(x = args as i8 as i32))]
    #[op(code = "81xxxx", fmt = "PUSHINT {x}", args(x = args as i16 as i32))]
    fn exec_push_tinyint4(st: &mut VmState, x: i32) -> VmResult<i32> {
        ok!(SafeRc::make_mut(&mut st.stack).push_int(x));
        Ok(0)
    }

    #[op_ext_range(
        code_min = 0x82 << 5,
        code_max = (0x82 << 5) + 31,
        total_bits = 13,
        dump_with = dump_push_int
    )]
    fn exec_push_int(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let l = (args as u16 & 0b11111) + 2;
        let value_len = 3 + l * 8;
        vm_ensure!(
            st.code.range().has_remaining(bits + value_len, 0),
            InvalidOpcode
        );
        st.code.range_mut().skip_first(bits, 0).ok();

        let mut cs = st.code.apply();
        let int = cs.load_bigint(value_len, true)?;
        st.code.set_range(cs.range());

        vm_log_op!("PUSHINT {int}");

        ok!(SafeRc::make_mut(&mut st.stack).push_int(int));
        Ok(0)
    }

    #[cfg(feature = "dump")]
    fn dump_push_int(
        code: &mut CellSlice<'_>,
        args: u32,
        bits: u16,
        f: &mut dyn DumpOutput,
    ) -> DumpResult {
        let l = (args as u16 & 0b11111) + 2;
        let value_len = 3 + l * 8;

        if !code.has_remaining(bits + value_len, 0) {
            return Err(DumpError::InvalidOpcode);
        }
        code.skip_first(bits, 0)?;

        let int = code.load_bigint(value_len, true)?;
        f.record_opcode(&format_args!("PUSHINT {int}"))
    }

    #[op(code = "83xx @ ..83ff", fmt = "PUSHPOW2 {x}", args(x = (args & 0xff) + 1))]
    pub fn exec_push_pow2(st: &mut VmState, x: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.push_int(BigInt::from(1) << x));
        Ok(0)
    }

    #[op(code = "83ff", fmt = "PUSHNAN")]
    fn exec_push_nan(st: &mut VmState) -> VmResult<i32> {
        ok!(SafeRc::make_mut(&mut st.stack).push_nan());
        Ok(0)
    }

    #[op(code = "84xx", fmt = "PUSHPOW2DEC {x}", args(x = (args & 0xff) + 1))]
    fn exec_push_pow2dec(st: &mut VmState, x: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut value = BigInt::from(1) << x;
        value -= 1;
        ok!(stack.push_int(value));
        Ok(0)
    }

    #[op(code = "85xx", fmt = "PUSHNEGPOW2 {x}", args(x = (args & 0xff) + 1))]
    fn exec_push_negpow2(st: &mut VmState, x: u32) -> VmResult<i32> {
        ok!(SafeRc::make_mut(&mut st.stack).push_int(-(BigInt::from(1) << x)));
        Ok(0)
    }

    // === Simple math instructions ===
    #[op(code = "a0", fmt = "ADD", args(quiet = false))]
    #[op(code = "b7a0", fmt = "QADD", args(quiet = true))]
    fn exec_add(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(y)) => {
                *SafeRc::make_mut(&mut x) += y.as_ref();
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "a1", fmt = "SUB", args(quiet = false))]
    #[op(code = "b7a1", fmt = "QSUB", args(quiet = true))]
    fn exec_sub(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(y)) => {
                *SafeRc::make_mut(&mut x) -= y.as_ref();
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "a2", fmt = "SUBR", args(quiet = false))]
    #[op(code = "b7a2", fmt = "QSUBR", args(quiet = true))]
    fn exec_subr(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(x), Some(mut y)) => {
                *SafeRc::make_mut(&mut y) -= x.as_ref();
                ok!(stack.push_raw_int(y, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "a3", fmt = "NEGATE", args(quiet = false))]
    #[op(code = "b7a3", fmt = "QNEGATE", args(quiet = true))]
    fn exec_negate(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                {
                    let x = SafeRc::make_mut(&mut x);
                    *x = -std::mem::take(x);
                }
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "a4", fmt = "INC", args(quiet = false))]
    #[op(code = "b7a4", fmt = "QINC", args(quiet = true))]
    fn exec_inc(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *SafeRc::make_mut(&mut x) += 1;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "a5", fmt = "DEC", args(quiet = false))]
    #[op(code = "b7a5", fmt = "QDEC", args(quiet = true))]
    fn exec_dec(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *SafeRc::make_mut(&mut x) -= 1;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "a6yy", fmt = "ADDINT {y}", args(y = args as i8, quiet = false))]
    #[op(code = "b7a6yy", fmt = "QADDINT {y}", args(y = args as i8, quiet = true))]
    fn exec_addint(st: &mut VmState, y: i8, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *SafeRc::make_mut(&mut x) += y;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "a7yy", fmt = "MULINT {y}", args(y = args as i8, quiet = false))]
    #[op(code = "b7a7yy", fmt = "QMULINT {y}", args(y = args as i8, quiet = true))]
    fn exec_mulint(st: &mut VmState, y: i8, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *SafeRc::make_mut(&mut x) *= y;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "a8", fmt = "MUL", args(quiet = false))]
    #[op(code = "b7a8", fmt = "QMUL", args(quiet = true))]
    fn exec_mul(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(y)) => {
                *SafeRc::make_mut(&mut x) *= y.as_ref();
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    // === Division instructions ===
    #[op(code = "a90m", fmt = DumpDivmod(m), args(quiet = false))]
    #[op(code = "b7a90m", fmt = DumpDivmod(m), args(quiet = true))]
    fn exec_divmod(st: &mut VmState, m: u32, quiet: bool) -> VmResult<i32> {
        enum Operation {
            Div,
            Mod,
            Divmod,
        }

        let round_mode = ok!(RoundMode::from_args(m & 0b11));
        let mut add = false;
        let operation = match (m >> 2) & 0b11 {
            0 if st.version.is_ton(4..) => {
                add = true;
                Operation::Divmod
            }
            1 => Operation::Div,
            2 => Operation::Mod,
            3 => Operation::Divmod,
            _ => vm_bail!(InvalidOpcode),
        };

        let stack = SafeRc::make_mut(&mut st.stack);

        let y = ok!(stack.pop_int_or_nan());
        let w = if add {
            ok!(stack.pop_int_or_nan())
        } else {
            None
        };
        let x = ok!(stack.pop_int_or_nan());

        match (x, y) {
            (Some(mut x), Some(y)) if !y.is_zero() => match operation {
                Operation::Div => {
                    let res = int_div(&x, &y, round_mode);
                    ok!(stack.push_raw_int(update_or_new_rc(x, res), quiet));
                }
                Operation::Mod => {
                    let res = int_mod(&x, &y, round_mode);
                    ok!(stack.push_raw_int(update_or_new_rc(x, res), quiet));
                }
                Operation::Divmod => {
                    if add {
                        match w {
                            Some(w) => *SafeRc::make_mut(&mut x) += w.as_ref(),
                            None if quiet => {
                                ok!(stack.push_nan());
                                ok!(stack.push_nan());
                                return Ok(0);
                            }
                            None => vm_bail!(IntegerOverflow),
                        }
                    }

                    let (q, r) = int_divmod(&x, &y, round_mode);
                    ok!(stack.push_raw_int(update_or_new_rc(x, q), quiet));
                    ok!(stack.push_raw_int(update_or_new_rc(y, r), quiet));
                }
            },
            _ if quiet => {
                ok!(stack.push_nan());
                if let Operation::Divmod = operation {
                    ok!(stack.push_nan());
                }
            }
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "a92m", fmt = DumpShr(m, false), args(imm = false, quiet = false))]
    #[op(code = "a93mmm", fmt = DumpShr(m, true), args(imm = true, quiet = false))]
    #[op(code = "b7a92m", fmt = ("Q{}", DumpShr(m, false)), args(imm = false, quiet = true))]
    fn exec_shrmod(st: &mut VmState, mut m: u32, imm: bool, quiet: bool) -> VmResult<i32> {
        enum Operation {
            RShift,
            ModPow2,
            RShiftMod,
        }

        let y = if imm {
            let y = (m & 0xff) + 1;
            m >>= 8;
            Some(y)
        } else {
            None
        };

        let mut round_mode = ok!(RoundMode::from_args(m & 0b11));
        let mut add = false;
        let operation = match (m >> 2) & 0b11 {
            0 if st.version.is_ton(4..) => {
                add = true;
                Operation::RShiftMod
            }
            1 => Operation::RShift,
            2 => Operation::ModPow2,
            3 => Operation::RShiftMod,
            _ => vm_bail!(InvalidOpcode),
        };

        let stack = SafeRc::make_mut(&mut st.stack);
        let y = match y {
            Some(y) => y,
            None => ok!(stack.pop_smallint_range(0, 256)),
        };

        if y == 0 {
            round_mode = RoundMode::Floor;
        }
        let w = if add {
            ok!(stack.pop_int_or_nan())
        } else {
            None
        };

        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => match operation {
                Operation::RShift => {
                    let res = int_rshift(&x, y, round_mode);
                    ok!(stack.push_raw_int(update_or_new_rc(x, res), quiet));
                }
                Operation::ModPow2 => {
                    let res = int_mod_pow2(&x, y, round_mode);
                    ok!(stack.push_raw_int(update_or_new_rc(x, res), quiet));
                }
                Operation::RShiftMod => {
                    if add {
                        match w {
                            Some(w) => *SafeRc::make_mut(&mut x) += w.as_ref(),
                            None if quiet => {
                                ok!(stack.push_nan());
                                ok!(stack.push_nan());
                                return Ok(0);
                            }
                            None => vm_bail!(IntegerOverflow),
                        }
                    }

                    let (q, r) = int_rshiftmod(&x, y, round_mode);
                    ok!(stack.push_raw_int(update_or_new_rc(x, q), quiet));
                    ok!(stack.push_raw_int(SafeRc::new(r), quiet));
                }
            },
            _ if quiet => {
                ok!(stack.push_nan());
                if let Operation::RShiftMod = operation {
                    ok!(stack.push_nan());
                }
            }
            _ => vm_bail!(IntegerOverflow),
        }

        Ok(0)
    }

    #[op(code = "a98m", fmt = ("MUL{}", DumpDivmod(m)), args(quiet = false))]
    #[op(code = "b7a98m", fmt = ("QMUL{}", DumpDivmod(m)), args(quiet = true))]
    fn exec_muldivmod(st: &mut VmState, m: u32, quiet: bool) -> VmResult<i32> {
        #[allow(clippy::enum_variant_names)]
        enum Operation {
            MulDiv,
            MulMod,
            MulDivMod,
        }

        let round_mode = ok!(RoundMode::from_args(m & 0b11));
        let mut add = false;
        let operation = match (m >> 2) & 0b11 {
            0 if st.version.is_ton(4..) => {
                add = true;
                Operation::MulDivMod
            }
            1 => Operation::MulDiv,
            2 => Operation::MulMod,
            3 => Operation::MulDivMod,
            _ => vm_bail!(InvalidOpcode),
        };

        let stack = SafeRc::make_mut(&mut st.stack);

        let z = ok!(stack.pop_int_or_nan());
        let w = if add {
            ok!(stack.pop_int_or_nan())
        } else {
            None
        };
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());

        match (x, y, z) {
            (Some(mut x), Some(y), Some(z)) if !z.is_zero() => {
                *SafeRc::make_mut(&mut x) *= y.as_ref();

                match operation {
                    Operation::MulDiv => {
                        let res = int_div(&x, &z, round_mode);
                        ok!(stack.push_raw_int(update_or_new_rc(x, res), quiet));
                    }
                    Operation::MulMod => {
                        let res = int_mod(&x, &z, round_mode);
                        ok!(stack.push_raw_int(update_or_new_rc(x, res), quiet));
                    }
                    Operation::MulDivMod => {
                        if add {
                            match w {
                                Some(w) => *SafeRc::make_mut(&mut x) += w.as_ref(),
                                None if quiet => {
                                    ok!(stack.push_nan());
                                    ok!(stack.push_nan());
                                    return Ok(0);
                                }
                                None => vm_bail!(IntegerOverflow),
                            }
                        }

                        let (q, r) = int_divmod(&x, &z, round_mode);
                        ok!(stack.push_raw_int(update_or_new_rc(x, q), quiet));
                        ok!(stack.push_raw_int(update_or_new_rc(y, r), quiet));
                    }
                }
            }
            _ if quiet => {
                ok!(stack.push_nan());
                if let Operation::MulDivMod = operation {
                    ok!(stack.push_nan());
                }
            }
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "a9am", fmt = ("MUL{}", DumpShr(m, false)), args(imm = false, quiet = false))]
    #[op(code = "a9bmmm", fmt = ("MUL{}", DumpShr(m, true)), args(imm = true, quiet = false))]
    #[op(code = "b7a9am", fmt = ("QMUL{}", DumpShr(m, false)), args(imm = false, quiet = true))]
    fn exec_mulshrmod(st: &mut VmState, mut m: u32, imm: bool, quiet: bool) -> VmResult<i32> {
        enum Operation {
            MulRShift,
            MulModPow2,
            MulRShiftMod,
        }

        let z = if imm {
            let z = (m & 0xff) + 1;
            m >>= 8;
            Some(z)
        } else {
            None
        };

        let mut round_mode = ok!(RoundMode::from_args(m & 0b11));
        let mut add = false;
        let operation = match (m >> 2) & 0b11 {
            0 if st.version.is_ton(4..) => {
                add = true;
                Operation::MulRShiftMod
            }
            1 => Operation::MulRShift,
            2 => Operation::MulModPow2,
            3 => Operation::MulRShiftMod,
            _ => vm_bail!(InvalidOpcode),
        };

        let stack = SafeRc::make_mut(&mut st.stack);
        let z = match z {
            Some(z) => z,
            None => ok!(stack.pop_smallint_range(0, 256)),
        };

        if z == 0 {
            round_mode = RoundMode::Floor;
        }
        let w = if add {
            ok!(stack.pop_int_or_nan())
        } else {
            None
        };

        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(y)) => {
                *SafeRc::make_mut(&mut x) *= y.as_ref();

                match operation {
                    Operation::MulRShift => {
                        let res = int_rshift(&x, z, round_mode);
                        ok!(stack.push_raw_int(update_or_new_rc(x, res), quiet));
                    }
                    Operation::MulModPow2 => {
                        let res = int_mod_pow2(&x, z, round_mode);
                        ok!(stack.push_raw_int(update_or_new_rc(x, res), quiet));
                    }
                    Operation::MulRShiftMod => {
                        if add {
                            match w {
                                Some(w) => *SafeRc::make_mut(&mut x) += w.as_ref(),
                                None if quiet => {
                                    ok!(stack.push_nan());
                                    ok!(stack.push_nan());
                                    return Ok(0);
                                }
                                None => vm_bail!(IntegerOverflow),
                            }
                        }

                        let (q, r) = int_rshiftmod(&x, z, round_mode);
                        ok!(stack.push_raw_int(update_or_new_rc(x, q), quiet));
                        ok!(stack.push_raw_int(SafeRc::new(r), quiet));
                    }
                }
            }
            _ if quiet => {
                ok!(stack.push_nan());
                if let Operation::MulRShiftMod = operation {
                    ok!(stack.push_nan());
                }
            }
            _ => vm_bail!(IntegerOverflow),
        }

        Ok(0)
    }

    #[op(code = "a9cm", fmt = DumpShl(m, false), args(imm = false, quiet = false))]
    #[op(code = "a9dmmm", fmt = DumpShl(m, true), args(imm = true, quiet = false))]
    #[op(code = "b7a9cm", fmt = ("Q{}", DumpShl(m, false)), args(imm = false, quiet = true))]
    fn exec_shldivmod(st: &mut VmState, mut m: u32, imm: bool, quiet: bool) -> VmResult<i32> {
        enum Operation {
            Div,
            Mod,
            Divmod,
        }

        let z = if imm {
            let z = (m & 0xff) + 1;
            m >>= 8;
            Some(z)
        } else {
            None
        };

        let round_mode = ok!(RoundMode::from_args(m & 0b11));
        let mut add = false;
        let operation = match (m >> 2) & 0b11 {
            0 if st.version.is_ton(4..) => {
                add = true;
                Operation::Divmod
            }
            1 => Operation::Div,
            2 => Operation::Mod,
            3 => Operation::Divmod,
            _ => vm_bail!(InvalidOpcode),
        };

        let stack = SafeRc::make_mut(&mut st.stack);
        let z = match z {
            Some(z) => z,
            None => ok!(stack.pop_smallint_range(0, 256)),
        };

        let y = ok!(stack.pop_int_or_nan());
        let w = if add {
            ok!(stack.pop_int_or_nan())
        } else {
            None
        };
        let x = ok!(stack.pop_int_or_nan());

        match (x, y) {
            (Some(mut x), Some(y)) if !y.is_zero() => {
                *SafeRc::make_mut(&mut x) <<= z;

                match operation {
                    Operation::Div => {
                        let res = int_div(&x, &y, round_mode);
                        ok!(stack.push_raw_int(update_or_new_rc(x, res), quiet));
                    }
                    Operation::Mod => {
                        let res = int_mod(&x, &y, round_mode);
                        ok!(stack.push_raw_int(update_or_new_rc(x, res), quiet));
                    }
                    Operation::Divmod => {
                        if add {
                            match w {
                                Some(w) => *SafeRc::make_mut(&mut x) += w.as_ref(),
                                None if quiet => {
                                    ok!(stack.push_nan());
                                    ok!(stack.push_nan());
                                    return Ok(0);
                                }
                                None => vm_bail!(IntegerOverflow),
                            }
                        }

                        let (q, r) = int_divmod(&x, &y, round_mode);
                        ok!(stack.push_raw_int(update_or_new_rc(x, q), quiet));
                        ok!(stack.push_raw_int(update_or_new_rc(y, r), quiet));
                    }
                }
            }
            _ if quiet => {
                ok!(stack.push_nan());
                if let Operation::Divmod = operation {
                    ok!(stack.push_nan());
                }
            }
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    // === Other opcodes ===

    #[op(code = "b608", fmt = "MIN", args(mn = true, mx = false, q = false))]
    #[op(code = "b609", fmt = "MAX", args(mn = false, mx = true, q = false))]
    #[op(code = "b60a", fmt = "MINMAX", args(mn = true, mx = true, q = false))]
    #[op(code = "b7b608", fmt = "QMIN", args(mn = true, mx = false, q = true))]
    #[op(code = "b7b609", fmt = "QMAX", args(mn = false, mx = true, q = true))]
    #[op(code = "b7b60a", fmt = "QMINMAX", args(mn = true, mx = true, q = true))]
    fn exec_minmax(st: &mut VmState, mn: bool, mx: bool, q: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_int_or_nan());
        let y = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(mut y)) => {
                if x > y {
                    std::mem::swap(&mut x, &mut y);
                }
                if mn {
                    ok!(stack.push_raw(x));
                }
                if mx {
                    ok!(stack.push_raw(y));
                }
            }
            _ if q => {
                if mn {
                    ok!(stack.push_nan());
                }
                if mx {
                    ok!(stack.push_nan());
                }
            }
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[op(code = "b60b", fmt = "ABS", args(quiet = false))]
    #[op(code = "b7b60b", fmt = "QABS", args(quiet = true))]
    fn exec_abs(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                if x.sign() == Sign::Minus {
                    let x = SafeRc::make_mut(&mut x);
                    *x = -std::mem::take(x);
                }
                ok!(stack.push_raw_int(x, quiet));
            }
            None if quiet => ok!(stack.push_nan()),
            None => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }
}

struct DumpDivmod(u32);

impl std::fmt::Display for DumpDivmod {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match (self.0 >> 2) & 0b11 {
            0 => "ADDDIVMOD",
            1 => "DIV",
            2 => "MOD",
            3 => "DIVMOD",
            _ => return f.write_str("DIV/MOD"),
        })?;
        f.write_str(match self.0 & 0b11 {
            1 => "R",
            2 => "C",
            _ => "",
        })
    }
}

struct DumpShr(u32, bool);

impl std::fmt::Display for DumpShr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut m = self.0;
        let y = if self.1 {
            let y = (m & 0xff) + 1;
            m >>= 8;
            Some(y)
        } else {
            None
        };

        let (start, end) = match (m >> 2) & 0b11 {
            0 => ("ADDRSHIFT", "MOD"),
            1 => ("RSHIFT", ""),
            2 => ("MODPOW2", ""),
            3 => ("RSHIFT", "MOD"),
            _ => return f.write_str("SHR/MOD"),
        };
        let mode = match m & 0b11 {
            1 => "R",
            2 => "C",
            _ => "",
        };

        if let Some(y) = y {
            write!(f, "{start}{mode}#{end} {y}")
        } else {
            write!(f, "{start}{end}{mode}")
        }
    }
}

struct DumpShl(u32, bool);

impl std::fmt::Display for DumpShl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut m = self.0;
        let y = if self.1 {
            let y = (m & 0xff) + 1;
            m >>= 8;
            Some(y)
        } else {
            None
        };

        let op = match (m >> 2) & 0b11 {
            0 => "ADDDIVMOD",
            1 => "DIV",
            2 => "MOD",
            3 => "DIVMOD",
            _ => return f.write_str("SHLDIV/MOD"),
        };
        let mode = match m & 0b11 {
            1 => "R",
            2 => "C",
            _ => "",
        };

        if let Some(y) = y {
            write!(f, "LSHIFT#{op}{mode} {y}")
        } else {
            write!(f, "LSHIFT{op}{mode}")
        }
    }
}

enum RoundMode {
    Floor = 0,
    Nearest = 1,
    Ceiling = 2,
}

impl RoundMode {
    fn from_args(args: u32) -> VmResult<Self> {
        Ok(match args {
            0 => Self::Floor,
            1 => Self::Nearest,
            2 => Self::Ceiling,
            _ => vm_bail!(InvalidOpcode),
        })
    }
}

fn int_div(x: &BigInt, y: &BigInt, round_mode: RoundMode) -> BigInt {
    match round_mode {
        RoundMode::Floor => x.div_floor(y),
        RoundMode::Nearest => {
            let (mut q, r) = x.div_rem(y);
            if nearest_rounding_required(&r, x, y) {
                if x.sign() == y.sign() {
                    q += 1;
                } else {
                    q -= 1;
                }
            }
            q
        }
        RoundMode::Ceiling => {
            let (mut q, r) = x.div_rem(y);
            if ceil_rounding_required(&r, y) {
                if x.sign() == y.sign() {
                    q += 1;
                } else {
                    q -= 1;
                }
            }
            q
        }
    }
}

fn int_mod(x: &BigInt, y: &BigInt, round_mode: RoundMode) -> BigInt {
    match round_mode {
        RoundMode::Floor => x.mod_floor(y),
        RoundMode::Nearest => {
            let (_, mut r) = x.div_rem(y);
            if nearest_rounding_required(&r, x, y) {
                if r.sign() == y.sign() {
                    r -= y;
                } else {
                    r += y;
                }
            }
            r
        }
        RoundMode::Ceiling => {
            let (_, mut r) = x.div_rem(y);
            if ceil_rounding_required(&r, y) {
                r -= y;
            }
            r
        }
    }
}

fn int_divmod(x: &BigInt, y: &BigInt, round_mode: RoundMode) -> (BigInt, BigInt) {
    match round_mode {
        RoundMode::Floor => x.div_mod_floor(y),
        RoundMode::Nearest => {
            let (mut q, mut r) = x.div_rem(y);
            if nearest_rounding_required(&r, x, y) {
                if x.sign() == y.sign() {
                    q += 1;
                } else {
                    q -= 1;
                }
                if r.sign() == y.sign() {
                    r -= y;
                } else {
                    r += y;
                }
            }
            (q, r)
        }
        RoundMode::Ceiling => {
            let (mut q, mut r) = x.div_rem(y);
            if ceil_rounding_required(&r, y) {
                r -= y;
                if x.sign() == y.sign() {
                    q += 1;
                } else {
                    q -= 1;
                }
            }
            (q, r)
        }
    }
}

fn int_rshift(x: &BigInt, y: u32, round_mode: RoundMode) -> BigInt {
    match round_mode {
        RoundMode::Floor => x >> y,
        // TODO: Optimize
        RoundMode::Nearest | RoundMode::Ceiling => {
            let pow = BigInt::from(1) << y;
            int_div(x, &pow, round_mode)
        }
    }
}

// TODO: Optimize
fn int_mod_pow2(x: &BigInt, y: u32, round_mode: RoundMode) -> BigInt {
    let mut pow2 = BigInt::from(1) << y;
    match round_mode {
        RoundMode::Floor => {
            pow2 -= 1;
            x & pow2
        }
        RoundMode::Nearest | RoundMode::Ceiling => int_mod(x, &pow2, round_mode),
    }
}

// TODO: Optimize
fn int_rshiftmod(x: &BigInt, y: u32, round_mode: RoundMode) -> (BigInt, BigInt) {
    let mut pow2 = BigInt::from(1) << y;
    match round_mode {
        RoundMode::Floor => {
            pow2 -= 1;
            (x >> y, x & pow2)
        }
        RoundMode::Nearest | RoundMode::Ceiling => int_divmod(x, &pow2, round_mode),
    }
}

fn nearest_rounding_required(r: &BigInt, x: &BigInt, y: &BigInt) -> bool {
    if r.is_zero() {
        return false;
    }

    let r_x2: BigInt = r << 1;
    match r_x2.magnitude().cmp(y.magnitude()) {
        Ordering::Greater => true,
        Ordering::Equal if x.sign() == y.sign() => true,
        _ => false,
    }
}

fn ceil_rounding_required(r: &BigInt, y: &BigInt) -> bool {
    !r.is_zero() && r.sign() == y.sign()
}

fn update_or_new_rc(mut rc: SafeRc<BigInt>, value: BigInt) -> SafeRc<BigInt> {
    match SafeRc::get_mut(&mut rc) {
        None => SafeRc::new(value),
        Some(x) => {
            *x = value;
            rc
        }
    }
}

#[cfg(test)]
mod tests {
    use tracing_test::traced_test;

    use super::*;

    #[test]
    #[traced_test]
    fn op_pushconst() {
        assert_run_vm!("PUSHINT 1", [] => [int 1]);
        assert_run_vm!("PUSHINT 127", [] => [int 127]);
        assert_run_vm!("PUSHINT 32767", [] => [int 32767]);
        assert_run_vm!("PUSHINT 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF", [] => [int 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFi128]);
        assert_run_vm!("PUSHINT 85143", [] => [int 85143]);
        assert_run_vm!("PUSHPOW2 1", [] => [int 2]);
        assert_run_vm!("PUSHPOW2 10", [] => [int (1 << 10)]);
        assert_run_vm!("PUSHPOW2 255", [] => [int (BigInt::from(1) << 255)]);
        assert_run_vm!("PUSHNAN", [] => [nan]);
        assert_run_vm!("PUSHPOW2DEC 1", [] => [int 1]);
        assert_run_vm!("PUSHPOW2DEC 10", [] => [int (1 << 10) - 1]);
        assert_run_vm!("PUSHPOW2DEC 256", [] => [int (BigInt::from(1) << 256) - 1]);
        assert_run_vm!("PUSHNEGPOW2 1", [] => [int -2]);
        assert_run_vm!("PUSHNEGPOW2 10", [] => [int (-1 << 10)]);
        assert_run_vm!("PUSHNEGPOW2 255", [] => [int (BigInt::from(-1) << 255)]);
    }

    #[test]
    #[traced_test]
    fn op_simple_math() {
        // === ADD/ADDINT/QADD/QADDINT ===

        // pos
        assert_run_vm!("ADD", [int 2, int 5] => [int 7]);
        assert_run_vm!("ADD", [int -5, int 5] => [int 0]);
        assert_run_vm!("ADDINT 2", [int 5] => [int 7]);
        assert_run_vm!("ADDINT -5", [int 5] => [int 0]);
        // neg
        assert_run_vm!("ADD", [] => [int 0], exit_code: 2);
        assert_run_vm!("ADDINT 123", [] => [int 0], exit_code: 2);
        assert_run_vm!("ADD", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("ADD", [null, int 5] => [int 0], exit_code: 7);
        assert_run_vm!("ADDINT 5", [nan] => [int 0], exit_code: 4);
        assert_run_vm!("ADD", [int int257_max(), int 1] => [int 0], exit_code: 4);
        assert_run_vm!("ADDINT 1", [int int257_max()] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("QADD", [int 2, int 5] => [int 7]);
        assert_run_vm!("QADD", [int -5, int 5] => [int 0]);
        assert_run_vm!("QADD", [int int257_max(), int 0] => [int int257_max()]);
        assert_run_vm!("QADD", [int int257_max() + 1, int 1] => [nan]);
        assert_run_vm!("QADD", [int int257_max() + 1, int 0] => [nan]);
        assert_run_vm!("QADD", [nan, int 5] => [nan]);
        assert_run_vm!("QADDINT 2", [int 5] => [int 7]);
        assert_run_vm!("QADDINT -5", [int 5] => [int 0]);
        assert_run_vm!("QADDINT 2", [nan] => [nan]);
        assert_run_vm!("QADDINT -5", [int 5] => [int 0]);
        // neg
        assert_run_vm!("QADD", [] => [int 0], exit_code: 2);
        assert_run_vm!("QADD", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("QADDINT 0", [] => [int 0], exit_code: 2);

        // === SUB/SUBINT/QSUB ===

        // pos
        assert_run_vm!("SUB", [int 2, int 5] => [int -3]);
        assert_run_vm!("SUB", [int -5, int 5] => [int -10]);
        assert_run_vm!("SUBINT 2", [int 5] => [int 3]);
        assert_run_vm!("SUBINT -5", [int 5] => [int 10]);
        // neg
        assert_run_vm!("SUB", [int -5, null] => [int 0], exit_code: 7);
        assert_run_vm!("SUB", [int int257_min(), int 1] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("QSUB", [int 2, int 5] => [int -3]);
        assert_run_vm!("QSUB", [int -5, int 5] => [int -10]);
        assert_run_vm!("QSUB", [int int257_max(), int 0] => [int int257_max()]);
        assert_run_vm!("QSUB", [int int257_min() + 1, int 1] => [int int257_min()]);
        assert_run_vm!("QSUB", [int int257_min(), int 1] => [nan]);
        assert_run_vm!("QSUB", [nan, int 5] => [nan]);
        // neg
        assert_run_vm!("QSUB", [] => [int 0], exit_code: 2);
        assert_run_vm!("QSUB", [int 123] => [int 0], exit_code: 2);

        // === SUBR/QSUBR ===

        // pos
        assert_run_vm!("SUBR", [int 5, int 2] => [int -3]);
        assert_run_vm!("SUBR", [int 5, int -5] => [int -10]);
        // neg
        assert_run_vm!("SUBR", [] => [int 0], exit_code: 2);
        assert_run_vm!("SUBR", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("SUBR", [int 5, null] => [int 0], exit_code: 7);
        assert_run_vm!("SUBR", [int -1, int int257_max()] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("QSUBR", [int 5, int 2] => [int -3]);
        assert_run_vm!("QSUBR", [int 5, int -5] => [int -10]);
        assert_run_vm!("QSUBR", [int 0, int int257_max()] => [int int257_max()]);
        assert_run_vm!("QSUBR", [int 1, int int257_min() + 1] => [int int257_min()]);
        assert_run_vm!("QSUBR", [int 1, int int257_min()] => [nan]);
        assert_run_vm!("QSUBR", [int 5, nan] => [nan]);
        // neg
        assert_run_vm!("QSUBR", [] => [int 0], exit_code: 2);
        assert_run_vm!("QSUBR", [int 123] => [int 0], exit_code: 2);

        // === NEGATE/QNEGATE ===

        // pos
        assert_run_vm!("NEGATE", [int 123] => [int -123]);
        assert_run_vm!("NEGATE", [int 0] => [int 0]);
        assert_run_vm!("NEGATE", [int -10] => [int 10]);
        assert_run_vm!("NEGATE", [int int257_min() + 1] => [int int257_max()]);
        assert_run_vm!("NEGATE", [int int257_max()] => [int int257_min() + 1]);
        // neg
        assert_run_vm!("NEGATE", [] => [int 0], exit_code: 2);
        assert_run_vm!("NEGATE", [nan] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("QNEGATE", [int 123] => [int -123]);
        assert_run_vm!("QNEGATE", [nan] => [nan]);
        // neg
        assert_run_vm!("QNEGATE", [] => [int 0], exit_code: 2);
        assert_run_vm!("QNEGATE", [null] => [int 0], exit_code: 7);

        // === INC/QINC ===

        // pos
        assert_run_vm!("INC", [int 10] => [int 11]);
        assert_run_vm!("INC", [int -1] => [int 0]);
        assert_run_vm!("INC", [int int257_max() - 1] => [int int257_max()]);
        assert_run_vm!("INC", [int int257_min()] => [int int257_min() + 1]);
        // neg
        assert_run_vm!("INC", [] => [int 0], exit_code: 2);
        assert_run_vm!("INC", [nan] => [int 0], exit_code: 4);
        assert_run_vm!("INC", [int int257_max()] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("QINC", [int 10] => [int 11]);
        assert_run_vm!("QINC", [int -1] => [int 0]);
        assert_run_vm!("QINC", [int int257_max() - 1] => [int int257_max()]);
        assert_run_vm!("QINC", [int int257_min()] => [int int257_min() + 1]);
        assert_run_vm!("QINC", [nan] => [nan]);
        assert_run_vm!("QINC", [int int257_max()] => [nan]);
        // neg
        assert_run_vm!("QINC", [] => [int 0], exit_code: 2);

        // === DEC/QDEC ===

        // pos
        assert_run_vm!("DEC", [int 10] => [int 9]);
        assert_run_vm!("DEC", [int 0] => [int -1]);
        assert_run_vm!("DEC", [int int257_min() + 1] => [int int257_min()]);
        assert_run_vm!("DEC", [int int257_max()] => [int int257_max() - 1]);
        // neg
        assert_run_vm!("DEC", [] => [int 0], exit_code: 2);
        assert_run_vm!("DEC", [nan] => [int 0], exit_code: 4);
        assert_run_vm!("DEC", [int int257_min()] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("QDEC", [int 10] => [int 9]);
        assert_run_vm!("QDEC", [int 0] => [int -1]);
        assert_run_vm!("QDEC", [int int257_min() + 1] => [int int257_min()]);
        assert_run_vm!("QDEC", [int int257_max()] => [int int257_max() - 1]);
        assert_run_vm!("QDEC", [nan] => [nan]);
        assert_run_vm!("QDEC", [int int257_min()] => [nan]);
        // neg
        assert_run_vm!("QDEC", [] => [int 0], exit_code: 2);

        // === MUL/QMUL

        // pos
        assert_run_vm!("MUL", [int 123, int 0] => [int 0]);
        assert_run_vm!("MUL", [int 123, int 1] => [int 123]);
        assert_run_vm!("MUL", [int 123, int 123] => [int 123 * 123]);
        assert_run_vm!("MUL", [int -123, int 0] => [int 0]);
        assert_run_vm!("MUL", [int -123, int 1] => [int -123]);
        assert_run_vm!("MULINT 0", [int -123] => [int 0]);
        assert_run_vm!("MULINT 1", [int -123] => [int -123]);
        assert_run_vm!("MUL", [int -123, int 123] => [int -123 * 123]);
        assert_run_vm!("MULINT 123", [int -123] => [int -123 * 123]);
        assert_run_vm!("MUL", [int -123, int -123] => [int 123 * 123]);
        assert_run_vm!("MULINT -123", [int -123] => [int 123 * 123]);
        assert_run_vm!("MUL", [int int257_min(), int 0] => [int 0]);
        assert_run_vm!("MUL", [int int257_max(), int 0] => [int 0]);
        assert_run_vm!("MUL", [int int257_min(), int 1] => [int int257_min()]);
        assert_run_vm!("MUL", [int int257_max(), int 1] => [int int257_max()]);
        assert_run_vm!("MUL", [int int257_max(), int -1] => [int int257_min() + 1]);
        // neg
        assert_run_vm!("MUL", [] => [int 0], exit_code: 2);
        assert_run_vm!("MUL", [int 2] => [int 0], exit_code: 2);
        assert_run_vm!("MUL", [int 2, nan] => [int 0], exit_code: 4);
        assert_run_vm!("MUL", [nan, int 2] => [int 0], exit_code: 4);
        assert_run_vm!("MUL", [int 2, null] => [int 0], exit_code: 7);
        assert_run_vm!("MUL", [int int257_min(), int -1] => [int 0], exit_code: 4);
        assert_run_vm!("MUL", [int int257_min() / 2, int -2] => [int 0], exit_code: 4);
        assert_run_vm!("MUL", [int int257_max(), int 2] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("QMUL", [int 123, int 0] => [int 0]);
        assert_run_vm!("QMUL", [int 123, int 1] => [int 123]);
        assert_run_vm!("QMUL", [int 123, int 123] => [int 123 * 123]);
        assert_run_vm!("QMUL", [int -123, int 0] => [int 0]);
        assert_run_vm!("QMUL", [int -123, int 1] => [int -123]);
        assert_run_vm!("QMULINT 0", [int -123] => [int 0]);
        assert_run_vm!("QMULINT 1", [int -123] => [int -123]);
        assert_run_vm!("QMUL", [int -123, int 123] => [int -123 * 123]);
        assert_run_vm!("QMULINT 123", [int -123] => [int -123 * 123]);
        assert_run_vm!("QMUL", [int -123, int -123] => [int 123 * 123]);
        assert_run_vm!("QMULINT -123", [int -123] => [int 123 * 123]);
        assert_run_vm!("QMUL", [int int257_min(), int 0] => [int 0]);
        assert_run_vm!("QMUL", [int int257_max(), int 0] => [int 0]);
        assert_run_vm!("QMUL", [int int257_min(), int 1] => [int int257_min()]);
        assert_run_vm!("QMUL", [int int257_max(), int 1] => [int int257_max()]);
        assert_run_vm!("QMUL", [int int257_max(), int -1] => [int int257_min() + 1]);
        assert_run_vm!("QMUL", [nan, int 2] => [nan]);
        assert_run_vm!("QMUL", [int 2, nan] => [nan]);
        assert_run_vm!("QMUL", [int int257_min(), int -1] => [nan]);
        assert_run_vm!("QMUL", [int int257_min() / 2, int -2] => [nan]);
        assert_run_vm!("QMUL", [int int257_max(), int 2] => [nan]);
        // neg
        assert_run_vm!("QMUL", [] => [int 0], exit_code: 2);
        assert_run_vm!("QMUL", [int 2] => [int 0], exit_code: 2);
        assert_run_vm!("QMUL", [int 2, null] => [int 0], exit_code: 7);
    }

    #[test]
    #[traced_test]
    fn op_divmod() {
        // pos
        assert_run_vm!("DIV", [int 5, int 5] => [int 1]);
        assert_run_vm!("DIV", [int 5, int 2] => [int 2]);
        assert_run_vm!("DIVR", [int 10, int 3] => [int 3]);
        assert_run_vm!("DIVC", [int 10, int 3] => [int 4]);
        // neg
        assert_run_vm!("DIV", [] => [int 0], exit_code: 2);
        assert_run_vm!("DIV", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("DIV", [int 1, int 0] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("MOD", [int 5, int 5] => [int 0]);
        assert_run_vm!("MOD", [int 5, int 2] => [int 1]);
        assert_run_vm!("MODR", [int 10, int 3] => [int 1]);
        assert_run_vm!("MODC", [int 10, int 3] => [int -2]);
        // neg
        assert_run_vm!("MOD", [] => [int 0], exit_code: 2);
        assert_run_vm!("MOD", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("MOD", [int 1, int 0] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("DIVMOD", [int 5, int 5] => [int 1, int 0]);
        assert_run_vm!("DIVMOD", [int 5, int 2] => [int 2, int 1]);
        assert_run_vm!("DIVMOD", [int -11, int 5] => [int -3, int 4]);
        assert_run_vm!("DIVMODR", [int 10, int 3] => [int 3, int 1]);
        assert_run_vm!("DIVMODC", [int 10, int 3] => [int 4, int -2]);
        // neg
        assert_run_vm!("DIVMOD", [] => [int 0], exit_code: 2);
        assert_run_vm!("DIVMOD", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("DIVMOD", [int 1, int 0] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("ADDDIVMOD", [int 3, int 2, int 5] => [int 1, int 0]);
        assert_run_vm!("ADDDIVMOD", [int 1, int 4, int 2] => [int 2, int 1]);
        assert_run_vm!("ADDDIVMOD", [int -15, int 4, int 5] => [int -3, int 4]);
        assert_run_vm!("ADDDIVMODR", [int 3, int 7, int 3] => [int 3, int 1]);
        assert_run_vm!("ADDDIVMODC", [int 1, int 9, int 3] => [int 4, int -2]);
        // neg
        assert_run_vm!("ADDDIVMOD", [] => [int 0], exit_code: 2);
        assert_run_vm!("ADDDIVMOD", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("ADDDIVMOD", [int 1, int 1, int 0] => [int 0], exit_code: 4);
        assert_run_vm!("ADDDIVMOD", [int 1, nan, int 0] => [int 0], exit_code: 4);
    }

    // TODO: Add more tests
    #[test]
    #[traced_test]
    fn op_shrmod() {
        assert_run_vm!("RSHIFT", [int 5, int 2] => [int 1]);
        assert_run_vm!("RSHIFT", [int 5, int 0] => [int 5]);
        assert_run_vm!("RSHIFT", [int -10, int 0] => [int -10]);
        assert_run_vm!("RSHIFT", [int -9, int 3] => [int -2]);
        assert_run_vm!("RSHIFT", [int -8, int 3] => [int -1]);
        assert_run_vm!("RSHIFT", [nan, int 3] => [int 0], exit_code: 4);
        assert_run_vm!("QUIET RSHIFT", [int 5, int 2] => [int 1]);
        assert_run_vm!("QUIET RSHIFT", [nan, int 3] => [nan]);

        assert_run_vm!("MODPOW2", [int 5, int 2] => [int 1]);
        assert_run_vm!("MODPOW2", [int 5, int 0] => [int 0]);
        assert_run_vm!("MODPOW2", [int -9, int 3] => [int 7]);
        assert_run_vm!("MODPOW2", [int -9, int 0] => [int 0]);
        assert_run_vm!("MODPOW2", [int -8, int 3] => [int 0]);
        assert_run_vm!("MODPOW2", [nan, int 3] => [int 0], exit_code: 4);
        assert_run_vm!("QUIET MODPOW2", [int 5, int 2] => [int 1]);
        assert_run_vm!("QUIET MODPOW2", [nan, int 3] => [nan]);

        assert_run_vm!("RSHIFTMOD", [int 5, int 2] => [int 1, int 1]);
        assert_run_vm!("RSHIFTMOD", [int 5, int 0] => [int 5, int 0]);
        assert_run_vm!("RSHIFTMOD", [int -9, int 3] => [int -2, int 7]);
        assert_run_vm!("RSHIFTMOD", [int -9, int 0] => [int -9, int 0]);
        assert_run_vm!("RSHIFTMOD", [int -8, int 3] => [int -1, int 0]);
        assert_run_vm!("RSHIFTMOD", [nan, int 3] => [int 0], exit_code: 4);
        assert_run_vm!("QUIET RSHIFTMOD", [int 5, int 2] => [int 1, int 1]);
        assert_run_vm!("QUIET RSHIFTMOD", [nan, int 3] => [nan, nan]);

        assert_run_vm!("ADDRSHIFTMOD", [int 3, int 2, int 2] => [int 1, int 1]);
        assert_run_vm!("ADDRSHIFTMOD", [int 3, int 2, int 0] => [int 5, int 0]);
        assert_run_vm!("ADDRSHIFTMOD", [int -10, int 1, int 3] => [int -2, int 7]);
        assert_run_vm!("ADDRSHIFTMOD", [int -10, int 1, int 0] => [int -9, int 0]);
        assert_run_vm!("ADDRSHIFTMOD", [int -4, int -4, int 3] => [int -1, int 0]);
        assert_run_vm!("ADDRSHIFTMOD", [nan, int 1, int 3] => [int 0], exit_code: 4);
        assert_run_vm!("ADDRSHIFTMOD", [int 1, nan, int 3] => [int 0], exit_code: 4);
        assert_run_vm!("QUIET ADDRSHIFTMOD", [int 3, int 2, int 2] => [int 1, int 1]);
        assert_run_vm!("QUIET ADDRSHIFTMOD", [nan, int 1, int 3] => [nan, nan]);
        assert_run_vm!("QUIET ADDRSHIFTMOD", [int 1, nan, int 3] => [nan, nan]);
    }

    // TODO: Add more tests
    #[test]
    #[traced_test]
    fn op_muldivmod() {
        // pos
        assert_run_vm!("MULDIV", [int 5, int 1, int 5] => [int 1]);
        assert_run_vm!("MULDIV", [int 5, int 1, int 2] => [int 2]);
        assert_run_vm!("MULDIVR", [int 5, int 2, int 3] => [int 3]);
        assert_run_vm!("MULDIVC", [int 5, int 2, int 3] => [int 4]);
        // neg
        assert_run_vm!("MULDIV", [] => [int 0], exit_code: 2);
        assert_run_vm!("MULDIV", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("MULDIV", [int 1, int 1, int 0] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("MULMOD", [int 6, int 2, int 6] => [int 0]);
        assert_run_vm!("MULMOD", [int 5, int 1, int 2] => [int 1]);
        assert_run_vm!("MULMODR", [int 5, int 2, int 3] => [int 1]);
        assert_run_vm!("MULMODC", [int 2, int 5, int 3] => [int -2]);
        // neg
        assert_run_vm!("MULMOD", [] => [int 0], exit_code: 2);
        assert_run_vm!("MULMOD", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("MULMOD", [int 1, int 1, int 0] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("MULDIVMOD", [int 3, int 2, int 6] => [int 1, int 0]);
        assert_run_vm!("MULDIVMOD", [int 3, int 2, int 4] => [int 1, int 2]);
        assert_run_vm!("MULDIVMOD", [int 11, int -1, int 5] => [int -3, int 4]);
        assert_run_vm!("MULDIVMODR", [int 2, int 5, int 3] => [int 3, int 1]);
        assert_run_vm!("MULDIVMODC", [int 2, int 5, int 3] => [int 4, int -2]);
        // neg
        assert_run_vm!("MULDIVMOD", [] => [int 0], exit_code: 2);
        assert_run_vm!("MULDIVMOD", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("MULDIVMOD", [int 1, int 1, int 0] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("MULADDDIVMOD", [int 3, int 1, int 2, int 5] => [int 1, int 0]);
        assert_run_vm!("MULADDDIVMOD", [int 1, int 1, int 4, int 2] => [int 2, int 1]);
        assert_run_vm!("MULADDDIVMOD", [int -5, int 3, int 4, int 5] => [int -3, int 4]);
        assert_run_vm!("MULADDDIVMODR", [int 1, int 3, int 7, int 3] => [int 3, int 1]);
        assert_run_vm!("MULADDDIVMODC", [int 1, int 1, int 9, int 3] => [int 4, int -2]);
        // neg
        assert_run_vm!("MULADDDIVMOD", [] => [int 0], exit_code: 2);
        assert_run_vm!("MULADDDIVMOD", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("MULADDDIVMOD", [int 1, int 1, int 1, int 0] => [int 0], exit_code: 4);
        assert_run_vm!("MULADDDIVMOD", [int 1, int 1, nan, int 0] => [int 0], exit_code: 4);
    }

    // TODO: Add more tests
    #[test]
    #[traced_test]
    fn op_mulshrmod() {
        assert_run_vm!("MULRSHIFT", [int 1, int 5, int 2] => [int 1]);
        assert_run_vm!("MULRSHIFT", [int 1, int 5, int 0] => [int 5]);
        assert_run_vm!("MULRSHIFT", [int -3, int 3, int 3] => [int -2]);
        assert_run_vm!("MULRSHIFT", [int -3, int 3, int 0] => [int -9]);
        assert_run_vm!("MULRSHIFT", [int 4, int -2, int 3] => [int -1]);
        assert_run_vm!("MULRSHIFT", [int 1, nan, int 3] => [int 0], exit_code: 4);
        assert_run_vm!("QUIET MULRSHIFT", [int 5, int 1, int 2] => [int 1]);
        assert_run_vm!("QUIET MULRSHIFT", [nan, int 1, int 3] => [nan]);

        assert_run_vm!("MULMODPOW2", [int 5, int 1, int 2] => [int 1]);
        assert_run_vm!("MULMODPOW2", [int 5, int 1, int 0] => [int 0]);
        assert_run_vm!("MULMODPOW2", [int -3, int 3, int 3] => [int 7]);
        assert_run_vm!("MULMODPOW2", [int -3, int 3, int 0] => [int 0]);
        assert_run_vm!("MULMODPOW2", [int 4, int -2, int 3] => [int 0]);
        assert_run_vm!("MULMODPOW2", [int 1, nan, int 3] => [int 0], exit_code: 4);
        assert_run_vm!("QUIET MULMODPOW2", [int 5, int 1, int 2] => [int 1]);
        assert_run_vm!("QUIET MULMODPOW2", [nan, int 1, int 3] => [nan]);

        assert_run_vm!("MULRSHIFTMOD", [int 5, int 1, int 2] => [int 1, int 1]);
        assert_run_vm!("MULRSHIFTMOD", [int 5, int 1, int 0] => [int 5, int 0]);
        assert_run_vm!("MULRSHIFTMOD", [int -3, int 3, int 3] => [int -2, int 7]);
        assert_run_vm!("MULRSHIFTMOD", [int -3, int 3, int 0] => [int -9, int 0]);
        assert_run_vm!("MULRSHIFTMOD", [int -4, int 2, int 3] => [int -1, int 0]);
        assert_run_vm!("MULRSHIFTMOD", [int 1, nan, int 3] => [int 0], exit_code: 4);
        assert_run_vm!("QUIET MULRSHIFTMOD", [int 5, int 1, int 2] => [int 1, int 1]);
        assert_run_vm!("QUIET MULRSHIFTMOD", [nan, int 1, int 3] => [nan, nan]);

        assert_run_vm!("MULADDRSHIFTMOD", [int 3, int 1, int 2, int 2] => [int 1, int 1]);
        assert_run_vm!("MULADDRSHIFTMOD", [int 3, int 1, int 2, int 0] => [int 5, int 0]);
        assert_run_vm!("MULADDRSHIFTMOD", [int -5, int 2, int 1, int 3] => [int -2, int 7]);
        assert_run_vm!("MULADDRSHIFTMOD", [int -5, int 2, int 1, int 0] => [int -9, int 0]);
        assert_run_vm!("MULADDRSHIFTMOD", [int -2, int 2, int -4, int 3] => [int -1, int 0]);
        assert_run_vm!("MULADDRSHIFTMOD", [int 1, nan, int 1, int 3] => [int 0], exit_code: 4);
        assert_run_vm!("MULADDRSHIFTMOD", [int 2, int 1, nan, int 3] => [int 0], exit_code: 4);
        assert_run_vm!("QUIET MULADDRSHIFTMOD", [int 1, int 3, int 2, int 2] => [int 1, int 1]);
        assert_run_vm!("QUIET MULADDRSHIFTMOD", [int 1, nan, int 1, int 3] => [nan, nan]);
        assert_run_vm!("QUIET MULADDRSHIFTMOD", [int 1, int 1, nan, int 3] => [nan, nan]);
    }

    // TODO: Add more tests
    #[test]
    #[traced_test]
    fn op_shldivmod() {
        // pos
        assert_run_vm!("LSHIFTDIV", [int 5, int 5, int 0] => [int 1]);
        assert_run_vm!("LSHIFTDIV", [int 5, int 2, int 0] => [int 2]);
        assert_run_vm!("LSHIFTDIVR", [int 5, int 3, int 1] => [int 3]);
        assert_run_vm!("LSHIFTDIVC", [int 5, int 3, int 1] => [int 4]);
        // neg
        assert_run_vm!("LSHIFTDIV", [] => [int 0], exit_code: 2);
        assert_run_vm!("LSHIFTDIV", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("LSHIFTDIV", [int 1, int 0, int 1] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("LSHIFTMOD", [int 5, int 5, int 0] => [int 0]);
        assert_run_vm!("LSHIFTMOD", [int 5, int 2, int 0] => [int 1]);
        assert_run_vm!("LSHIFTMODR", [int 5, int 3, int 1] => [int 1]);
        assert_run_vm!("LSHIFTMODC", [int 5, int 3, int 1] => [int -2]);
        // neg
        assert_run_vm!("LSHIFTMOD", [] => [int 0], exit_code: 2);
        assert_run_vm!("LSHIFTMOD", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("LSHIFTMOD", [int 1, int 0, int 1] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("LSHIFTDIVMOD", [int 5, int 5, int 0] => [int 1, int 0]);
        assert_run_vm!("LSHIFTDIVMOD", [int 5, int 2, int 0] => [int 2, int 1]);
        assert_run_vm!("LSHIFTDIVMOD", [int -11, int 5, int 0] => [int -3, int 4]);
        assert_run_vm!("LSHIFTDIVMODR", [int 5, int 3, int 1] => [int 3, int 1]);
        assert_run_vm!("LSHIFTDIVMODC", [int 5, int 3, int 1] => [int 4, int -2]);
        // neg
        assert_run_vm!("LSHIFTDIVMOD", [] => [int 0], exit_code: 2);
        assert_run_vm!("LSHIFTDIVMOD", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("LSHIFTDIVMOD", [int 1, int 0, int 1] => [int 0], exit_code: 4);
    }

    #[test]
    #[traced_test]
    fn other_ops() {
        // === MIN/MAX/MINMAX/QMIN/QMAX/QMINMAX ===

        // pos
        assert_run_vm!("MIN", [int 123, int 456] => [int 123]);
        assert_run_vm!("MAX", [int 123, int 456] => [int 456]);
        assert_run_vm!("MINMAX", [int 456, int 123] => [int 123, int 456]);
        // neg
        assert_run_vm!("MIN", [] => [int 0], exit_code: 2);
        assert_run_vm!("MIN", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("MIN", [int 123, nan] => [int 0], exit_code: 4);
        assert_run_vm!("MINMAX", [int 123, nan] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("QUIET MIN", [int 123, int 456] => [int 123]);
        assert_run_vm!("QUIET MAX", [int 123, int 456] => [int 456]);
        assert_run_vm!("QUIET MINMAX", [int 456, int 123] => [int 123, int 456]);
        assert_run_vm!("QUIET MIN", [int 123, nan] => [nan]);
        assert_run_vm!("QUIET MINMAX", [int 123, nan] => [nan, nan]);
        // neg
        assert_run_vm!("QUIET MIN", [] => [int 0], exit_code: 2);
        assert_run_vm!("QUIET MIN", [int 123] => [int 0], exit_code: 2);

        // === ABS/QABS ===

        // pos
        assert_run_vm!("ABS", [int 0] => [int 0]);
        assert_run_vm!("ABS", [int 123] => [int 123]);
        assert_run_vm!("ABS", [int -123123] => [int 123123]);
        assert_run_vm!("ABS", [int int257_min() + 1] => [int int257_max()]);
        // neg
        assert_run_vm!("ABS", [] => [int 0], exit_code: 2);
        assert_run_vm!("ABS", [nan] => [int 0], exit_code: 4);
        assert_run_vm!("ABS", [int int257_min()] => [int 0], exit_code: 4);
        assert_run_vm!("ABS", [null] => [int 0], exit_code: 7);

        // pos
        assert_run_vm!("QUIET ABS", [int 0] => [int 0]);
        assert_run_vm!("QUIET ABS", [int 123] => [int 123]);
        assert_run_vm!("QUIET ABS", [int -123123] => [int 123123]);
        assert_run_vm!("QUIET ABS", [int int257_min() + 1] => [int int257_max()]);
        assert_run_vm!("QUIET ABS", [nan] => [nan]);
        assert_run_vm!("QUIET ABS", [int int257_min()] => [nan]);
        // neg
        assert_run_vm!("QUIET ABS", [] => [int 0], exit_code: 2);
        assert_run_vm!("QUIET ABS", [null] => [int 0], exit_code: 7);
    }

    fn int257_min() -> BigInt {
        BigInt::from(-1) << 256
    }

    fn int257_max() -> BigInt {
        (BigInt::from(1) << 256) - 1
    }
}
