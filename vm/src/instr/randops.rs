use everscale_types::cell::HashBytes;
use num_bigint::{BigInt, Sign};
use sha2::Digest;
use tycho_vm_proc::vm_module;

use crate::cont::ControlRegs;
use crate::error::VmResult;
use crate::gas::GasConsumer;
use crate::saferc::SafeRc;
use crate::smc_info::SmcInfoBase;
use crate::stack::{Stack, StackValueType};
use crate::state::VmState;

pub struct RandOps;

#[vm_module]
impl RandOps {
    #[op(code = "f810", fmt = "RANDU256")]
    fn exec_randu256(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let random_bytes = ok!(generate_random_u256(&mut st.cr, &st.gas));
        let random = BigInt::from_bytes_be(Sign::Plus, random_bytes.as_ref());
        ok!(stack.push_int(random));
        Ok(0)
    }

    #[op(code = "f811", fmt = "RAND")]
    fn exec_rand_int(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let mut int = ok!(stack.pop_int());
        let random_bytes = ok!(generate_random_u256(&mut st.cr, &st.gas));
        let random = BigInt::from_bytes_be(Sign::Plus, random_bytes.as_ref());

        {
            let int = SafeRc::make_mut(&mut int);
            *int *= random;
            *int >>= 256;
        }

        ok!(stack.push_raw(int));
        Ok(0)
    }

    #[op(code = "f814", fmt = "SETRAND", args(mix = false))]
    #[op(code = "f815", fmt = "ADDRAND", args(mix = true))]
    fn exec_set_rand(st: &mut VmState, mix: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);

        let mut int = ok!(stack.pop_int());
        if int.sign() == Sign::Minus || int.bits() > 256 {
            vm_bail!(IntegerOutOfRange {
                min: 0,
                max: 256,
                actual: int.bits().to_string()
            })
        }

        let Some(c7) = &st.cr.c7 else {
            vm_bail!(ControlRegisterOutOfRange(7))
        };

        let Some(t1v) = c7.first().cloned() else {
            vm_bail!(InvalidType {
                expected: StackValueType::Tuple,
                actual: StackValueType::Null
            })
        };

        let Some(t1) = t1v.as_tuple_range(0, 255) else {
            vm_bail!(InvalidType {
                expected: StackValueType::Tuple,
                actual: t1v.ty()
            })
        };

        if mix {
            let bytes = match t1.get(SmcInfoBase::RANDSEED_IDX) {
                Some(value) => {
                    let value = ok!(value.clone().into_int());
                    ok!(to_bytes_be(&value))
                }
                None => vm_bail!(InvalidType {
                    expected: StackValueType::Int,
                    actual: StackValueType::Null
                }),
            };

            let mut buffer = [0u8; 64];
            buffer[32 - bytes.len()..32].copy_from_slice(&bytes);
            drop(bytes);

            let bytes = ok!(to_bytes_be(&int));
            buffer[64 - bytes.len()..64].copy_from_slice(&bytes);
            drop(bytes);

            let new_seed = sha2::Sha256::digest(buffer);
            int = SafeRc::new(BigInt::from_bytes_be(Sign::Plus, &new_seed));
        }

        // NOTE: Make sure that we have a unique instance of the `c7` tuple
        //       (at least make sure that this situation is possible).
        let mut c7 = st.cr.c7.take().unwrap();

        // NOTE: Make sure that the `t1v` instance is unique
        //       (at least make sure that this situation is possible).
        SafeRc::make_mut(&mut c7)[0] = Stack::make_null();

        let mut t1v = t1v.into_tuple().expect("t1 was checked as tuple");
        {
            let t1v = SafeRc::make_mut(&mut t1v);
            if t1v.len() <= SmcInfoBase::RANDSEED_IDX {
                t1v.resize_with(SmcInfoBase::RANDSEED_IDX + 1, Stack::make_null);
            }
            t1v[SmcInfoBase::RANDSEED_IDX] = int.into_dyn_value();
        }
        let t1_len = t1v.len();

        // NOTE: Restore c7 and control registers state.
        SafeRc::make_mut(&mut c7)[0] = t1v.into_dyn_value();
        let c7_len = c7.len();
        st.cr.c7 = Some(c7);

        st.gas.try_consume_tuple_gas(t1_len as _)?;
        st.gas.try_consume_tuple_gas(c7_len as _)?;

        Ok(0)
    }
}

fn generate_random_u256(regs: &mut ControlRegs, gas: &GasConsumer) -> VmResult<HashBytes> {
    let Some(c7) = regs.c7.as_ref() else {
        vm_bail!(ControlRegisterOutOfRange(7))
    };

    let Some(t1v) = c7.first().cloned() else {
        vm_bail!(InvalidType {
            expected: StackValueType::Tuple,
            actual: StackValueType::Null
        })
    };
    let Some(t1) = t1v.as_tuple_range(0, 255) else {
        vm_bail!(InvalidType {
            expected: StackValueType::Tuple,
            actual: t1v.ty()
        })
    };

    let hash: [u8; 64] = match t1.get(SmcInfoBase::RANDSEED_IDX) {
        Some(value) => {
            let value = ok!(value.clone().into_int());
            let bytes = ok!(to_bytes_be(&value));

            let mut seed_bytes = [0u8; 32];
            seed_bytes[32 - bytes.len()..].copy_from_slice(&bytes);
            sha2::Sha512::digest(seed_bytes).into()
        }
        None => vm_bail!(InvalidType {
            expected: StackValueType::Int,
            actual: StackValueType::Null
        }),
    };

    let new_seedv = SafeRc::new_dyn_value(BigInt::from_bytes_be(Sign::Plus, &hash[..32]));
    let res = HashBytes::from_slice(&hash[32..]);

    // NOTE: Make sure that we have a unique instance of the `c7` tuple
    //       (at least make sure that this situation is possible).
    let mut c7 = regs.c7.take().unwrap();

    // NOTE: Make sure that the `t1v` instance is unique
    //       (at least make sure that this situation is possible).
    SafeRc::make_mut(&mut c7)[0] = Stack::make_null();

    let mut t1v = t1v.into_tuple().expect("t1 was checked as tuple");
    SafeRc::make_mut(&mut t1v)[SmcInfoBase::RANDSEED_IDX] = new_seedv;
    let t1_len = t1v.len();

    // NOTE: Restore c7 and control registers state.
    SafeRc::make_mut(&mut c7)[0] = t1v.into_dyn_value();
    let c7_len = c7.len();
    regs.c7 = Some(c7);

    gas.try_consume_tuple_gas(t1_len as _)?;
    gas.try_consume_tuple_gas(c7_len as _)?;

    Ok(res)
}

fn to_bytes_be(int: &BigInt) -> VmResult<Vec<u8>> {
    vm_ensure!(int.sign() != Sign::Minus, IntegerOutOfRange {
        min: 0,
        max: isize::MAX,
        actual: "negative".to_owned()
    });

    let mut bytes = int.magnitude().to_bytes_le();
    bytes.truncate(32);
    bytes.reverse();
    Ok(bytes)
}

#[cfg(test)]
pub mod test {
    use tracing_test::traced_test;

    use super::*;

    fn uint256(str: &str) -> BigInt {
        let value = hex::decode(str).unwrap();
        BigInt::from_bytes_be(Sign::Plus, &value)
    }

    #[test]
    #[traced_test]
    fn random() {
        assert_run_vm!("INT 123 RAND", c7: tuple![], [] => [int 0], exit_code: 7);
        assert_run_vm!("INT 123 RAND", c7: tuple![[]], [] => [int 0], exit_code: 7);

        assert_run_vm!("INT 123 SETRAND", c7: tuple![], [] => [int 0], exit_code: 7);
        assert_run_vm!("INT 123 SETRAND", c7: tuple![[]], [] => [], exit_code: 0);

        assert_run_vm!("INT 123 ADDRAND", c7: tuple![], [] => [int 0], exit_code: 7);
        assert_run_vm!("INT 123 ADDRAND", c7: tuple![[]], [] => [int 0], exit_code: 7);

        let value = uint256("576f8d6b5ac3bcc80844b7d50b1cc6603444bbe7cfcf8fc0aa1ee3c636d9e339");
        let c7 = tuple![[
            null,              // 0
            null,              // 1
            null,              // 2
            null,              // 3
            null,              // 4
            null,              // 5
            int value.clone(), // RANDSEED_IDX
        ]];

        let result = uint256("504C79E96A1A3D91262EDE19D9F064E9752EEA03E21A5E208D7BDCAF2D6610EE");
        assert_run_vm!("RAND", c7: c7.clone(), [int value.clone()] => [int result]);

        let result = uint256("EB1A91B388F714F56EE88C7B1B0902FF713FE8EBA39F64FC8F7F2F618601BBF5");
        assert_run_vm!("RANDU256", c7: c7.clone(), [] => [int result]);

        assert_run_vm!(
            r#"
                INT 123
                SETRAND
                GETPARAM 6
            "#,
            c7: c7.clone(),
            [] => [int 123],
        );

        let new_rand = BigInt::from_bytes_be(
            Sign::Plus,
            &sha2::Sha256::digest({
                let mut buffer = [0u8; 64];

                let mut old_rand = value.magnitude().to_bytes_le();
                old_rand.truncate(32);
                old_rand.reverse();
                buffer[32 - old_rand.len()..32].copy_from_slice(&old_rand);

                buffer[63] = 123;
                buffer
            }),
        );

        assert_run_vm!(
            r#"
                INT 123
                ADDRAND
                GETPARAM 6
            "#,
            c7: c7,
            [] => [int new_rand],
        );
    }
}
