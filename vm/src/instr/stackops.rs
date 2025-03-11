use tycho_vm_proc::vm_module;

use crate::error::VmResult;
use crate::saferc::SafeRc;
use crate::smc_info::VmVersion;
use crate::stack::Stack;
use crate::state::VmState;

pub struct StackOps;

#[vm_module]
impl StackOps {
    #[op(code = "00", fmt = "NOP")]
    fn exec_nop(_: &mut VmState) -> VmResult<i32> {
        Ok(0)
    }

    #[op(code = "01", fmt = "SWAP")]
    fn exec_swap(st: &mut VmState) -> VmResult<i32> {
        ok!(SafeRc::make_mut(&mut st.stack).swap(0, 1));
        Ok(0)
    }

    #[op(code = "0j @ 02..", fmt = "XCHG s{j}", args(i = 0))]
    #[op(code = "10ij", fmt = "XCHG s{i},s{j}", cond = i != 0 && i < j)]
    #[op(code = "11jj", fmt = "XCHG s{j}", args(i = 0))]
    #[op(code = "1j @ 12..", fmt = "XCHG s1,s{j}", args(i = 1))]
    fn exec_xchg(st: &mut VmState, i: u32, j: u32) -> VmResult<i32> {
        ok!(SafeRc::make_mut(&mut st.stack).swap(i as _, j as _));
        Ok(0)
    }

    #[op(code = "20", fmt = "DUP")]
    fn exec_dup(st: &mut VmState) -> VmResult<i32> {
        ok!(SafeRc::make_mut(&mut st.stack).push_nth(0));
        Ok(0)
    }

    #[op(code = "21", fmt = "OVER")]
    fn exec_over(st: &mut VmState) -> VmResult<i32> {
        ok!(SafeRc::make_mut(&mut st.stack).push_nth(1));
        Ok(0)
    }

    #[op(code = "2i @ 22..", fmt = "PUSH s{i}")]
    #[op(code = "56ii", fmt = "PUSH s{i}")]
    fn exec_push(st: &mut VmState, i: u32) -> VmResult<i32> {
        ok!(SafeRc::make_mut(&mut st.stack).push_nth(i as _));
        Ok(0)
    }

    #[op(code = "30", fmt = "DROP")]
    fn exec_drop(st: &mut VmState) -> VmResult<i32> {
        ok!(SafeRc::make_mut(&mut st.stack).pop());
        Ok(0)
    }

    #[op(code = "31", fmt = "NIP")]
    fn exec_nip(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.swap(0, 1));
        ok!(stack.pop());
        Ok(0)
    }

    #[op(code = "3i @ 32..", fmt = "POP s{i}")]
    #[op(code = "57ii", fmt = "POP s{i}")]
    fn exec_pop(st: &mut VmState, i: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.swap(0, i as _));
        ok!(stack.pop());
        Ok(0)
    }

    #[op(code = "4ijk", fmt = "XCHG3 s{i},s{j},s{k}")]
    #[op(code = "540ijk", fmt = "XCHG3 s{i},s{j},s{k}")]
    fn exec_xchg3(st: &mut VmState, i: u32, j: u32, k: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.swap(2, i as _));
        ok!(stack.swap(1, j as _));
        ok!(stack.swap(0, k as _));
        Ok(0)
    }

    #[op(code = "50ij", fmt = "XCHG2 s{i},s{j}")]
    fn exec_xchg2(st: &mut VmState, i: u32, j: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.swap(1, i as _));
        ok!(stack.swap(0, j as _));
        Ok(0)
    }

    #[op(code = "51ij", fmt = "XCPU s{i},s{j}")]
    fn exec_xcpu(st: &mut VmState, i: u32, j: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.swap(0, i as _));
        ok!(stack.push_nth(j as _));
        Ok(0)
    }

    #[op(code = "52ij", fmt = ("PUXC s{i},s{}", j as i32 - 1))]
    fn exec_puxc(st: &mut VmState, i: u32, j: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.push_nth(i as _));
        ok!(stack.swap(0, 1));
        ok!(stack.swap(0, j as _));
        Ok(0)
    }

    #[op(code = "53ij", fmt = "PUSH2 s{i},s{j}")]
    fn exec_push2(st: &mut VmState, i: u32, j: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.push_nth(i as _));
        ok!(stack.push_nth(1 + j as usize));
        Ok(0)
    }

    // XCHG XCHG XCHG -> 540ijk exec_xchg3

    // XCHG XCHG PUSH
    #[op(code = "541ijk", fmt = "XC2PU")]
    fn exec_xc2pu(st: &mut VmState, i: u32, j: u32, k: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.swap(1, i as _));
        ok!(stack.swap(0, j as _));
        ok!(stack.push_nth(k as _));
        Ok(0)
    }

    // XCHG PUSH XCHG
    #[op(code = "542ijk", fmt = ("XCPUXC s{i},s{j},s{}", k as i32 - 1))]
    fn exec_xcpuxc(st: &mut VmState, i: u32, j: u32, k: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.swap(1, i as _));
        ok!(stack.push_nth(j as _));
        ok!(stack.swap(0, 1));
        ok!(stack.swap(0, k as _));
        Ok(0)
    }

    // XCHG PUSH PUSH
    #[op(code = "543ijk", fmt = "XCPU2 s{i},s{j},s{k}")]
    fn exec_xcpu2(st: &mut VmState, i: u32, j: u32, k: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.swap(0, i as _));
        ok!(stack.push_nth(j as _));
        ok!(stack.push_nth(1 + k as usize));
        Ok(0)
    }

    // PUSH XCHG XCHG
    #[op(code = "544ijk", fmt = ("PUXC2 s{i},s{},s{}", j as i32 - 1, k as i32 - 1))]
    fn exec_puxc2(st: &mut VmState, i: u32, j: u32, k: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.push_nth(i as _));
        ok!(stack.swap(2, 0));
        ok!(stack.swap(1, j as _));
        ok!(stack.swap(0, k as _));
        Ok(0)
    }

    // PUSH XCHG PUSH
    #[op(code = "545ijk", fmt = ("PUXCPU s{i},s{},s{}", j as i32 - 1, k as i32 - 1))]
    fn exec_puxcpu(st: &mut VmState, i: u32, j: u32, k: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.push_nth(i as _));
        ok!(stack.swap(0, 1));
        ok!(stack.swap(0, j as _));
        ok!(stack.push_nth(k as _));
        Ok(0)
    }

    // PUSH PUSH XCHG
    #[op(code = "546ijk", fmt = ("PU2XC s{i},s{},s{}", j as i32 - 1, k as i32 - 2))]
    fn exec_pu2xc(st: &mut VmState, i: u32, j: u32, k: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.push_nth(i as _));
        ok!(stack.swap(1, 0));
        ok!(stack.push_nth(j as _));
        ok!(stack.swap(1, 0));
        ok!(stack.swap(0, k as _));
        Ok(0)
    }

    // PUSH PUSH PUSH
    #[op(code = "547ijk", fmt = "PUSH3 s{i},s{j},s{k}")]
    fn exec_push3(st: &mut VmState, i: u32, j: u32, k: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.push_nth(i as _));
        ok!(stack.push_nth(1 + j as usize));
        ok!(stack.push_nth(2 + k as usize));
        Ok(0)
    }

    #[op(code = "55ij", fmt = "BLKSWAP {i},{j}", args(i = 1 + ((args >> 4) & 0xf), j = 1 + (args & 0xf)))]
    fn exec_blkswap(st: &mut VmState, i: u32, j: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.reverse_range(j as _, i as _));
        ok!(stack.reverse_range(0, j as _));
        ok!(stack.reverse_range(0, (i + j) as _));
        Ok(0)
    }

    // 56ii exec_push
    // 57ii exec_pop

    #[op(code = "58", fmt = "ROT")]
    fn exec_rot(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.swap(1, 2));
        ok!(stack.swap(0, 1));
        Ok(0)
    }

    #[op(code = "59", fmt = "ROTREV")]
    fn exec_rotrev(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.swap(0, 1));
        ok!(stack.swap(1, 2));
        Ok(0)
    }

    #[op(code = "5a", fmt = "2SWAP")]
    fn exec_2swap(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.swap(1, 3));
        ok!(stack.swap(0, 2));
        Ok(0)
    }

    #[op(code = "5b", fmt = "2DROP")]
    fn exec_2drop(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.pop());
        ok!(stack.pop());
        Ok(0)
    }

    #[op(code = "5c", fmt = "2DUP")]
    fn exec_2dup(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.push_nth(1));
        ok!(stack.push_nth(1));
        Ok(0)
    }

    #[op(code = "5d", fmt = "2OVER")]
    fn exec_2over(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.push_nth(3));
        ok!(stack.push_nth(3));
        Ok(0)
    }

    #[op(code = "5eij", fmt = "REVERSE {i},{j}", args(i = 2 + ((args >> 4) & 0xf)))]
    fn exec_reverse(st: &mut VmState, i: u32, j: u32) -> VmResult<i32> {
        ok!(SafeRc::make_mut(&mut st.stack).reverse_range(j as _, i as _));
        Ok(0)
    }

    #[op(code = "5f0i", fmt = "BLKDROP {i}")]
    fn exec_blkdrop(st: &mut VmState, i: u32) -> VmResult<i32> {
        ok!(SafeRc::make_mut(&mut st.stack).pop_many(i as _));
        Ok(0)
    }

    #[op(code = "5fij @ 5f10..", fmt = "BLKPUSH {i},{j}")]
    fn exec_blkpush(st: &mut VmState, mut i: u32, j: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        while i >= 1 {
            ok!(stack.push_nth(j as _));
            i -= 1;
        }
        Ok(0)
    }

    #[op(code = "60", fmt = "PICK")]
    fn exec_pick(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let i = ok!(stack.pop_smallint_range(0, max_stack_size(st.version)));
        ok!(stack.push_nth(i as _));
        Ok(0)
    }

    #[op(code = "61", fmt = "ROLL")]
    fn exec_roll(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);

        let mut i = ok!(stack.pop_smallint_range(0, max_stack_size(st.version)));
        if let Some(diff) = i.checked_sub(STACK_FEE_THRESHOLD) {
            st.gas.try_consume(diff as u64)?;
        }

        while i >= 1 {
            ok!(stack.swap(i as _, (i - 1) as _));
            i -= 1;
        }
        Ok(0)
    }

    #[op(code = "62", fmt = "ROLLREV")]
    fn exec_rollrev(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);

        let x = ok!(stack.pop_smallint_range(0, max_stack_size(st.version)));
        if let Some(diff) = x.checked_sub(STACK_FEE_THRESHOLD) {
            st.gas.try_consume(diff as u64)?;
        }

        for i in 0..x {
            ok!(stack.swap(i as _, (i + 1) as _));
        }
        Ok(0)
    }

    #[op(code = "63", fmt = "BLKSWX")]
    fn exec_blkswap_x(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);

        let y = ok!(stack.pop_smallint_range(0, max_stack_size(st.version)));
        let x = ok!(stack.pop_smallint_range(0, max_stack_size(st.version)));

        if x > 0 && y > 0 {
            if should_consume_gas(st.version) {
                if let Some(diff) = (x as u64 + y as u64).checked_sub(STACK_FEE_THRESHOLD as _) {
                    st.gas.try_consume(diff)?;
                }
            }

            ok!(stack.reverse_range(y as _, x as _));
            ok!(stack.reverse_range(0, y as _));
            ok!(stack.reverse_range(0, (x + y) as _));
        }
        Ok(0)
    }

    #[op(code = "64", fmt = "REVX")]
    fn exec_reverse_x(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);

        let y = ok!(stack.pop_smallint_range(0, max_stack_size(st.version)));
        let x = ok!(stack.pop_smallint_range(0, max_stack_size(st.version)));
        if let Some(diff) = x.checked_sub(STACK_FEE_THRESHOLD) {
            st.gas.try_consume(diff as _)?;
        }
        ok!(stack.reverse_range(y as _, x as _));
        Ok(0)
    }

    #[op(code = "65", fmt = "DROPX")]
    fn exec_drop_x(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_smallint_range(0, max_stack_size(st.version)));
        ok!(stack.pop_many(x as _));
        Ok(0)
    }

    #[op(code = "66", fmt = "TUCK")]
    fn exec_tuck(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.swap(0, 1));
        ok!(stack.push_nth(1));
        Ok(0)
    }

    #[op(code = "67", fmt = "XCHGX")]
    fn exec_xchg_x(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_smallint_range(0, max_stack_size(st.version)));
        ok!(stack.swap(0, x as _));
        Ok(0)
    }

    #[op(code = "68", fmt = "DEPTH")]
    fn exec_depth(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        ok!(stack.push_int(stack.depth()));
        Ok(0)
    }

    #[op(code = "69", fmt = "CHKDEPTH")]
    fn exec_chkdepth(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_smallint_range(0, max_stack_size(st.version))) as usize;
        vm_ensure!(x <= stack.depth(), StackUnderflow(x));
        Ok(0)
    }

    #[op(code = "6a", fmt = "ONLYTOPX")]
    fn exec_onlytop_x(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);

        let x = ok!(stack.pop_smallint_range(0, max_stack_size(st.version))) as usize;
        let Some(d) = stack.depth().checked_sub(x) else {
            vm_bail!(StackUnderflow(x));
        };

        if d > 0 {
            if let Some(diff) = x.checked_sub(STACK_FEE_THRESHOLD as _) {
                st.gas.try_consume(diff as u64)?;
            }
            stack.items.drain(..d);
        }

        stack.items.truncate(x);
        Ok(0)
    }

    /// Pops integer `i` from the stack, then leaves only the bottom `i` element.
    #[op(code = "6b", fmt = "ONLYX")]
    fn exec_only_x(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_smallint_range(0, max_stack_size(st.version))) as usize;
        let Some(d) = stack.depth().checked_sub(x) else {
            vm_bail!(StackUnderflow(x));
        };
        stack.items.truncate(d);
        Ok(0)
    }

    /// Drops `i` stack elements under the top `j` elements.
    #[op(code = "6cij @ 6c10..", fmt = "BLKDROP2 {i},{j}")]
    fn exec_blkdrop2(st: &mut VmState, i: u32, j: u32) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let depth = stack.depth();
        let offset = j as usize;
        let count = i as usize;
        vm_ensure!((count + offset) <= depth, StackUnderflow(count + offset));

        stack.items.drain(depth - (count + offset)..depth - offset);
        Ok(0)
    }
}

fn should_consume_gas(version: VmVersion) -> bool {
    version.is_ton(4..)
}

fn max_stack_size(version: VmVersion) -> u32 {
    if should_consume_gas(version) {
        // FIXME: Ton uses `(1 << 30) - 1` but its a bit too much.
        Stack::MAX_DEPTH as u32
    } else {
        STACK_FEE_THRESHOLD
    }
}

const STACK_FEE_THRESHOLD: u32 = 255;

#[cfg(test)]
mod tests {
    use tracing_test::traced_test;

    #[test]
    #[traced_test]
    fn blkdrop2() {
        assert_run_vm!("BLKDROP2 3, 0", [int 1, int 2, int 3, int 4, int 5, int 6] => [int 1, int 2, int 3]);
        assert_run_vm!(
            r#"
                REVERSE 3, 0
                BLKDROP 3
            "#,
            [int 1, int 2, int 3, int 4, int 5, int 6] => [int 1, int 2, int 3]
        );

        assert_run_vm!("BLKDROP2 3, 1", [int 1, int 2, int 3, int 4, int 5, int 6] => [int 1, int 2, int 6]);
        assert_run_vm!(
            r#"
                REVERSE 4, 0
                BLKDROP 3
            "#,
            [int 1, int 2, int 3, int 4, int 5, int 6] => [int 1, int 2, int 6]
        );

        assert_run_vm!("BLKDROP2 3, 2", [int 1, int 2, int 3, int 4, int 5, int 6] => [int 1, int 5, int 6]);
        assert_run_vm!(
            r#"
                REVERSE 5, 0
                BLKDROP 3
                REVERSE 2, 0
            "#,
            [int 1, int 2, int 3, int 4, int 5, int 6] => [int 1, int 5, int 6]
        );

        assert_run_vm!("BLKDROP2 2, 2", [int 1, int 2, int 3, int 4] => [int 3, int 4]);
        assert_run_vm!(
            r#"
                REVERSE 4, 0
                BLKDROP 2
                REVERSE 2, 0
            "#,
            [int 1, int 2, int 3, int 4] => [int 3, int 4]
        );
    }
}
