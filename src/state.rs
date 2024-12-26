use std::rc::Rc;

use anyhow::Result;
use bitflags::bitflags;
use everscale_types::cell::*;
use everscale_types::error::Error;
use num_bigint::BigInt;
use num_traits::Zero;
#[cfg(feature = "tracing")]
use tracing::instrument;

use crate::cont::{
    AgainCont, ArgContExt, ControlData, ControlRegs, ExcQuitCont, OrdCont, QuitCont, RcCont,
    RepeatCont, UntilCont, WhileCont,
};
use crate::dispatch::DispatchTable;
use crate::error::{VmException, VmResult};
use crate::gas::{GasConsumer, GasParams, LibraryProvider, NoLibraries};
use crate::instr::{codepage, codepage0};
use crate::stack::{RcStackValue, Stack};
use crate::util::OwnedCellSlice;

#[derive(Default)]
pub struct VmStateBuilder {
    pub code: OwnedCellSlice,
    pub data: Option<Cell>,
    pub stack: Vec<RcStackValue>,
    pub libraries: Option<Box<dyn LibraryProvider>>,
    pub c7: Option<Vec<RcStackValue>>,
    pub gas: GasParams,
    pub same_c3: bool,
    pub version: Option<VmVersion>,
    pub without_push0: bool,
    pub modifiers: BehaviouModifiers,
    pub debug: Option<Box<dyn std::fmt::Write>>,
}

impl VmStateBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn build(mut self) -> Result<VmState> {
        if self.same_c3 && !self.without_push0 {
            vm_log_trace!("implicit PUSH 0 at start");
            self.stack.push(Rc::new(BigInt::zero()));
        }

        let quit0 = QUIT0.with(Rc::clone);
        let quit1 = QUIT1.with(Rc::clone);
        let cp = codepage0();

        Ok(VmState {
            cr: ControlRegs {
                c: [
                    Some(quit0.clone()),
                    Some(quit1.clone()),
                    Some(EXC_QUIT.with(Rc::clone)),
                    Some(if self.same_c3 {
                        Rc::new(OrdCont::simple(self.code.clone(), cp.id()))
                    } else {
                        Rc::new(QuitCont { exit_code: 11 })
                    }),
                ],
                d: [
                    Some(self.data.unwrap_or_default()),
                    Some(Cell::empty_cell()),
                ],
                c7: Some(Rc::new(self.c7.unwrap_or_default())),
            },
            code: self.code,
            stack: Rc::new(Stack { items: self.stack }),
            commited_state: None,
            steps: 0,
            quit0,
            quit1,
            gas: GasConsumer::with_libraries(
                self.gas,
                self.libraries.unwrap_or_else(|| Box::new(NoLibraries)),
            ),
            cp,
            debug: self.debug,
            modifiers: self.modifiers,
            version: self.version.unwrap_or(VmState::DEFAULT_VERSION),
        })
    }

    pub fn with_libraries<T: LibraryProvider + 'static>(mut self, libraries: T) -> Self {
        self.libraries = Some(match castaway::cast!(libraries, Box<dyn LibraryProvider>) {
            Ok(libraries) => libraries,
            Err(libraries) => Box::new(libraries),
        });
        self
    }

    pub fn with_gas(mut self, gas: GasParams) -> Self {
        self.gas = gas;
        self
    }

    pub fn with_debug<T: std::fmt::Write + 'static>(mut self, stderr: T) -> Self {
        self.debug = Some(Box::new(stderr));
        self
    }

    pub fn with_code<T: Into<OwnedCellSlice>>(mut self, code: T) -> Self {
        self.code = code.into();
        self
    }

    pub fn with_data(mut self, data: Cell) -> Self {
        self.data = Some(data);
        self
    }

    pub fn with_same_c3(mut self) -> Self {
        self.same_c3 = true;
        self
    }

    pub fn without_push0(mut self) -> Self {
        self.without_push0 = true;
        self
    }

    pub fn with_stack<I: IntoIterator<Item = RcStackValue>>(mut self, values: I) -> Self {
        self.stack = values.into_iter().collect();
        self
    }

    pub fn with_c7(mut self, c7: Vec<RcStackValue>) -> Self {
        self.c7 = Some(c7);
        self
    }

    pub fn with_modifiers(mut self, modifiers: BehaviouModifiers) -> Self {
        self.modifiers = modifiers;
        self
    }

    pub fn with_version(mut self, version: VmVersion) -> Self {
        self.version = Some(version);
        self
    }
}

pub struct VmState {
    pub code: OwnedCellSlice,
    pub stack: Rc<Stack>,
    pub cr: ControlRegs,
    pub commited_state: Option<CommitedState>,
    pub steps: u64,
    pub quit0: Rc<QuitCont>,
    pub quit1: Rc<QuitCont>,
    pub gas: GasConsumer,
    pub cp: &'static DispatchTable,
    pub debug: Option<Box<dyn std::fmt::Write>>,
    pub modifiers: BehaviouModifiers,
    pub version: VmVersion,
}

impl VmState {
    pub const DEFAULT_VERSION: VmVersion = VmVersion::Ton(9);

    pub const MAX_DATA_DEPTH: u16 = 512;

    pub const ACTIONS_GLOBAL_IDX: usize = 1;
    pub const MSGS_SENT_GLOBAL_IDX: usize = 2;
    pub const UNIX_TIME_GLOBAL_IDX: usize = 3;
    pub const BLOCK_LT_GLOBAL_IDX: usize = 4;
    pub const TX_LT_GLOBAL_IDX: usize = 5;
    pub const RANDSEED_GLOBAL_IDX: usize = 6;
    pub const BALANCE_GLOBAL_IDX: usize = 7;
    pub const MYADDR_GLOBAL_IDX: usize = 8;
    pub const CONFIG_GLOBAL_IDX: usize = 9;
    pub const MYCODE_GLOBAL_IDX: usize = 10;
    pub const IN_MSG_VALUE_GLOBAL_IDX: usize = 11;
    pub const STORAGE_FEE_GLOBAL_IDX: usize = 12;
    pub const PREV_BLOCKS_GLOBAL_IDX: usize = 13;
    pub const PARSED_CONFIG_GLOBAL_IDX: usize = 14;
    pub const STORAGE_DEBT_GLOBAL_IDX: usize = 15;
    pub const PRECOMPILED_GAS_GLOBAL_IDX: usize = 16;

    thread_local! {
        static EMPTY_STACK: Rc<Stack> = Rc::new(Default::default());
    }

    pub fn builder() -> VmStateBuilder {
        VmStateBuilder::default()
    }

    #[cfg_attr(
        feature = "tracing",
        instrument(
            level = "trace",
            name = "vm_step",
            fields(n = self.steps),
            skip_all,
        )
    )]
    pub fn step(&mut self) -> VmResult<i32> {
        self.steps += 1;
        if !self.code.range().is_data_empty() {
            self.cp.dispatch(self)
        } else if !self.code.range().is_refs_empty() {
            vm_log_op!("implicit JMPREF");

            let next_cell = self.code.apply()?.get_reference_cloned(0)?;

            self.gas.try_consume_implicit_jmpref_gas()?;
            let code = self
                .gas
                .context()
                .load_cell(next_cell, LoadMode::Full)?
                .into();

            let cont = Rc::new(OrdCont::simple(code, self.cp.id()));
            self.jump(cont)
        } else {
            vm_log_op!("implicit RET");

            self.gas.try_consume_implicit_ret_gas()?;
            self.ret()
        }
    }

    pub fn run(&mut self) -> i32 {
        let mut res = 0;
        while res == 0 {
            res = match self.step() {
                Ok(res) => res,
                Err(e) if e.is_out_of_gas() => {
                    self.steps += 1;
                    self.throw_out_of_gas()
                }
                Err(e) => {
                    let exception = e.as_exception();
                    vm_log_trace!(e = ?exception, "handling exception: {e:?}");

                    self.steps += 1;
                    match self.throw_exception(exception as i32) {
                        Ok(res) => res,
                        Err(e) if e.is_out_of_gas() => {
                            self.steps += 1;
                            self.throw_out_of_gas()
                        }
                        Err(e) => {
                            vm_log_trace!(e = ?exception, "double exception: {e:?}");
                            return exception.as_exit_code();
                        }
                    }
                }
            };
        }

        // Try commit on ~(0) and ~(-1) exit codes
        if res | 1 == -1 && !self.try_commit() {
            vm_log_trace!("automatic commit failed");
            self.stack = Rc::new(Stack {
                items: vec![Rc::new(BigInt::default())],
            });
            return VmException::CellOverflow.as_exit_code();
        }

        res
    }

    pub fn try_commit(&mut self) -> bool {
        if let (Some(c4), Some(c5)) = (&self.cr.d[0], &self.cr.d[1]) {
            if c4.level() == 0
                && c5.level() == 0
                && c4.repr_depth() <= Self::MAX_DATA_DEPTH
                && c5.repr_depth() <= Self::MAX_DATA_DEPTH
            {
                self.commited_state = Some(CommitedState {
                    c4: c4.clone(),
                    c5: c5.clone(),
                });
                return true;
            }
        }

        false
    }

    pub fn force_commit(&mut self) -> Result<(), Error> {
        if self.try_commit() {
            Ok(())
        } else {
            Err(Error::CellOverflow)
        }
    }

    pub fn take_stack(&mut self) -> Rc<Stack> {
        std::mem::replace(&mut self.stack, Self::EMPTY_STACK.with(Rc::clone))
    }

    pub fn ref_to_cont(&mut self, code: Cell) -> VmResult<Rc<OrdCont>> {
        let code = self.gas.context().load_cell(code, LoadMode::Full)?;
        Ok(Rc::new(OrdCont::simple(code.into(), self.cp.id())))
    }

    pub fn c1_envelope_if(&mut self, cond: bool, cont: RcCont, save: bool) -> RcCont {
        if cond {
            self.c1_envelope(cont, save)
        } else {
            cont
        }
    }

    pub fn c1_envelope(&mut self, mut cont: RcCont, save: bool) -> RcCont {
        if save {
            if cont.get_control_data().is_none() {
                let mut c = ArgContExt {
                    data: Default::default(),
                    ext: cont,
                };
                c.data.save.define_c0(&self.cr.c[0]);
                c.data.save.define_c1(&self.cr.c[1]);

                cont = Rc::new(c);
            } else {
                let cont = dyn_clone::rc_make_mut(&mut cont);
                if let Some(data) = cont.get_control_data_mut() {
                    data.save.define_c0(&self.cr.c[0]);
                    data.save.define_c1(&self.cr.c[1]);
                }
            }
        }
        self.cr.c[1] = Some(cont.clone());
        cont
    }

    pub fn c1_save_set(&mut self) {
        let [c0, c1, ..] = &mut self.cr.c;

        if let Some(c0) = c0 {
            if c0.get_control_data().is_none() {
                let mut c = ArgContExt {
                    data: Default::default(),
                    ext: c0.clone(),
                };
                c.data.save.define_c1(c1);
                *c0 = Rc::new(c);
            } else {
                let c0 = dyn_clone::rc_make_mut(c0);
                if let Some(data) = c0.get_control_data_mut() {
                    data.save.define_c1(c1);
                }
            }
        }

        c1.clone_from(c0);
    }

    pub fn extract_cc(
        &mut self,
        mode: SaveCr,
        stack_copy: Option<u16>,
        nargs: Option<u16>,
    ) -> VmResult<Rc<OrdCont>> {
        let new_stack = match stack_copy {
            Some(0) => None,
            Some(n) if (n as usize) != self.stack.depth() => {
                let stack = ok!(Rc::make_mut(&mut self.stack).split_top(n as _).map(Some));
                self.gas.try_consume_stack_gas(stack.as_ref())?;
                stack
            }
            _ => Some(self.take_stack()),
        };

        let mut res = OrdCont {
            code: std::mem::take(&mut self.code),
            data: ControlData {
                nargs,
                stack: Some(self.take_stack()),
                save: Default::default(),
                cp: Some(self.cp.id()),
            },
        };
        if let Some(new_stack) = new_stack {
            self.stack = new_stack;
        }

        if mode.contains(SaveCr::C0) {
            res.data.save.c[0] = std::mem::replace(&mut self.cr.c[0], Some(self.quit0.clone()));
        }
        if mode.contains(SaveCr::C1) {
            res.data.save.c[1] = std::mem::replace(&mut self.cr.c[1], Some(self.quit1.clone()));
        }
        if mode.contains(SaveCr::C2) {
            res.data.save.c[2] = self.cr.c[2].take();
        }

        Ok(Rc::new(res))
    }

    pub fn throw_exception(&mut self, n: i32) -> VmResult<i32> {
        self.stack = Rc::new(Stack {
            items: vec![Rc::new(BigInt::zero()), Rc::new(BigInt::from(n))],
        });
        self.code = Default::default();
        self.gas.try_consume_exception_gas()?;
        let Some(c2) = self.cr.c[2].clone() else {
            vm_bail!(InvalidOpcode);
        };
        self.jump(c2)
    }

    pub fn throw_exception_with_arg(&mut self, n: i32, arg: RcStackValue) -> VmResult<i32> {
        self.stack = Rc::new(Stack {
            items: vec![arg, Rc::new(BigInt::from(n))],
        });
        self.code = Default::default();
        self.gas.try_consume_exception_gas()?;
        let Some(c2) = self.cr.c[2].clone() else {
            vm_bail!(InvalidOpcode);
        };
        self.jump(c2)
    }

    pub fn throw_out_of_gas(&mut self) -> i32 {
        let consumed = self.gas.gas_consumed();
        vm_log_trace!(consumed, limit = self.gas.gas_limit, "out of gas");
        self.stack = Rc::new(Stack {
            items: vec![Rc::new(BigInt::from(consumed))],
        });

        // No negation for unhandled exceptions (to make their faking impossible).
        VmException::OutOfGas as u8 as i32
    }

    pub fn call(&mut self, cont: RcCont) -> VmResult<i32> {
        if let Some(control_data) = cont.get_control_data() {
            if control_data.save.c[0].is_some() {
                // If cont has c0 then call reduces to a jump
                return self.jump(cont);
            }
            if control_data.stack.is_some() || control_data.nargs.is_some() {
                // If cont has non-empty stack or expects a fixed number of
                // arguments, call is not simple
                return self.call_ext(cont, None, None);
            }
        }

        // Create return continuation
        let mut ret = OrdCont::simple(std::mem::take(&mut self.code), self.cp.id());
        ret.data.save.c[0] = self.cr.c[0].take();
        self.cr.c[0] = Some(Rc::new(ret));

        // NOTE: cont.data.save.c[0] must not be set
        cont.jump(self)
    }

    pub fn call_ext(
        &mut self,
        mut cont: RcCont,
        pass_args: Option<u16>,
        ret_args: Option<u16>,
    ) -> VmResult<i32> {
        let (new_stack, c0) = if let Some(control_data) = cont.get_control_data() {
            if control_data.save.c[0].is_some() {
                // If cont has c0 then call reduces to a jump
                return self.jump(cont);
            }

            let current_depth = self.stack.depth();
            vm_ensure!(
                pass_args.unwrap_or_default() as usize <= current_depth
                    && control_data.nargs.unwrap_or_default() as usize <= current_depth,
                StackUnderflow(std::cmp::max(
                    pass_args.unwrap_or_default(),
                    control_data.nargs.unwrap_or_default()
                ) as _)
            );

            if let Some(pass_args) = pass_args {
                vm_ensure!(
                    control_data.nargs.unwrap_or_default() <= pass_args,
                    StackUnderflow(pass_args as _)
                );
            }

            let old_c0 = self.cr.c[0].take();
            self.cr.preclear(&control_data.save);

            let (copy, skip) = match (pass_args, control_data.nargs) {
                (Some(pass_args), Some(copy)) => (Some(copy as usize), (pass_args - copy) as usize),
                (Some(pass_args), None) => (Some(pass_args as usize), 0),
                _ => (None, 0),
            };

            let new_stack = match Rc::get_mut(&mut cont) {
                Some(cont) => cont
                    .get_control_data_mut()
                    .and_then(|control_data| control_data.stack.take()),
                None => cont
                    .get_control_data()
                    .and_then(|control_data| control_data.stack.clone()),
            };

            let new_stack = match new_stack {
                Some(mut stack) if !stack.items.is_empty() => {
                    let copy = copy.unwrap_or(current_depth);

                    let current_stack = Rc::make_mut(&mut self.stack);
                    ok!(Rc::make_mut(&mut stack).move_from_stack(current_stack, copy));
                    ok!(current_stack.pop_many(skip));
                    self.gas.try_consume_stack_gas(Some(&self.stack))?;

                    stack
                }
                _ => {
                    if let Some(copy) = copy {
                        let stack = ok!(Rc::make_mut(&mut self.stack).split_top_ext(copy, skip));
                        self.gas.try_consume_stack_gas(Some(&stack))?;
                        stack
                    } else {
                        self.take_stack()
                    }
                }
            };

            (new_stack, old_c0)
        } else {
            // Simple case without continuation data
            let new_stack = if let Some(pass_args) = pass_args {
                let stack = ok!(Rc::make_mut(&mut self.stack).split_top(pass_args as _));
                self.gas.try_consume_stack_gas(Some(&stack))?;
                stack
            } else {
                self.take_stack()
            };

            (new_stack, self.cr.c[0].take())
        };

        // Create a new stack from the top `pass_args` items of the current stack
        let mut ret = OrdCont {
            code: std::mem::take(&mut self.code),
            data: ControlData {
                save: Default::default(),
                nargs: ret_args,
                stack: Some(std::mem::replace(&mut self.stack, new_stack)),
                cp: Some(self.cp.id()),
            },
        };
        ret.data.save.c[0] = c0;
        self.cr.c[0] = Some(Rc::new(ret));

        cont.jump(self)
    }

    pub fn jump(&mut self, cont: RcCont) -> VmResult<i32> {
        if let Some(cont_data) = cont.get_control_data() {
            if cont_data.stack.is_some() || cont_data.nargs.is_some() {
                // Cont has a non-empty stack or expects a fixed number of arguments
                return self.jump_ext(cont, None);
            }
        }

        // The simplest continuation case:
        // - the continuation doesn't have its own stack
        // - `nargs` is not specified so it expects the full current stack
        //
        // So, we don't need to change anything to call it
        cont.jump(self)
    }

    pub fn jump_ext(&mut self, mut cont: RcCont, pass_args: Option<u16>) -> VmResult<i32> {
        // Either all values or the top n values in the current stack are
        // moved to the stack of the continuation, and only then is the
        // remainder of the current stack discarded.

        if let Some(control_data) = cont.get_control_data() {
            // n = self.stack.depth()
            // if has nargs:
            //     # From docs:
            //     n' = control_data.nargs - control_data.stack.depth()
            //     # From c++ impl:
            //     n' = control_data.nargs
            //     assert n' <= n
            // if pass_args is specified:
            //     n" = pass_args
            //     assert n" >= n'
            //
            // - n" (or n) of args are taken from the current stack
            // - n' (or n) of args are passed to the continuation

            let current_depth = self.stack.depth();
            vm_ensure!(
                pass_args.unwrap_or_default() as usize <= current_depth
                    && control_data.nargs.unwrap_or_default() as usize <= current_depth,
                StackUnderflow(std::cmp::max(
                    pass_args.unwrap_or_default(),
                    control_data.nargs.unwrap_or_default()
                ) as usize)
            );

            if let Some(pass_args) = pass_args {
                vm_ensure!(
                    control_data.nargs.unwrap_or_default() <= pass_args,
                    StackUnderflow(pass_args as usize)
                );
            }

            // Prepare the current savelist to be overwritten by the continuation
            self.preclear_cr(&control_data.save);

            // Compute the next stack depth
            let next_depth = control_data
                .nargs
                .or(pass_args)
                .map(|n| n as usize)
                .unwrap_or(current_depth);

            // Try to reuse continuation stack to reduce copies
            let cont_stack = match Rc::get_mut(&mut cont) {
                None => cont
                    .get_control_data()
                    .and_then(|control_data| control_data.stack.clone()),
                Some(cont) => cont
                    .get_control_data_mut()
                    .and_then(|control_data| control_data.stack.take()),
            };

            match cont_stack {
                // If continuation has a non-empty stack, extend it from the current stack
                Some(mut cont_stack) if !cont_stack.items.is_empty() => {
                    // TODO?: don't copy `self.stack` here
                    ok!(Rc::make_mut(&mut cont_stack)
                        .move_from_stack(Rc::make_mut(&mut self.stack), next_depth));
                    self.gas.try_consume_stack_gas(Some(&cont_stack))?;

                    self.stack = cont_stack;
                }
                // Ensure that the current stack has an exact number of items
                _ if next_depth < current_depth => {
                    ok!(Rc::make_mut(&mut self.stack).drop_bottom(current_depth - next_depth));
                    self.gas.try_consume_stack_depth_gas(next_depth as u64)?;
                }
                // Leave the current stack untouched
                _ => {}
            }
        } else if let Some(pass_args) = pass_args {
            // Try to leave only `pass_args` number of arguments in the current stack
            let Some(depth_diff) = self.stack.depth().checked_sub(pass_args as _) else {
                vm_bail!(StackUnderflow(pass_args as _));
            };

            if depth_diff > 0 {
                // Modify the current stack only when needed
                ok!(Rc::make_mut(&mut self.stack).drop_bottom(depth_diff));
                self.gas.try_consume_stack_depth_gas(pass_args as u64)?;
            }
        }

        // Proceed to the continuation
        cont.jump(self)
    }

    pub fn ret(&mut self) -> VmResult<i32> {
        let cont = ok!(self.take_c0());
        self.jump(cont)
    }

    pub fn ret_ext(&mut self, ret_args: Option<u16>) -> VmResult<i32> {
        let cont = ok!(self.take_c0());
        self.jump_ext(cont, ret_args)
    }

    pub fn ret_alt(&mut self) -> VmResult<i32> {
        let cont = ok!(self.take_c1());
        self.jump(cont)
    }

    pub fn ret_alt_ext(&mut self, ret_args: Option<u16>) -> VmResult<i32> {
        let cont = ok!(self.take_c1());
        self.jump_ext(cont, ret_args)
    }

    pub fn repeat(&mut self, body: RcCont, after: RcCont, n: u32) -> VmResult<i32> {
        self.jump(if n == 0 {
            drop(body);
            after
        } else {
            Rc::new(RepeatCont {
                count: n as _,
                body,
                after,
            })
        })
    }

    pub fn until(&mut self, body: RcCont, after: RcCont) -> VmResult<i32> {
        if !body.has_c0() {
            self.cr.c[0] = Some(Rc::new(UntilCont {
                body: body.clone(),
                after,
            }))
        }
        self.jump(body)
    }

    pub fn loop_while(&mut self, cond: RcCont, body: RcCont, after: RcCont) -> VmResult<i32> {
        if !cond.has_c0() {
            self.cr.c[0] = Some(Rc::new(WhileCont {
                check_cond: true,
                cond: cond.clone(),
                body,
                after,
            }));
        }
        self.jump(cond)
    }

    pub fn again(&mut self, body: RcCont) -> VmResult<i32> {
        self.jump(Rc::new(AgainCont { body }))
    }

    pub fn adjust_cr(&mut self, save: &ControlRegs) {
        self.cr.merge(save)
    }

    pub fn preclear_cr(&mut self, save: &ControlRegs) {
        self.cr.preclear(save)
    }

    pub fn set_c0(&mut self, cont: RcCont) {
        self.cr.c[0] = Some(cont);
    }

    pub fn set_code(&mut self, code: OwnedCellSlice, cp: u16) -> VmResult<()> {
        self.code = code;
        self.force_cp(cp)
    }

    pub fn force_cp(&mut self, cp: u16) -> VmResult<()> {
        let Some(cp) = codepage(cp) else {
            vm_bail!(InvalidOpcode);
        };
        self.cp = cp;
        Ok(())
    }

    fn take_c0(&mut self) -> VmResult<RcCont> {
        let Some(cont) = std::mem::replace(&mut self.cr.c[0], Some(self.quit0.clone())) else {
            vm_bail!(InvalidOpcode);
        };
        Ok(cont)
    }

    fn take_c1(&mut self) -> VmResult<RcCont> {
        let Some(cont) = std::mem::replace(&mut self.cr.c[1], Some(self.quit1.clone())) else {
            vm_bail!(InvalidOpcode);
        };
        Ok(cont)
    }
}

#[derive(Default, Debug, Clone, Copy)]
pub struct BehaviouModifiers {
    pub stop_on_accept: bool,
    pub chksig_always_succeed: bool,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum VmVersion {
    Everscale(u32),
    Ton(u32),
}

impl VmVersion {
    pub fn is_ton<R: std::ops::RangeBounds<u32>>(&self, range: R) -> bool {
        matches!(self, Self::Ton(version) if range.contains(version))
    }

    pub fn require_ton<R: std::ops::RangeBounds<u32>>(&self, range: R) -> VmResult<()> {
        vm_ensure!(self.is_ton(range), InvalidOpcode);
        Ok(())
    }
}

pub struct CommitedState {
    pub c4: Cell,
    pub c5: Cell,
}

bitflags! {
    pub struct SaveCr: u8 {
        const NONE = 0;

        const C0 = 1;
        const C1 = 1 << 1;
        const C2 = 1 << 2;

        const C0_C1 = SaveCr::C0.bits() | SaveCr::C1.bits();
        const FULL = SaveCr::C0_C1.bits() | SaveCr::C2.bits();
    }
}

thread_local! {
    static QUIT0: Rc<QuitCont> = Rc::new(QuitCont { exit_code: 0 });
    static QUIT1: Rc<QuitCont> = Rc::new(QuitCont { exit_code: 1 });
    static EXC_QUIT: Rc<ExcQuitCont> = Rc::new(ExcQuitCont);
}
