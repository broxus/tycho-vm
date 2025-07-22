use std::mem::ManuallyDrop;
use std::rc::Rc;

use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};
use tycho_types::error::Error;
use tycho_types::prelude::*;

use crate::cont::{Cont, RcCont, load_cont};
use crate::error::{VmError, VmResult};
use crate::saferc::{SafeDelete, SafeRc, SafeRcMakeMut};
use crate::util::{OwnedCellSlice, ensure_empty_slice};

/// A stack of values.
#[derive(Debug, Default, Clone)]
pub struct Stack {
    pub items: Vec<RcStackValue>,
}

impl Stack {
    pub const MAX_DEPTH: usize = 0xffffff;

    pub fn make_null() -> RcStackValue {
        thread_local! {
            static NULL: RcStackValue = SafeRc::new_dyn_value(());
        }
        NULL.with(SafeRc::clone)
    }

    pub fn make_nan() -> RcStackValue {
        thread_local! {
            static NAN: RcStackValue = SafeRc::new_dyn_value(NaN);
        }
        NAN.with(SafeRc::clone)
    }

    pub fn make_empty_tuple() -> RcStackValue {
        thread_local! {
            static EMPTY_TUPLE: RcStackValue = SafeRc::new_dyn_value(Vec::new());
        }
        EMPTY_TUPLE.with(SafeRc::clone)
    }

    pub fn make_zero() -> RcStackValue {
        thread_local! {
            static ONE: RcStackValue = SafeRc::new_dyn_value(BigInt::zero());
        }
        ONE.with(SafeRc::clone)
    }

    pub fn make_minus_one() -> RcStackValue {
        thread_local! {
            static MINUS_ONE: RcStackValue = SafeRc::new_dyn_value(-BigInt::one());
        }
        MINUS_ONE.with(SafeRc::clone)
    }

    pub fn make_one() -> RcStackValue {
        thread_local! {
            static ONE: RcStackValue = SafeRc::new_dyn_value(BigInt::one());
        }
        ONE.with(SafeRc::clone)
    }

    pub fn make_bool(value: bool) -> RcStackValue {
        if value {
            Self::make_minus_one()
        } else {
            Self::make_zero()
        }
    }

    /// Loads stack value from the cell. Returns an error if data was not fully used.
    pub fn load_stack_value_from_cell(cell: &DynCell) -> Result<RcStackValue, Error> {
        let slice = &mut ok!(cell.as_slice());
        let res = ok!(Self::load_stack_value(slice));
        ok!(ensure_empty_slice(slice));
        Ok(res)
    }

    /// Loads stack value from the slice advancing its cursors.
    pub fn load_stack_value(slice: &mut CellSlice) -> Result<RcStackValue, Error> {
        let ty = ok!(slice.load_u8());
        Ok(match ty {
            // vm_stk_null#00 = VmStackValue;
            0 => Stack::make_null(),
            // vm_stk_tinyint#01 value:int64 = VmStackValue;
            1 => {
                let value = ok!(slice.load_u64()) as i64;
                SafeRc::new_dyn_value(BigInt::from(value))
            }
            2 => {
                let t = ok!(slice.get_u8(0));
                if t == 0xff {
                    // vm_stk_nan#02ff = VmStackValue;
                    ok!(slice.skip_first(8, 0));
                    Stack::make_nan()
                } else if t / 2 == 0 {
                    // vm_stk_int#0201_ value:int257 = VmStackValue;
                    ok!(slice.skip_first(7, 0));
                    SafeRc::new_dyn_value(ok!(slice.load_bigint(257, true)))
                } else {
                    return Err(Error::InvalidData);
                }
            }
            // vm_stk_cell#03 cell:^Cell = VmStackValue;
            3 => SafeRc::new_dyn_value(ok!(slice.load_reference_cloned())),
            // vm_stk_slice#04 _:VmCellSlice = VmStackValue;
            4 => SafeRc::new_dyn_value(ok!(load_slice_as_stack_value(slice))),
            // vm_stk_builder#05 cell:^Cell = VmStackValue;
            5 => {
                let cell = ok!(slice.load_reference());
                let mut builder = CellBuilder::new();
                ok!(builder.store_slice(cell.as_slice_allow_exotic()));
                SafeRc::new_dyn_value(builder)
            }
            // vm_stk_cont#06 cont:VmCont = VmStackValue;
            6 => ok!(load_cont(slice)).into_dyn_value(),
            // vm_stk_tuple#07 len:(## 16) data:(VmTuple len) = VmStackValue;
            7 => {
                let len = ok!(slice.load_u16()) as usize;
                let mut tuple = Vec::with_capacity(std::cmp::min(len, 128));

                match len {
                    0 => {}
                    1 => {
                        let value = ok!(slice.load_reference());
                        tuple.push(ok!(Self::load_stack_value_from_cell(value)));
                    }
                    _ => {
                        let mut head = ok!(slice.load_reference());
                        let mut tail = ok!(slice.load_reference());
                        tuple.push(ok!(Self::load_stack_value_from_cell(tail)));

                        for _ in 0..len - 2 {
                            let slice = &mut ok!(head.as_slice());
                            head = ok!(slice.load_reference());
                            tail = ok!(slice.load_reference());
                            ok!(ensure_empty_slice(slice));
                            tuple.push(ok!(Self::load_stack_value_from_cell(tail)));
                        }

                        tuple.push(ok!(Self::load_stack_value_from_cell(head)));
                        tuple.reverse();
                    }
                }

                SafeRc::new_dyn_value(tuple)
            }
            _ => return Err(Error::InvalidTag),
        })
    }

    pub fn with_items(items: Vec<RcStackValue>) -> Self {
        Self { items }
    }

    pub fn depth(&self) -> usize {
        self.items.len()
    }

    pub fn display_dump(&self, verbose: bool) -> impl std::fmt::Display + '_ {
        struct DisplayStack<'a> {
            items: &'a Vec<RcStackValue>,
            #[allow(unused)]
            verbose: bool,
        }

        impl std::fmt::Display for DisplayStack<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                (self.items as &dyn StackValue).display_list().fmt(f)
            }
        }

        DisplayStack {
            items: &self.items,
            verbose,
        }
    }

    /// Reserves capacity for at least `additional` more elements to be inserted.
    pub fn reserve(&mut self, additional: usize) {
        self.items.reserve(additional);
    }

    pub fn push<T: StackValue + 'static>(&mut self, item: T) -> VmResult<()> {
        self.push_raw(SafeRc::new_dyn_value(item))
    }

    pub fn push_raw<T: StackValue + ?Sized + 'static>(&mut self, item: SafeRc<T>) -> VmResult<()> {
        vm_ensure!(
            self.depth() < Self::MAX_DEPTH,
            StackUnderflow(Self::MAX_DEPTH)
        );

        self.items.push(item.into_dyn_value());
        Ok(())
    }

    pub fn push_opt<T: StackValue + 'static>(&mut self, value: Option<T>) -> VmResult<()> {
        match value {
            None => self.push_null(),
            Some(value) => self.push(value),
        }
    }

    pub fn push_opt_raw<T: StackValue + ?Sized + 'static>(
        &mut self,
        item: Option<SafeRc<T>>,
    ) -> VmResult<()> {
        match item {
            None => self.push_null(),
            Some(item) => self.push_raw(item),
        }
    }

    pub fn push_nth(&mut self, idx: usize) -> VmResult<()> {
        let depth = self.depth();
        vm_ensure!(idx < depth, StackUnderflow(idx));
        vm_ensure!(depth + 1 < Self::MAX_DEPTH, StackUnderflow(Self::MAX_DEPTH));
        self.items.push(self.items[depth - idx - 1].clone());
        Ok(())
    }

    pub fn push_null(&mut self) -> VmResult<()> {
        self.push_raw(Self::make_null())
    }

    pub fn push_nan(&mut self) -> VmResult<()> {
        self.push_raw(Self::make_nan())
    }

    pub fn push_bool(&mut self, value: bool) -> VmResult<()> {
        self.push_raw(Self::make_bool(value))
    }

    pub fn push_zero(&mut self) -> VmResult<()> {
        self.push_raw(Self::make_zero())
    }

    pub fn push_int<T: Into<BigInt>>(&mut self, value: T) -> VmResult<()> {
        // TODO: Inline some numbers as thread-local constants to avoid some allocations
        self.push(value.into())
    }

    pub fn push_raw_int(&mut self, value: SafeRc<BigInt>, quiet: bool) -> VmResult<()> {
        if value.bitsize(true) <= 257 {
            self.push_raw(value)
        } else if quiet {
            self.push_nan()
        } else {
            vm_bail!(IntegerOverflow)
        }
    }

    pub fn move_from_stack(&mut self, other: &mut Self, n: usize) -> VmResult<()> {
        let Some(new_other_len) = other.depth().checked_sub(n) else {
            vm_bail!(StackUnderflow(n));
        };
        self.items.extend(other.items.drain(new_other_len..));
        Ok(())
    }

    pub fn split_top(&mut self, n: usize) -> VmResult<SafeRc<Self>> {
        let Some(new_depth) = self.depth().checked_sub(n) else {
            vm_bail!(StackUnderflow(n));
        };
        Ok(SafeRc::new(Self {
            items: self.items.drain(new_depth..).collect(),
        }))
    }

    pub fn split_top_ext(&mut self, n: usize, drop: usize) -> VmResult<SafeRc<Self>> {
        let Some(new_depth) = self.depth().checked_sub(n + drop) else {
            vm_bail!(StackUnderflow(n + drop));
        };
        let res = SafeRc::new(Self {
            items: self.items.drain(new_depth + drop..).collect(),
        });
        self.items.truncate(new_depth);
        Ok(res)
    }

    pub fn pop(&mut self) -> VmResult<RcStackValue> {
        let Some(item) = self.items.pop() else {
            vm_bail!(StackUnderflow(0));
        };
        Ok(item)
    }

    pub fn pop_bool(&mut self) -> VmResult<bool> {
        Ok(!ok!(self.pop_int()).is_zero())
    }

    pub fn pop_int(&mut self) -> VmResult<SafeRc<BigInt>> {
        ok!(self.pop()).into_int()
    }

    pub fn pop_int_or_nan(&mut self) -> VmResult<Option<SafeRc<BigInt>>> {
        let value = ok!(self.pop());
        if value.ty() == StackValueType::Int && value.as_int().is_none() {
            Ok(None)
        } else {
            value.into_int().map(Some)
        }
    }

    pub fn pop_smallint_range(&mut self, min: u32, max: u32) -> VmResult<u32> {
        let item = self.pop_int()?;
        if let Some(item) = item.to_u32() {
            if item >= min && item <= max {
                return Ok(item);
            }
        }
        vm_bail!(IntegerOutOfRange {
            min: min as isize,
            max: max as isize,
            actual: item.to_string(),
        })
    }

    pub fn pop_long_range(&mut self, min: u64, max: u64) -> VmResult<u64> {
        let item = self.pop_int()?;
        if let Some(item) = item.to_u64() {
            if item >= min && item <= max {
                return Ok(item);
            }
        }
        vm_bail!(IntegerOutOfRange {
            min: min as isize,
            max: max as isize,
            actual: item.to_string(),
        })
    }

    pub fn pop_smallint_signed_range(&mut self, min: i32, max: i32) -> VmResult<i32> {
        let item = self.pop_int()?;
        into_signed_range(item, min, max)
    }

    pub fn pop_smallint_signed_range_or_null(
        &mut self,
        min: i32,
        max: i32,
    ) -> VmResult<Option<i32>> {
        let item = ok!(self.pop());
        if item.ty() == StackValueType::Null {
            return Ok(None);
        }
        into_signed_range(item.into_int()?, min, max).map(Some)
    }

    pub fn pop_tuple(&mut self) -> VmResult<SafeRc<Tuple>> {
        self.pop()?.into_tuple()
    }

    pub fn pop_tuple_range(&mut self, min_len: u32, max_len: u32) -> VmResult<SafeRc<Tuple>> {
        let tuple = self.pop()?.into_tuple()?;
        vm_ensure!(
            (min_len as usize..=max_len as usize).contains(&tuple.len()),
            InvalidType {
                expected: StackValueType::Tuple,
                actual: StackValueType::Tuple,
            }
        );
        Ok(tuple)
    }

    pub fn pop_opt_tuple_range(
        &mut self,
        min_len: u32,
        max_len: u32,
    ) -> VmResult<Option<SafeRc<Tuple>>> {
        let tuple = {
            let value = self.pop()?;
            if value.is_null() {
                return Ok(None);
            }
            value.into_tuple()?
        };

        vm_ensure!(
            (min_len as usize..=max_len as usize).contains(&tuple.len()),
            InvalidType {
                expected: StackValueType::Tuple,
                actual: StackValueType::Tuple,
            }
        );
        Ok(Some(tuple))
    }

    pub fn pop_cont(&mut self) -> VmResult<RcCont> {
        self.pop()?.into_cont()
    }

    pub fn pop_cs(&mut self) -> VmResult<SafeRc<OwnedCellSlice>> {
        self.pop()?.into_cell_slice()
    }

    pub fn pop_builder(&mut self) -> VmResult<SafeRc<CellBuilder>> {
        self.pop()?.into_cell_builder()
    }

    pub fn pop_cell(&mut self) -> VmResult<SafeRc<Cell>> {
        self.pop()?.into_cell()
    }

    pub fn pop_cell_opt(&mut self) -> VmResult<Option<SafeRc<Cell>>> {
        let sv = self.pop()?;
        if sv.is_null() {
            Ok(None)
        } else {
            sv.into_cell().map(Some)
        }
    }

    pub fn pop_many(&mut self, n: usize) -> VmResult<()> {
        let Some(new_len) = self.depth().checked_sub(n) else {
            vm_bail!(StackUnderflow(n));
        };
        self.items.truncate(new_len);
        Ok(())
    }

    pub fn drop_bottom(&mut self, n: usize) -> VmResult<()> {
        vm_ensure!(n <= self.depth(), StackUnderflow(n));
        self.items.drain(..n);
        Ok(())
    }

    pub fn swap(&mut self, lhs: usize, rhs: usize) -> VmResult<()> {
        let depth = self.depth();
        vm_ensure!(lhs < depth, StackUnderflow(lhs));
        vm_ensure!(rhs < depth, StackUnderflow(rhs));
        self.items.swap(depth - lhs - 1, depth - rhs - 1);
        Ok(())
    }

    pub fn reverse_range(&mut self, offset: usize, n: usize) -> VmResult<()> {
        let depth = self.depth();
        vm_ensure!(offset < depth, StackUnderflow(offset));
        vm_ensure!(offset + n <= depth, StackUnderflow(offset + n));
        self.items[depth - offset - n..depth - offset].reverse();
        Ok(())
    }

    pub fn fetch(&self, idx: usize) -> VmResult<&RcStackValue> {
        let depth = self.depth();
        vm_ensure!(idx < depth, StackUnderflow(idx));
        Ok(&self.items[depth - idx - 1])
    }

    pub fn get_exit_arg(&self) -> Option<i32> {
        let last = self.items.last()?;
        let last = last.as_int()?;
        last.to_i32()
    }
}

fn into_signed_range(item: SafeRc<BigInt>, min: i32, max: i32) -> VmResult<i32> {
    if let Some(item) = item.to_i32() {
        if item >= min && item <= max {
            return Ok(item);
        }
    }
    vm_bail!(IntegerOutOfRange {
        min: min as isize,
        max: max as isize,
        actual: item.to_string(),
    })
}

impl SafeRcMakeMut for Stack {
    #[inline]
    fn rc_make_mut(rc: &mut Rc<Self>) -> &mut Self {
        Rc::make_mut(rc)
    }
}

impl FromIterator<RcStackValue> for Stack {
    #[inline]
    fn from_iter<T: IntoIterator<Item = RcStackValue>>(iter: T) -> Self {
        Self {
            items: Vec::<RcStackValue>::from_iter(iter),
        }
    }
}

// TODO: impl store with limit
impl Store for Stack {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        let depth = self.depth();
        if depth > Self::MAX_DEPTH {
            return Err(Error::IntOverflow);
        }
        ok!(builder.store_uint(depth as _, 24));

        if let Some((last, items)) = self.items.split_last() {
            let mut rest = Cell::empty_cell();
            for item in items {
                let mut builder = CellBuilder::new();
                ok!(builder.store_reference(rest));
                ok!(item.store_as_stack_value(&mut builder, context));
                rest = ok!(builder.build_ext(context));
            }

            ok!(builder.store_reference(rest));
            ok!(last.store_as_stack_value(builder, context));
        }
        Ok(())
    }
}

impl<'a> Load<'a> for Stack {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let depth = ok!(slice.load_uint(24)) as usize;
        if depth == 0 {
            return Ok(Stack::default());
        }

        let mut result = Stack {
            items: Vec::with_capacity(std::cmp::min(depth, 128)),
        };

        let mut rest = ok!(slice.load_reference());
        result.items.push(ok!(Self::load_stack_value(slice)));

        if depth > 1 {
            for _ in 0..depth - 1 {
                let slice = &mut ok!(rest.as_slice());
                rest = ok!(slice.load_reference());
                result.items.push(ok!(Self::load_stack_value(slice)));
                ok!(ensure_empty_slice(slice));
            }

            ok!(ensure_empty_slice(&ok!(rest.as_slice())));

            result.items.reverse();
        }

        Ok(result)
    }
}

// === StackValue trait ===

/// [`Stack`] item.
pub type RcStackValue = SafeRc<dyn StackValue>;

/// A value type of [`StackValue`].
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum StackValueType {
    Null,
    Int,
    Cell,
    Slice,
    Builder,
    Cont,
    Tuple,
}

/// Interface of a [`Stack`] item.
pub trait StackValue: SafeDelete + std::fmt::Debug {
    fn rc_into_dyn(self: Rc<Self>) -> Rc<dyn StackValue>;

    fn ty(&self) -> StackValueType;

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error>;

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;

    fn as_int(&self) -> Option<&BigInt> {
        None
    }

    fn try_as_int(&self) -> VmResult<&BigInt> {
        match self.as_int() {
            Some(value) => Ok(value),
            None => Err(invalid_type(self.ty(), StackValueType::Int)),
        }
    }

    fn rc_into_int(self: Rc<Self>) -> VmResult<Rc<BigInt>> {
        Err(invalid_type(self.ty(), StackValueType::Int))
    }

    fn as_cell(&self) -> Option<&Cell> {
        None
    }

    fn try_as_cell(&self) -> VmResult<&Cell> {
        match self.as_cell() {
            Some(value) => Ok(value),
            None => Err(invalid_type(self.ty(), StackValueType::Cell)),
        }
    }

    fn rc_into_cell(self: Rc<Self>) -> VmResult<Rc<Cell>> {
        Err(invalid_type(self.ty(), StackValueType::Cell))
    }

    fn as_cell_slice(&self) -> Option<&OwnedCellSlice> {
        None
    }

    fn try_as_cell_slice(&self) -> VmResult<&OwnedCellSlice> {
        match self.as_cell_slice() {
            Some(value) => Ok(value),
            None => Err(invalid_type(self.ty(), StackValueType::Slice)),
        }
    }

    fn rc_into_cell_slice(self: Rc<Self>) -> VmResult<Rc<OwnedCellSlice>> {
        Err(invalid_type(self.ty(), StackValueType::Slice))
    }

    fn as_cell_builder(&self) -> Option<&CellBuilder> {
        None
    }

    fn try_as_cell_builder(&self) -> VmResult<&CellBuilder> {
        match self.as_cell_builder() {
            Some(value) => Ok(value),
            None => Err(invalid_type(self.ty(), StackValueType::Builder)),
        }
    }

    fn rc_into_cell_builder(self: Rc<Self>) -> VmResult<Rc<CellBuilder>> {
        Err(invalid_type(self.ty(), StackValueType::Builder))
    }

    fn as_cont(&self) -> Option<&dyn Cont> {
        None
    }

    fn try_as_cont(&self) -> VmResult<&dyn Cont> {
        match self.as_cont() {
            Some(value) => Ok(value),
            None => Err(invalid_type(self.ty(), StackValueType::Cont)),
        }
    }

    fn rc_into_cont(self: Rc<Self>) -> VmResult<Rc<dyn Cont>> {
        Err(invalid_type(self.ty(), StackValueType::Cont))
    }

    fn as_tuple(&self) -> Option<&[RcStackValue]> {
        None
    }

    fn try_as_tuple(&self) -> VmResult<&[RcStackValue]> {
        match self.as_tuple() {
            Some(value) => Ok(value),
            None => Err(invalid_type(self.ty(), StackValueType::Tuple)),
        }
    }

    fn rc_into_tuple(self: Rc<Self>) -> VmResult<Rc<Tuple>> {
        Err(invalid_type(self.ty(), StackValueType::Tuple))
    }
}

impl dyn StackValue + '_ {
    pub fn is_null(&self) -> bool {
        self.ty() == StackValueType::Null
    }

    pub fn is_tuple(&self) -> bool {
        self.ty() == StackValueType::Tuple
    }

    pub fn as_tuple_range(&self, min_len: u32, max_len: u32) -> Option<&[RcStackValue]> {
        let tuple = self.as_tuple()?;
        (min_len as usize..=max_len as usize)
            .contains(&tuple.len())
            .then_some(tuple)
    }

    pub fn as_pair(&self) -> Option<(&dyn StackValue, &dyn StackValue)> {
        match self.as_tuple()? {
            [first, second] => Some((first.as_ref(), second.as_ref())),
            _ => None,
        }
    }

    pub fn as_list(&self) -> Option<(&dyn StackValue, &dyn StackValue)> {
        let (head, tail) = self.as_pair()?;

        let mut next = tail;
        while !next.is_null() {
            let (_, tail) = next.as_pair()?;
            next = tail;
        }

        Some((head, tail))
    }

    pub fn display_list(&self) -> impl std::fmt::Display + '_ {
        pub struct DisplayList<'a>(&'a dyn StackValue);

        impl std::fmt::Display for DisplayList<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.0.fmt_list(f)
            }
        }

        DisplayList(self)
    }

    fn fmt_list(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_null() {
            f.write_str("()")
        } else if let Some(tuple) = self.as_tuple() {
            if let Some((head, tail)) = self.as_list() {
                f.write_str("(")?;
                head.fmt_list(f)?;
                tail.fmt_list_tail(f)?;
                return Ok(());
            }

            f.write_str("[")?;
            let mut first = true;
            for item in tuple {
                if !std::mem::take(&mut first) {
                    f.write_str(" ")?;
                }
                item.as_ref().fmt_list(f)?;
            }
            f.write_str("]")?;

            Ok(())
        } else {
            self.fmt_dump(f)
        }
    }

    fn fmt_list_tail(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut item = self;
        while !item.is_null() {
            let Some((head, tail)) = item.as_pair() else {
                f.write_str(" . ")?;
                item.fmt_list(f)?;
                break;
            };

            f.write_str(" ")?;
            head.fmt_list(f)?;
            item = tail;
        }
        f.write_str(")")
    }
}

/// Static-dispatch type extension for [`StackValue`].
pub trait StaticStackValue: StackValue {
    type DynRef<'a>;

    fn known_ty() -> StackValueType;
    fn from_dyn(value: Rc<dyn StackValue>) -> VmResult<Rc<Self>>;
    fn from_dyn_ref(value: &dyn StackValue) -> VmResult<Self::DynRef<'_>>;
}

fn invalid_type(actual: StackValueType, expected: StackValueType) -> Box<VmError> {
    Box::new(VmError::InvalidType { expected, actual })
}

// === Null ===

impl StackValue for () {
    #[inline]
    fn rc_into_dyn(self: Rc<Self>) -> Rc<dyn StackValue> {
        self
    }

    fn ty(&self) -> StackValueType {
        StackValueType::Null
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        _: &dyn CellContext,
    ) -> Result<(), Error> {
        // vm_stk_null#00 = VmStackValue;
        builder.store_zeros(8)
    }

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("(null)")
    }
}

// === Int (NaN) ===

/// Invalid integer stack value.
#[derive(Debug, Clone, Copy)]
pub struct NaN;

impl StackValue for NaN {
    #[inline]
    fn rc_into_dyn(self: Rc<Self>) -> Rc<dyn StackValue> {
        self
    }

    fn ty(&self) -> StackValueType {
        StackValueType::Int
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        _: &dyn CellContext,
    ) -> Result<(), Error> {
        // vm_stk_nan#02ff = VmStackValue;
        builder.store_u16(0x02ff)
    }

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("NaN")
    }

    fn try_as_int(&self) -> VmResult<&BigInt> {
        vm_bail!(IntegerOverflow);
    }

    fn rc_into_int(self: Rc<Self>) -> VmResult<Rc<BigInt>> {
        vm_bail!(IntegerOverflow);
    }
}

impl SafeRcMakeMut for NaN {
    #[inline]
    fn rc_make_mut(rc: &mut Rc<Self>) -> &mut Self {
        Rc::make_mut(rc)
    }
}

// === Int ===

impl StackValue for BigInt {
    #[inline]
    fn rc_into_dyn(self: Rc<Self>) -> Rc<dyn StackValue> {
        self
    }

    fn ty(&self) -> StackValueType {
        StackValueType::Int
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        _: &dyn CellContext,
    ) -> Result<(), Error> {
        let bitsize = self.bitsize(true);
        if bitsize <= 64 {
            // vm_stk_tinyint#01 value:int64 = VmStackValue;
            ok!(builder.store_u8(0x01));
            builder.store_bigint(self, 64, true)
        } else {
            // vm_stk_int#0201_ value:int257 = VmStackValue;
            ok!(builder.store_uint(0x0200 >> 1, 15));
            builder.store_bigint(self, 257, true)
        }
    }

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }

    fn as_int(&self) -> Option<&BigInt> {
        Some(self)
    }

    fn rc_into_int(self: Rc<Self>) -> VmResult<Rc<BigInt>> {
        Ok(self)
    }
}

impl StaticStackValue for BigInt {
    type DynRef<'a> = &'a BigInt;

    fn known_ty() -> StackValueType {
        StackValueType::Int
    }

    fn from_dyn(value: Rc<dyn StackValue>) -> VmResult<Rc<Self>> {
        value.rc_into_int()
    }

    fn from_dyn_ref(value: &dyn StackValue) -> VmResult<Self::DynRef<'_>> {
        match value.as_int() {
            Some(value) => Ok(value),
            None => vm_bail!(InvalidType {
                expected: StackValueType::Int,
                actual: value.ty(),
            }),
        }
    }
}

impl SafeRcMakeMut for BigInt {
    #[inline]
    fn rc_make_mut(rc: &mut Rc<Self>) -> &mut Self {
        Rc::make_mut(rc)
    }
}

// === Cell ===

impl StackValue for Cell {
    #[inline]
    fn rc_into_dyn(self: Rc<Self>) -> Rc<dyn StackValue> {
        self
    }

    fn ty(&self) -> StackValueType {
        StackValueType::Cell
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        _: &dyn CellContext,
    ) -> Result<(), Error> {
        // vm_stk_cell#03 cell:^Cell = VmStackValue;
        ok!(builder.store_u8(0x03));
        builder.store_reference(self.clone())
    }

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "C{{{:X}}}", self.repr_hash())
    }

    fn as_cell(&self) -> Option<&Cell> {
        Some(self)
    }

    fn rc_into_cell(self: Rc<Self>) -> VmResult<Rc<Cell>> {
        Ok(self)
    }
}

impl StaticStackValue for Cell {
    type DynRef<'a> = &'a Cell;

    fn known_ty() -> StackValueType {
        StackValueType::Cell
    }

    fn from_dyn(value: Rc<dyn StackValue>) -> VmResult<Rc<Self>> {
        value.rc_into_cell()
    }

    fn from_dyn_ref(value: &dyn StackValue) -> VmResult<Self::DynRef<'_>> {
        match value.as_cell() {
            Some(value) => Ok(value),
            None => vm_bail!(InvalidType {
                expected: StackValueType::Cell,
                actual: value.ty(),
            }),
        }
    }
}

impl SafeRcMakeMut for Cell {
    #[inline]
    fn rc_make_mut(rc: &mut Rc<Self>) -> &mut Self {
        Rc::make_mut(rc)
    }
}

// === CellSlice ===

impl StackValue for OwnedCellSlice {
    #[inline]
    fn rc_into_dyn(self: Rc<Self>) -> Rc<dyn StackValue> {
        self
    }

    fn ty(&self) -> StackValueType {
        StackValueType::Slice
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        _: &dyn CellContext,
    ) -> Result<(), Error> {
        // vm_stk_slice#04 _:VmCellSlice = VmStackValue;
        ok!(builder.store_u8(0x04));
        store_slice_as_stack_value(self, builder)
    }

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }

    fn as_cell_slice(&self) -> Option<&OwnedCellSlice> {
        Some(self)
    }

    fn rc_into_cell_slice(self: Rc<Self>) -> VmResult<Rc<OwnedCellSlice>> {
        Ok(self)
    }
}

impl StaticStackValue for OwnedCellSlice {
    type DynRef<'a> = &'a OwnedCellSlice;

    fn known_ty() -> StackValueType {
        StackValueType::Slice
    }

    fn from_dyn(value: Rc<dyn StackValue>) -> VmResult<Rc<Self>> {
        value.rc_into_cell_slice()
    }

    fn from_dyn_ref(value: &dyn StackValue) -> VmResult<Self::DynRef<'_>> {
        match value.as_cell_slice() {
            Some(value) => Ok(value),
            None => vm_bail!(InvalidType {
                expected: StackValueType::Slice,
                actual: value.ty(),
            }),
        }
    }
}

impl SafeRcMakeMut for OwnedCellSlice {
    #[inline]
    fn rc_make_mut(rc: &mut Rc<Self>) -> &mut Self {
        Rc::make_mut(rc)
    }
}

// === CellBuilder ===

impl StackValue for CellBuilder {
    #[inline]
    fn rc_into_dyn(self: Rc<Self>) -> Rc<dyn StackValue> {
        self
    }

    fn ty(&self) -> StackValueType {
        StackValueType::Builder
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        let mut b = self.clone();
        // NOTE: We cannot serialize builders with partially built
        // exotic cells because it will fail.
        b.set_exotic(false);

        // vm_stk_builder#05 cell:^Cell = VmStackValue;
        ok!(builder.store_u8(0x05));
        builder.store_reference(ok!(b.build_ext(context)))
    }

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BC{{{}}}", self.display_data())
    }

    fn as_cell_builder(&self) -> Option<&CellBuilder> {
        Some(self)
    }

    fn rc_into_cell_builder(self: Rc<Self>) -> VmResult<Rc<CellBuilder>> {
        Ok(self)
    }
}

impl StaticStackValue for CellBuilder {
    type DynRef<'a> = &'a CellBuilder;

    fn known_ty() -> StackValueType {
        StackValueType::Builder
    }

    fn from_dyn(value: Rc<dyn StackValue>) -> VmResult<Rc<Self>> {
        value.rc_into_cell_builder()
    }

    fn from_dyn_ref(value: &dyn StackValue) -> VmResult<Self::DynRef<'_>> {
        match value.as_cell_builder() {
            Some(value) => Ok(value),
            None => vm_bail!(InvalidType {
                expected: StackValueType::Builder,
                actual: value.ty(),
            }),
        }
    }
}

impl SafeRcMakeMut for CellBuilder {
    #[inline]
    fn rc_make_mut(rc: &mut Rc<Self>) -> &mut Self {
        Rc::make_mut(rc)
    }
}

// === Continuation ===

impl StackValue for dyn Cont {
    #[inline]
    fn rc_into_dyn(self: Rc<Self>) -> Rc<dyn StackValue> {
        Cont::rc_into_dyn(self)
    }

    fn ty(&self) -> StackValueType {
        StackValueType::Cont
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        // vm_stk_cont#06 cont:VmCont = VmStackValue;
        ok!(builder.store_u8(0x06));
        self.store_into(builder, context)
    }

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Cont{{{:?}}}", self as *const _ as *const ())
    }

    fn as_cont(&self) -> Option<&dyn Cont> {
        Some(self)
    }

    fn rc_into_cont(self: Rc<Self>) -> VmResult<Rc<dyn Cont>> {
        Ok(self)
    }
}

impl StaticStackValue for dyn Cont {
    type DynRef<'a> = &'a dyn Cont;

    fn known_ty() -> StackValueType {
        StackValueType::Cont
    }

    fn from_dyn(value: Rc<dyn StackValue>) -> VmResult<Rc<Self>> {
        value.rc_into_cont()
    }

    fn from_dyn_ref(value: &dyn StackValue) -> VmResult<Self::DynRef<'_>> {
        match value.as_cont() {
            Some(value) => Ok(value),
            None => vm_bail!(InvalidType {
                expected: StackValueType::Cont,
                actual: value.ty(),
            }),
        }
    }
}

// === Tuple ===

/// Multiple [`RcStackValue`]s.
pub type Tuple = Vec<RcStackValue>;

/// Tuple utilities.
pub trait TupleExt {
    fn try_get(&self, index: usize) -> VmResult<&RcStackValue>;

    fn try_get_owned<V: StaticStackValue>(&self, index: usize) -> VmResult<SafeRc<V>> {
        let value = ok!(self.try_get(index));
        V::from_dyn(Rc::clone(&*value.0)).map(SafeRc::from)
    }

    fn try_get_ref<V: StaticStackValue>(&self, index: usize) -> VmResult<V::DynRef<'_>> {
        let value = ok!(self.try_get(index));
        V::from_dyn_ref(value.as_ref())
    }

    fn try_get_tuple_range<R>(&self, index: usize, range: R) -> VmResult<&[RcStackValue]>
    where
        R: std::ops::RangeBounds<usize>,
    {
        let value = ok!(self.try_get_ref::<Tuple>(index));
        if range.contains(&value.len()) {
            Ok(value)
        } else {
            // NOTE: This error is logically incorrect, but it is the desired behaviour.
            vm_bail!(InvalidType {
                expected: StackValueType::Tuple,
                actual: StackValueType::Null
            })
        }
    }
}

impl TupleExt for [RcStackValue] {
    fn try_get(&self, index: usize) -> VmResult<&RcStackValue> {
        let Some(value) = self.get(index) else {
            vm_bail!(IntegerOutOfRange {
                min: 0,
                max: self.len() as _,
                actual: index.to_string(),
            });
        };
        Ok(value)
    }
}

impl StackValue for Tuple {
    #[inline]
    fn rc_into_dyn(self: Rc<Self>) -> Rc<dyn StackValue> {
        self
    }

    fn ty(&self) -> StackValueType {
        StackValueType::Tuple
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        if self.len() > u16::MAX as usize {
            return Err(Error::IntOverflow);
        }

        let mut head = None::<Cell>;
        let mut tail = None::<Cell>;

        for item in self {
            std::mem::swap(&mut head, &mut tail);

            if tail.is_some() && head.is_some() {
                if let (Some(t), Some(h)) = (tail.take(), head.take()) {
                    head = Some(ok!(CellBuilder::build_from_ext((t, h), context)));
                }
            }

            let mut builder = CellBuilder::new();
            ok!(item.store_as_stack_value(&mut builder, context));
            tail = Some(ok!(builder.build_ext(context)));
        }

        // vm_stk_tuple#07 len:(## 16) data:(VmTuple len) = VmStackValue;
        ok!(builder.store_u8(0x07));
        ok!(builder.store_u16(self.len() as _));
        if let Some(head) = head {
            ok!(builder.store_reference(head));
        }
        if let Some(tail) = tail {
            ok!(builder.store_reference(tail));
        }
        Ok(())
    }

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_empty() {
            return f.write_str("[]");
        }
        f.write_str("[ ")?;
        let mut first = true;
        for item in self {
            if !std::mem::take(&mut first) {
                f.write_str(" ")?;
            }
            StackValue::fmt_dump(item.as_ref(), f)?;
        }
        f.write_str(" ]")
    }

    fn as_tuple(&self) -> Option<&[RcStackValue]> {
        Some(self)
    }

    fn rc_into_tuple(self: Rc<Self>) -> VmResult<Rc<Tuple>> {
        Ok(self)
    }
}

impl StaticStackValue for Tuple {
    type DynRef<'a> = &'a [RcStackValue];

    fn known_ty() -> StackValueType {
        StackValueType::Tuple
    }

    fn from_dyn(value: Rc<dyn StackValue>) -> VmResult<Rc<Self>> {
        value.rc_into_tuple()
    }

    fn from_dyn_ref(value: &dyn StackValue) -> VmResult<Self::DynRef<'_>> {
        match value.as_tuple() {
            Some(value) => Ok(value),
            None => vm_bail!(InvalidType {
                expected: StackValueType::Tuple,
                actual: value.ty(),
            }),
        }
    }
}

// === Store/Load ===

/// ```text
/// _ cell:^Cell
///   st_bits:(## 10) end_bits:(## 10) { st_bits <= end_bits }
///   st_ref:(#<= 4) end_ref:(#<= 4) { st_ref <= end_ref } = VmCellSlice;
/// ```
pub(crate) fn store_slice_as_stack_value(
    slice: &OwnedCellSlice,
    builder: &mut CellBuilder,
) -> Result<(), Error> {
    ok!(builder.store_reference(slice.cell().clone()));

    let range = slice.range();
    let value = ((range.offset_bits() as u64) << 16)
        | (((range.offset_bits() + range.size_bits()) as u64) << 6)
        | ((range.offset_refs() as u64) << 3)
        | (range.offset_refs() + range.size_refs()) as u64;
    builder.store_uint(value, 26)
}

/// ```text
/// _ cell:^Cell
///   st_bits:(## 10) end_bits:(## 10) { st_bits <= end_bits }
///   st_ref:(#<= 4) end_ref:(#<= 4) { st_ref <= end_ref } = VmCellSlice;
/// ```
pub(crate) fn load_slice_as_stack_value(slice: &mut CellSlice) -> Result<OwnedCellSlice, Error> {
    let cell = ok!(slice.load_reference_cloned());
    let range = ok!(slice.load_uint(26));

    let bits_start = (range >> 16) as u16 & 0x3ff;
    let bits_end = (range >> 6) as u16 & 0x3ff;
    let refs_start = (range >> 3) as u8 & 0b111;
    let refs_end = range as u8 & 0b111;

    if bits_start > bits_end || refs_start > refs_end || refs_end > 4 {
        return Err(Error::InvalidData);
    }

    if bits_end > cell.bit_len() || refs_end > cell.reference_count() {
        return Err(Error::InvalidData);
    }

    let mut range = CellSliceRange::full(cell.as_ref());
    let ok = range.skip_first(bits_start, refs_start).is_ok();
    debug_assert!(ok);

    let bits = bits_end - bits_start;
    let refs = refs_end - refs_start;
    let ok = range.only_first(bits, refs).is_ok();
    debug_assert!(ok);

    Ok(OwnedCellSlice::from((range, cell)))
}

// === SafeRc ===

impl RcStackValue {
    #[inline]
    pub fn new_dyn_value<T: StackValue + 'static>(value: T) -> Self {
        Self(ManuallyDrop::new(Rc::new(value)))
    }

    #[inline]
    pub fn into_int(self) -> VmResult<SafeRc<BigInt>> {
        Self::into_inner(self).rc_into_int().map(SafeRc::from)
    }

    #[inline]
    pub fn into_cell(self) -> VmResult<SafeRc<Cell>> {
        Self::into_inner(self).rc_into_cell().map(SafeRc::from)
    }

    #[inline]
    pub fn into_cell_slice(self) -> VmResult<SafeRc<OwnedCellSlice>> {
        Self::into_inner(self)
            .rc_into_cell_slice()
            .map(SafeRc::from)
    }

    #[inline]
    pub fn into_cell_builder(self) -> VmResult<SafeRc<CellBuilder>> {
        Self::into_inner(self)
            .rc_into_cell_builder()
            .map(SafeRc::from)
    }

    #[inline]
    pub fn into_cont(self) -> VmResult<SafeRc<dyn Cont>> {
        Self::into_inner(self).rc_into_cont().map(SafeRc::from)
    }

    #[inline]
    pub fn into_tuple(self) -> VmResult<SafeRc<Tuple>> {
        Self::into_inner(self).rc_into_tuple().map(SafeRc::from)
    }
}

impl<T: StackValue + ?Sized> SafeRc<T> {
    #[inline]
    pub fn into_dyn_value(self) -> RcStackValue {
        let value = SafeRc::into_inner(self);
        SafeRc(ManuallyDrop::new(value.rc_into_dyn()))
    }
}

impl<T: StackValue + 'static> From<T> for RcStackValue {
    #[inline]
    fn from(value: T) -> Self {
        Self(ManuallyDrop::new(Rc::new(value)))
    }
}

impl<T: StackValue + 'static> From<Rc<T>> for RcStackValue {
    #[inline]
    fn from(value: Rc<T>) -> Self {
        Self(ManuallyDrop::new(value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_stack_tuple() {
        let cell =
            Boc::decode_base64("te6cckEBAwEAHQABGAAAAgEAAAAAAAAAAgEBEgEAAAAAAAAAAQIAAHap0w8=")
                .unwrap();

        let stack = cell.parse::<Stack>().unwrap();
        println!("{:#?}", stack.items);
    }

    #[test]
    fn stack_store_load_works() {
        #[track_caller]
        fn check_value(value: RcStackValue) {
            let mut b = CellBuilder::new();
            value
                .store_as_stack_value(&mut b, Cell::empty_context())
                .unwrap();
            let parsed = Stack::load_stack_value(&mut b.as_full_slice()).unwrap();

            let value = format!("{}", value.display_list());
            let parsed = format!("{}", parsed.display_list());
            println!("VALUE: {value}, PARSED: {parsed}");
            assert_eq!(value, parsed);
        }

        // Null
        check_value(SafeRc::new_dyn_value(()));

        // Int
        for negate in [false, true] {
            for pow in 0..=256 {
                let mut value: BigInt = (BigInt::from(1) << pow) - 1;
                if negate {
                    value = -value;
                }
                check_value(SafeRc::new_dyn_value(value));
            }
        }

        // NaN
        check_value(SafeRc::new_dyn_value(NaN));

        // Cell
        check_value(SafeRc::new_dyn_value(
            CellBuilder::build_from((
                0x123123u32,
                HashBytes::wrap(&[0xff; 32]),
                Cell::default(),
                Cell::default(),
            ))
            .unwrap(),
        ));

        // CellSlice
        check_value(SafeRc::new_dyn_value({
            let cell = CellBuilder::build_from((
                0x123123u32,
                HashBytes::wrap(&[0xff; 32]),
                Cell::default(),
                Cell::default(),
            ))
            .unwrap();
            let mut cs = OwnedCellSlice::new_allow_exotic(cell);

            {
                let mut slice = cs.apply();
                slice.skip_first(16, 1).unwrap();
                slice.skip_last(8, 0).unwrap();
                cs.set_range(slice.range());
            }

            cs
        }));

        // CellBuilder
        check_value(SafeRc::new_dyn_value({
            let mut b = CellBuilder::new();
            b.set_exotic(true);
            b.store_u32(0x123123).unwrap();
            b.store_u256(HashBytes::wrap(&[0xff; 32])).unwrap();
            b.store_reference(Cell::default()).unwrap();
            b
        }));

        // Tuple
        check_value(SafeRc::new_dyn_value(tuple![]));
        check_value(SafeRc::new_dyn_value(tuple![int 0, int 1, int 2]));
        check_value(SafeRc::new_dyn_value(
            tuple![int 0, int 1, int 2, [int 1, [int 2, [int 3, int 4]]]],
        ));
        check_value(SafeRc::new_dyn_value(tuple![
            raw SafeRc::new_dyn_value(Cell::default()),
            raw SafeRc::new_dyn_value(CellBuilder::new()),
            null,
            nan,
        ]));
    }
}
