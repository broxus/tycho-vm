use std::mem::ManuallyDrop;
use std::rc::Rc;
use std::sync::Arc;

use tycho_types::error::Error;
use tycho_types::prelude::*;

// === SafeRc impl ===

/// A data which can be used in [`SafeRc`].
pub trait SafeDelete: 'static {
    fn rc_into_safe_delete(self: Rc<Self>) -> Rc<dyn SafeDelete>;
}

impl<T: 'static> SafeDelete for T {
    #[inline]
    fn rc_into_safe_delete(self: Rc<Self>) -> Rc<dyn SafeDelete> {
        self
    }
}

/// [`Rc`]-like object with a linear drop.
///
/// Allows to build a deeply
/// nested data without causing a stack overflow.
#[repr(transparent)]
pub struct SafeRc<T: SafeDelete + ?Sized>(pub(crate) ManuallyDrop<Rc<T>>);

impl<T: SafeDelete> SafeRc<T> {
    #[inline]
    pub fn new(value: T) -> Self {
        Self(ManuallyDrop::new(Rc::new(value)))
    }

    #[inline]
    pub fn try_unwrap(this: Self) -> Result<T, Self> {
        match Rc::try_unwrap(Self::into_inner(this)) {
            Ok(value) => Ok(value),
            Err(rc) => Err(Self(ManuallyDrop::new(rc))),
        }
    }
}

impl<T: SafeDelete + ?Sized> SafeRc<T> {
    #[inline]
    pub fn into_inner(mut this: Self) -> Rc<T> {
        // SAFETY: Item was taken only once.
        let value = unsafe { ManuallyDrop::take(&mut this.0) };
        // Forget `self` to prevent `drop` from calling.
        std::mem::forget(this);

        value
    }

    #[inline]
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        Rc::get_mut(&mut *this.0)
    }

    #[inline]
    pub fn ptr_eq(lhs: &Self, rhs: &Self) -> bool {
        Rc::<T>::ptr_eq(&*lhs.0, &*rhs.0)
    }

    #[inline]
    pub fn as_ptr(&self) -> *const T {
        Rc::as_ptr(&*self.0)
    }
}

impl<T: SafeDelete + Clone> SafeRc<T> {
    #[inline]
    pub fn unwrap_or_clone(this: Self) -> T {
        Rc::unwrap_or_clone(Self::into_inner(this))
    }
}

// === Common traits impl ===

impl<T: Default + SafeDelete> Default for SafeRc<T> {
    fn default() -> Self {
        Self(ManuallyDrop::new(Rc::<T>::default()))
    }
}

impl<T: SafeDelete + ?Sized> Clone for SafeRc<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: SafeDelete + std::fmt::Display + ?Sized> std::fmt::Display for SafeRc<T> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&*self.0, f)
    }
}

impl<T: SafeDelete + std::fmt::Debug + ?Sized> std::fmt::Debug for SafeRc<T> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&*self.0, f)
    }
}

impl<T: Eq + SafeDelete + ?Sized> Eq for SafeRc<T> {}

impl<T: PartialEq + SafeDelete + ?Sized> PartialEq for SafeRc<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        T::eq(&*self.0, &*other.0)
    }
}

impl<T: Ord + SafeDelete + ?Sized> Ord for SafeRc<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        T::cmp(&*self.0, &*other.0)
    }
}

impl<T: PartialOrd + SafeDelete + ?Sized> PartialOrd for SafeRc<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        T::partial_cmp(&*self.0, &*other.0)
    }
}

impl<T: SafeDelete + ?Sized> Drop for SafeRc<T> {
    fn drop(&mut self) {
        // SAFETY: Item was taken only once.
        let value = unsafe { ManuallyDrop::take(&mut self.0) };

        // // TODO: Somehow move this to stack module?
        // castaway::match_type!(value, {
        //     // Just drop the value for non-recursive types.
        //     () as _v => {},
        //     crate::stack::NaN as _v => {},
        //     num_bigint::BigInt as _v => {},
        //     tycho_types::cell::Cell as _v => {},
        //     tycho_types::cell::CellBuilder as _v => {},
        //     crate::util::OwnedCellSlice as _v => {},
        //     // Go through retire othersize (Cont, Stack, Tuple, etc.).
        //     value => {
        //         if Rc::strong_count(&value) == 1 {
        //             SafeDeleter::retire(value.rc_into_safe_delete());
        //         }
        //     }
        // });

        if Rc::strong_count(&value) == 1 {
            SafeDeleter::retire(value.rc_into_safe_delete());
        }
    }
}

impl<T: SafeDelete + ?Sized> std::ops::Deref for SafeRc<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: SafeDelete + ?Sized> AsRef<T> for SafeRc<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T: SafeDelete + ?Sized> From<Rc<T>> for SafeRc<T> {
    #[inline]
    fn from(value: Rc<T>) -> Self {
        Self(ManuallyDrop::new(value))
    }
}

impl<T: SafeDelete> From<T> for SafeRc<T> {
    #[inline]
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

#[cfg(feature = "arbitrary")]
impl<'a, T: SafeDelete + arbitrary::Arbitrary<'a>> arbitrary::Arbitrary<'a> for SafeRc<T> {
    #[inline]
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        u.arbitrary().map(Self::new)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        Self::try_size_hint(depth).unwrap_or_default()
    }

    #[inline]
    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        <T as arbitrary::Arbitrary>::try_size_hint(depth)
    }
}

// === `Rc::make_mut` glue ===

/// `Rc::make_mut` glue.
pub trait SafeRcMakeMut: SafeDelete {
    fn rc_make_mut(rc: &mut Rc<Self>) -> &mut Self;
}

impl<T: SafeRcMakeMut + ?Sized> SafeRc<T> {
    #[inline]
    pub fn make_mut(&mut self) -> &mut T {
        T::rc_make_mut(&mut *self.0)
    }
}

impl SafeRcMakeMut for () {
    #[inline]
    fn rc_make_mut(rc: &mut Rc<Self>) -> &mut Self {
        Rc::make_mut(rc)
    }
}

impl<T: Clone + 'static> SafeRcMakeMut for Box<T> {
    #[inline]
    fn rc_make_mut(rc: &mut Rc<Self>) -> &mut Self {
        Rc::make_mut(rc)
    }
}

impl<T: ?Sized + 'static> SafeRcMakeMut for Rc<T> {
    #[inline]
    fn rc_make_mut(rc: &mut Rc<Self>) -> &mut Self {
        Rc::make_mut(rc)
    }
}

impl<T: ?Sized + 'static> SafeRcMakeMut for Arc<T> {
    #[inline]
    fn rc_make_mut(rc: &mut Rc<Self>) -> &mut Self {
        Rc::make_mut(rc)
    }
}

impl<T: Clone + 'static> SafeRcMakeMut for Vec<T> {
    #[inline]
    fn rc_make_mut(rc: &mut Rc<Self>) -> &mut Self {
        Rc::make_mut(rc)
    }
}

impl SafeRcMakeMut for String {
    #[inline]
    fn rc_make_mut(rc: &mut Rc<Self>) -> &mut Self {
        Rc::make_mut(rc)
    }
}

// === Cell traits impl ===

impl<'a, T: Load<'a> + SafeDelete> Load<'a> for SafeRc<T> {
    #[inline]
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let value = ok!(Rc::<T>::load_from(slice));
        Ok(Self(ManuallyDrop::new(value)))
    }
}

impl<T: Store + SafeDelete + ?Sized> Store for SafeRc<T> {
    #[inline]
    fn store_into(&self, b: &mut CellBuilder, c: &dyn CellContext) -> Result<(), Error> {
        T::store_into(&*self.0, b, c)
    }
}

// === Linear deleter ===

struct SafeDeleter {
    to_delete: std::cell::RefCell<Vec<Rc<dyn SafeDelete>>>,
    is_active: std::cell::Cell<bool>,
}

impl SafeDeleter {
    fn retire(value: Rc<dyn SafeDelete>) {
        thread_local! {
            static DELETER: SafeDeleter = const {
                SafeDeleter {
                    to_delete: std::cell::RefCell::new(Vec::new()),
                    is_active: std::cell::Cell::new(false),
                }
            };
        }

        let mut value = ManuallyDrop::new(value);

        match DELETER.try_with(|deleter| {
            // SAFETY: Value is going to be taken only once, because this
            // closure will run only if `LocalKey` still exists.
            let value = unsafe { ManuallyDrop::take(&mut value) };

            if deleter.is_active.get() {
                // Delay child value drop if we are already dropping some parent value.
                deleter.to_delete.borrow_mut().push(value);
                return;
            }

            // Activate delayed drop of children.
            deleter.is_active.set(true);

            // Drop the parent value. This will fill the `to_delete` vector
            // with children values.
            drop(value);

            // Iterate and "drop" children.
            loop {
                // Take one child value.
                let mut to_delete = deleter.to_delete.borrow_mut();
                match to_delete.pop() {
                    Some(value) => {
                        // Make sure to drop the `RefMut` guard first.
                        drop(to_delete);
                        // "Drop" the child.
                        drop(value);
                    }
                    None => break,
                }
            }

            // Disable delayed delete.
            deleter.is_active.set(false);
        }) {
            Ok(()) => {}
            // SAFETY: `LocalKey` does not exist anymore (we are removing some other
            // thread local SafeRc). So the closure above will not run and
            // we are dropping the value like always.
            Err(_) => drop(unsafe { ManuallyDrop::take(&mut value) }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg_attr(miri, ignore)]
    fn drop_deep_tuple() {
        let mut tuple = SafeRc::new_dyn_value(());
        for _ in 0..1000000 {
            tuple = SafeRc::new_dyn_value(vec![tuple]);
        }
    }
}
