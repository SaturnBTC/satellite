use std::mem::MaybeUninit;

use crate::generic::fixed_list::FixedListError;

/// A fixed-capacity list that uses MaybeUninit to avoid Default and Clone requirements.
/// This allows storing types like Ref and RefMut that don't implement these traits.
pub struct FixedRefList<T, const MAX_SIZE: usize> {
    items: [MaybeUninit<T>; MAX_SIZE],
    len: usize,
}

impl<T, const MAX_SIZE: usize> FixedRefList<T, MAX_SIZE> {
    /// Creates a new empty ShardList.
    pub fn new() -> Self {
        Self {
            items: unsafe { MaybeUninit::uninit().assume_init() },
            len: 0,
        }
    }

    /// Pushes an item to the list.
    pub fn push(&mut self, item: T) -> Result<(), FixedListError> {
        if self.len >= MAX_SIZE {
            return Err(FixedListError::Full);
        }

        self.items[self.len] = MaybeUninit::new(item);
        self.len += 1;
        Ok(())
    }

    /// Returns the length of the list.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the list is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns an iterator over the items in the list.
    pub fn iter(&self) -> FixedRefListIter<'_, T> {
        FixedRefListIter {
            items: &self.items[..self.len],
            index: 0,
        }
    }

    /// Returns a mutable iterator over the items in the list.
    pub fn iter_mut(&mut self) -> FixedRefListIterMut<'_, T> {
        FixedRefListIterMut {
            items: &mut self.items[..self.len],
            index: 0,
        }
    }

    /// Gets a reference to the item at the specified index.
    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len {
            Some(unsafe { self.items[index].assume_init_ref() })
        } else {
            None
        }
    }

    /// Gets a mutable reference to the item at the specified index.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index < self.len {
            Some(unsafe { self.items[index].assume_init_mut() })
        } else {
            None
        }
    }

    pub fn remove(&mut self, index: usize) -> Option<T> {
        if index >= self.len {
            return None;
        }

        // SAFETY: `index` is guaranteed to be < len, so the slot is initialised.
        let removed_item = unsafe { self.items[index].assume_init_read() };

        // Decrement len; the slot at `self.len` is now logically uninitialised.
        self.len -= 1;

        // If we removed something other than the last element, move the last
        // element into the hole so that all indices < len remain initialised.
        if index != self.len {
            let last_item = unsafe { self.items[self.len].assume_init_read() };
            self.items[index] = MaybeUninit::new(last_item);
        }

        Some(removed_item)
    }

    /// Returns an immutable slice over the initialised items in the list.
    pub fn as_slice(&self) -> &[T] {
        // SAFETY: `items` is a contiguous array and the first `len` elements are
        // guaranteed to be initialised by construction. We cast the raw pointer
        // to `T` and build a slice with length `len`.
        unsafe { std::slice::from_raw_parts(self.items.as_ptr() as *const T, self.len) }
    }

    /// Returns a mutable slice over the initialised items in the list.
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        // SAFETY: Same reasoning as `as_slice`, but we have a mutable reference
        // to self, ensuring unique access.
        unsafe { std::slice::from_raw_parts_mut(self.items.as_mut_ptr() as *mut T, self.len) }
    }
}

use std::ops::{Deref, DerefMut};

impl<T, const MAX_SIZE: usize> Deref for FixedRefList<T, MAX_SIZE> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T, const MAX_SIZE: usize> DerefMut for FixedRefList<T, MAX_SIZE> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<T, const MAX_SIZE: usize> AsRef<[T]> for FixedRefList<T, MAX_SIZE> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const MAX_SIZE: usize> AsMut<[T]> for FixedRefList<T, MAX_SIZE> {
    fn as_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<'a, T, const MAX_SIZE: usize> IntoIterator for &'a FixedRefList<T, MAX_SIZE> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

impl<'a, T, const MAX_SIZE: usize> IntoIterator for &'a mut FixedRefList<T, MAX_SIZE> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_mut_slice().iter_mut()
    }
}

impl<T, const MAX_SIZE: usize> Drop for FixedRefList<T, MAX_SIZE> {
    fn drop(&mut self) {
        // Properly drop all initialized items
        for i in 0..self.len {
            unsafe {
                self.items[i].assume_init_drop();
            }
        }
    }
}

/// Iterator over items in a ShardList.
pub struct FixedRefListIter<'a, T> {
    items: &'a [MaybeUninit<T>],
    index: usize,
}

impl<'a, T> Iterator for FixedRefListIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.items.len() {
            let item = unsafe { self.items[self.index].assume_init_ref() };
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }
}

/// Mutable iterator over items in a ShardList.
pub struct FixedRefListIterMut<'a, T> {
    items: &'a mut [MaybeUninit<T>],
    index: usize,
}

impl<'a, T> Iterator for FixedRefListIterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.items.len() {
            let item = unsafe { &mut *(self.items[self.index].as_mut_ptr()) };
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }
}
