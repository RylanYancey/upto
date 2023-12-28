
#![feature(maybe_uninit_uninit_array)]

//! # UpTo 
//! Fixed-Capacity Variable Length Stack-Allocated Arrays
//! 
//! ## When to use UpTo
//! UpTo is best when you know the maximum capacity a vector needs to have, but you
//! don't want to allocate the whole thing all at once. It is also best to keep UpTo capacities
//! relatively small. If you need a high-capacity container, just use a Vec<T>. 
//! 
//! ## Safety
//! This crate makes heavy use of `std::mem::MaybeUninit<T>``. The UpTo type is internally a `[MaybeUninit<T>; N]`. Reading 
//! from a `MaybeUninit` is inherently unsafe, but we can guarantee safety since any value at an index less than `UpTo.len`
//! is known to be initialized. 
//! 
//! ## Example
//! ```
//! use upto::{UpTo, upto};
//! 
//! // allocate an array with capacity 5.
//! let mut upto: UpTo<5, i32> = UpTo::new();
//! 
//! // push values.
//! upto.push(720);
//! upto.push(1080);
//! upto.push(1440);
//! upto.push(2160);
//! 
//! // Iter & IterMut
//! // output: "720, 1080, 1440, 2160"
//! for v in upto.iter() {
//!     println!("{v}, ")
//! }
//! 
//! for v in upto.iter_mut() {
//!     *v += 144;
//! }
//! 
//! // Remove & Insert values.
//! upto.remove(3);
//! upto.insert(540, 0);
//! 
//! // Index & IndexMut.
//! println!("{}", upto[3]);
//! upto[2] += 144;
//! 
//! // First (try_first_mut, try_first, first, first_mut)
//! if let Some(v) = upto.try_first() {
//!     println!("{v}")
//! }
//! 
//! // Last (try_last_mut, try_last, last, last_mut)
//! if let Some(v) = upto.try_last_mut() {
//!     *v += 144;
//! }
//! 
//! // Pop
//! while let Some(v) = upto.pop() {
//!     println!("{v}")
//! }
//! ```

use std::mem::MaybeUninit;
use std::ops::Index;
use std::ops::IndexMut;

/// # UpTo
/// 
/// Fixed-Size Growable-Length Array without Heap Allocation
/// 
/// ## Initialization
/// ```
/// use upto::{UpTo, upto};
/// 
/// // init with 'new'.
/// let mut array: UpTo<3, i32> = UpTo::new();
/// array.push(1);
/// array.push(2);
/// array.push(3);
/// 
/// // init with 'upto' macro.
/// let array: UpTo<3, i32> = upto![1, 2, 3];
/// 
/// // init from vector
/// let vec = vec![1, 2, 3];
/// let array: UpTo<3, i32> = UpTo::from(vec);
/// 
/// // init from array
/// let arr = [1, 2, 3];
/// let array: UpTo<3, i32> = UpTo::from(arr);
/// ```
/// 
/// ## Manipulation
/// ```
/// use upto::{UpTo, upto};
/// 
/// // init array with capacity of 3 and length 0.
/// let mut array: UpTo<3, i32> = UpTo::new();
/// 
/// // append a value to the end of the array.
/// array.push(0);
/// array.push(1);
/// 
/// // insert a value at index 1.
/// array.insert(2, 1);
/// 
/// // remove a value at index 2.
/// array.remove(2);
/// ```
pub struct UpTo<const N: usize, T> {
    array: [MaybeUninit<T>; N],
    len: usize,
}

impl<const N: usize, T> UpTo<N, T> {
    /// Construct a new Array with capacity N and length 0. 
    /// # Examples
    /// ```
    /// use upto::UpTo;
    /// 
    /// let array: UpTo<5, i32> = UpTo::new();
    /// ```
    pub fn new() -> Self {
        Self {
            array: MaybeUninit::uninit_array::<N>(),
            len: 0
        }
    }

    /// Construct a new Array with capacity N and length vec.len(). 
    /// # Panics
    /// - if vecs' len is greater than N
    /// # Examples
    /// ```
    /// use upto::UpTo;
    /// let vec = vec![1, 2, 3];
    /// 
    /// let array: UpTo<5, i32> = UpTo::from_vec(vec);
    /// ```
    pub fn from_vec(vec: Vec<T>) -> Self {
        vec.into()
    }

    /// The Length of the array.
    /// If the Array is empty, the len is 0. 
    pub fn len(&self) -> usize {
        self.len
    }

    /// The capacity of the array is always N.  
    pub fn capacity(&self) -> usize {
        N
    }

    /// Append a value to the back of the array. 
    /// # Panics
    /// - if the array is out of capacity.
    pub fn push(&mut self, val: T) {
        if self.len == N {
            panic!("Out of Capacity! Attempted to push a value but the array is full!");
        }

        self.array[self.len].write(val);
        self.len += 1;
    }

    /// Insert a value at `index`, pushing all elements after it to the right. 
    /// # Panics
    /// - if the array is out of capacity.
    /// - if the index is greater than or equal to the len. 
    pub fn insert(&mut self, val: T, index: usize) {
        if self.len == N {
            panic!("Out of Capacity! Attempted to insert a value but the array is full!")
        }

        if index >= self.len {
            panic!("Out of Bounds Error: Index was {} but the len was {}!", index, self.len)
        }

        // this loop moves the all the elements at and after index over 1, 
        // making space for the new value.
        for i in (index..self.len).rev() {
            self.array.swap(i, i+1);      
        }

        self.array[index].write(val);

        self.len += 1;
    }

    /// Remove & return a value at `index`, pushing all elemenetts after it to the left.
    /// # Panics
    /// - if the index is greater than or equal to the len.
    pub fn remove(&mut self, index: usize) -> T {
        if index >= self.len {
            panic!("Out of Bounds Error: Index was {} but the len was {}!", index, self.len);
        }

        // copy the value to be removed out of the array.
        let mut output = MaybeUninit::uninit();
        std::mem::swap(&mut self.array[index], &mut output);

        // this loop shifts the elements after `index` to the left.
        if index != self.len - 1 {
            for i in index..self.len - 1 {
                self.array.swap(i, i + 1)
            }
        } 
        
        self.len -= 1;

        unsafe {
            output.assume_init()
        }
    }

    /// Swap the elemenent at `index` with the last element in the array, then remove & return the last element.
    /// Faster than remove, but does not preserve the order of the array. 
    /// # Panics
    /// - if the index is greater than or equal to the len. 
    pub fn remove_swap(&mut self, index: usize) -> T {
        if index >= self.len {
            panic!("Out of Bounds Error: Index was {} but the len was {}!", index, self.len)
        }

        self.len -= 1;

        self.array.swap(index, self.len);

        let mut output = MaybeUninit::uninit();
        std::mem::swap(&mut self.array[self.len], &mut output);

        unsafe {
            output.assume_init()
        }
    }

    /// Remove and return the last element of the array. 
    /// If there are no elemenets in the array, return None.
    /// # Examples
    /// ```
    /// use upto::{UpTo, upto};
    /// 
    /// let mut array: UpTo<10, i32> = upto![1, 2, 3, 4, 5];
    /// 
    /// // removes and prints all values in the array.
    /// while let Some(v) = array.pop() {
    ///     println!("{v}, ")
    /// }
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            Some(self.remove(self.len - 1))
        }
    }

    /// Get a reference to the last element of the array.
    /// If the array is empty, return None.
    /// # Examples
    /// ```
    /// use upto::{UpTo, upto};
    /// 
    /// let array: UpTo<10, i32> = upto![1, 2, 3, 4, 5];
    /// 
    /// // get and print the last element.
    /// if let Some(v) = array.try_last() {
    ///     println!("{v}");
    /// } else {
    ///     panic!("No Elements to print!")
    /// }
    /// ```
    pub fn try_last(&self) -> Option<&T> {
        if self.len == 0 {
            None
        } else {
            unsafe {
                Some(self.array[self.len - 1].assume_init_ref())
            }
        }
    }

    /// Get a reference to the last element in the array.
    /// # Panics
    /// - if the array is empty.
    /// # Examples
    /// ```
    /// use upto::{UpTo, upto};
    /// 
    /// let array: UpTo<10, i32> = upto![1, 2, 3, 4, 5];
    /// 
    /// // print the last value.
    /// println!("{}", array.last());
    /// ```
    pub fn last(&self) -> &T {
        if self.len == 0 {
            panic!("Attempted to get last element, but the array is empty!")
        }

        unsafe {
            self.array[self.len - 1].assume_init_ref()
        }
    }

    /// Get a mutable reference to the last element in the array.
    /// If the array is empty, return None.
    /// ```
    /// use upto::{UpTo, upto};
    /// 
    /// let mut array: UpTo<10, i32> = upto![1, 2, 3, 4, 5];
    /// 
    /// // get and increase the last element
    /// if let Some(v) = array.try_last_mut() {
    ///     *v += 5;
    /// } else {
    ///     panic!("No Elements to Modify!")
    /// }
    /// ```
    pub fn try_last_mut(&mut self) -> Option<&mut T> {
        if self.len == 0 {
            None
        } else {
            unsafe {
                Some(self.array[self.len - 1].assume_init_mut())
            }
        }
    }

    /// Get a mutable reference to the last element in the array.
    /// # Panics
    /// - if the array is empty.
    /// # Examples
    /// ```
    /// use upto::{UpTo, upto};
    /// 
    /// let mut array: UpTo<10, i32> = upto![1, 2, 3];
    /// 
    /// // add 10 to the last element.
    /// *array.last_mut() += 10;
    /// ```
    pub fn last_mut(&mut self) -> &mut T {
        if self.len == 0 {
            panic!("Attempted to get last element, but the array is empty!")
        }

        unsafe {
            self.array[self.len - 1].assume_init_mut()
        }
    }

    /// Get a reference to the first element of the array.
    /// If the array is empty, return None.
    /// # Examples
    /// ```
    /// use upto::{UpTo, upto};
    /// 
    /// let array: UpTo<10, i32> = upto![1, 2, 3, 4, 5];
    /// 
    /// // get and print the first element.
    /// if let Some(v) = array.try_first() {
    ///     println!("{v}");
    /// } else {
    ///     panic!("No Elements to print!")
    /// }
    /// ```
    pub fn try_first(&self) -> Option<&T> {
        if self.len == 0 {
            None
        } else {
            unsafe {
                Some(self.array[0].assume_init_ref())
            }
        }
    }

    /// Get a reference to the first element in the array.
    /// # Panics
    /// - if the array is empty.
    /// # Examples
    /// ```
    /// use upto::{UpTo, upto};
    /// 
    /// let array: UpTo<10, i32> = upto![1, 2, 3, 4, 5];
    /// 
    /// // print the first value.
    /// println!("{}", array.first());
    /// ```
    pub fn first(&self) -> &T {
        if self.len == 0 {
            panic!("Attempted to get first element, but the array is empty!")
        } else {
            unsafe {
                self.array[0].assume_init_ref()
            }
        }
    }

    /// Get a mutable reference to the first element in the array.
    /// If the array is empty, return None.
    /// ```
    /// use upto::{UpTo, upto};
    /// 
    /// let mut array: UpTo<10, i32> = upto![1, 2, 3, 4, 5];
    /// 
    /// // get and increase the first element
    /// if let Some(v) = array.try_first_mut() {
    ///     *v += 5;
    /// } else {
    ///     panic!("No Elements to Modify!")
    /// }
    /// ```
    pub fn try_first_mut(&mut self) -> Option<&mut T> {
        if self.len == 0 {
            None
        } else {
            unsafe {
                Some(self.array[0].assume_init_mut())
            }
        }
    }

    /// Get a mutable reference to the first element in the array.
    /// # Panics
    /// - if the array is empty.
    /// # Examples
    /// ```
    /// use upto::{UpTo, upto};
    /// 
    /// let mut array: UpTo<10, i32> = upto![1, 2, 3];
    /// 
    /// // add 10 to the first element.
    /// *array.first_mut() += 10;
    /// ```
    pub fn first_mut(&mut self) -> &mut T {
        if self.len == 0 {
            panic!("Attempted to get first element, but the array is empty!")
        } else {
            unsafe {
                self.array[0].assume_init_mut()
            }
        }
    }
    
    /// Iterate immutably over the elements of the Array.
    pub fn iter<'a>(&'a self) -> UpToIter<'a, T> {
        UpToIter {
            array: &self.array,
            curr: 0,
            len: self.len
        }
    }

    /// Iterate mutably over the elements of the Array.
    pub fn iter_mut<'a>(&'a mut self) -> UpToIterMut<'a, T> {
        UpToIterMut {
            array: &mut self.array,
            curr: 0,
            len: self.len
        }
    }

    /// Convert the Array to a vector, consuming the array. 
    pub fn to_vec(mut self) -> Vec<T> {
        let mut vec = Vec::with_capacity(self.len);
        while let Some(v) = self.pop() {
            vec.push(v);
        }
        vec
    }
}

impl<const N: usize, T> UpTo<N, T> 
where
    T: Clone
{
    /// Initialize a new Array from a slice.
    pub fn from_slice(slice: &[T]) -> Self {
        if slice.len() > N {
            panic!("Attempted to create UpTo<N, T> from Vec<N>, but the len of the Vec is greater than N!")
        }

        let mut upto = UpTo::new();

        for v in slice {
            upto.push(v.clone());
        }

        upto
    }

    /// Create a new vec from the Array.
    pub fn as_vec(&self) -> Vec<T> {
        let mut vec = Vec::with_capacity(self.len);

        for v in self.iter() {
            vec.push(v.clone());
        }

        vec
    }
}

impl<const N: usize, T> From<&[T]> for UpTo<N, T> 
where
    T: Clone
{
    fn from(value: &[T]) -> Self {
        if value.len() > N {
            panic!("Attempted to create UpTo<N, T> from Vec<N>, but the len of the Vec is greater than N!")
        }

        let mut upto = UpTo::new();

        for v in value.into_iter() {
            upto.push(v.clone())
        }

        upto
    }
}

impl<const N: usize, T> From<Vec<T>> for UpTo<N, T> {
    fn from(value: Vec<T>) -> Self {
        if value.len() > N {
            panic!("Attempted to create UpTo<N, T> from Vec<N>, but the len of the Vec is greater than N!")
        }
        
        let mut upto = UpTo::new();
    
        for v in value {
            upto.push(v)
        }

        upto
    }
}

impl<const N: usize, T> From<[T; N]> for UpTo<N, T> {
    fn from(value: [T; N]) -> Self {
        let mut upto = UpTo::new();

        for v in value {
            upto.push(v)
        }

        upto
    }
}

impl<const N: usize, T> Drop for UpTo<N, T> {
    fn drop(&mut self) {
        while let Some(_) = self.pop() {}
    }
}

impl<const N: usize, T> Index<usize> for UpTo<N, T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        if index >= self.len {
            panic!("Out of Bounds Error: Index was {} but the len was {}!", index, self.len);
        } else {
            unsafe {
                self.array[index].assume_init_ref()
            }
        }
    }
}

impl<const N: usize, T> IndexMut<usize> for UpTo<N, T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index >= self.len {
            panic!("Out of Bounds Error: Index was {} but the len was {}!", index, self.len);
        } else {
            unsafe {
                self.array[index].assume_init_mut()
            }
        }
    }
}

/// Type for iterating immutably over the Array.
pub struct UpToIter<'a, T> {
    array: &'a [MaybeUninit<T>],
    curr: usize,
    len: usize,
}

impl<'a, T> Iterator for UpToIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        // if these are equal, we have iterated all the elements.
        if self.len == self.curr {
            None
        } else {
            // increment curr.
            self.curr += 1;

            // get and return.
            unsafe {
                Some(self.array[self.curr - 1].assume_init_ref())
            }
        }
    }
}

/// Type for iterating mutably over an Array.
pub struct UpToIterMut<'a, T> {
    array: &'a mut [MaybeUninit<T>],
    curr: usize, 
    len: usize,
}

impl<'a, T> Iterator for UpToIterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        // if these are equal, we have iterated all the elements.
        if self.len == self.curr {
            None
        } else {
            // increment curr.
            self.curr += 1;

            // get the value and return.
            unsafe {
                Some(&mut *self.array[self.curr - 1].as_mut_ptr())
            }
        }
    }
}

mod macros {
    #[macro_export]
    macro_rules! upto {
        [$($i: literal),*] => {
            UpTo::from_slice(&[$($i),*])
        };

        [$($i: ident),*] => {
            UpTo::from_slice(&[$($i),*])
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::UpTo;
    use crate::upto;

    #[test]
    fn push() {
        let mut upto: UpTo<3, i32> = UpTo::new();
        upto.push(0);
        upto.push(1);
        upto.push(2);
    }

    #[test]
    #[should_panic]
    fn push_overflow() {
        let mut upto: UpTo<3, i32> = UpTo::new();
        upto.push(0);
        upto.push(1);
        upto.push(2);
        upto.push(3);
    }

    #[test]
    fn macro_literals() {
        let upto: UpTo<3, i32> = upto![1, 2, 3];
        assert_eq!(3, upto[2])
    }

    #[test]
    fn macro_identifiers() {
        let a = 3;
        let b = 2;
        let c = 1;

        let upto: UpTo<3, i32> = upto![a, b, c];

        assert_eq!(1, upto[2])
    }

    #[test]
    fn remove() {
        let a = vec![1, 2, 3];
        let b = vec![4, 5, 6];
        let c = vec![7, 8, 9];
        let mut upto: UpTo<3, Vec<i32>> = UpTo::new();
        upto.push(a);
        upto.push(b);
        upto.push(c);

        upto.remove(1);

        assert_eq!(vec![1, 2, 3], upto[0]);
        assert_eq!(vec![7, 8, 9], upto[1]);
    }

    #[test]
    fn pop() {
        let mut upto: UpTo<3, i32> = upto![1, 2, 3];

        let mut sum = 0;
        while let Some(v) = upto.pop() {
            sum += v;
        }

        assert_eq!(sum, 6);
    }

    #[test]
    fn iter() {
        let upto: UpTo<5, i32> = upto![1, 2, 3, 4, 5];

        let mut sum = 0;
        for n in upto.iter() {
            sum += n;
        }

        assert_eq!(sum, 15);
    }

    #[test]
    fn iter_mut() {
        let mut upto: UpTo<5, i32> = upto![1, 2, 3, 4, 5];

        for n in upto.iter_mut() {
            *n += 1;
        }

        let mut sum = 0;
        for n in upto.iter() {
            sum += n;
        }

        assert_eq!(sum, 20)
    }

    #[test]
    fn index() {
        let upto: UpTo<5, i32> = upto![1, 2, 3, 4, 5];

        assert!(upto[0] == 1);
        assert!(upto[1] == 2);
        assert!(upto[2] == 3);
        assert!(upto[3] == 4);
        assert!(upto[4] == 5);
    }

    #[test]
    fn index_mut() {
        let mut upto: UpTo<5, i32> = upto![1, 2, 3, 4, 5];

        upto[0] += 1;
        upto[1] += 1;
        upto[2] += 1;
        upto[3] += 1;
        upto[4] += 1;

        assert!(upto[0] == 2);
        assert!(upto[1] == 3);
        assert!(upto[2] == 4);
        assert!(upto[3] == 5);
        assert!(upto[4] == 6);
    }

    #[test]
    fn try_last() {
        let upto: UpTo<3, i32> = upto![1, 2, 3];
        
        if let Some(v) = upto.try_last() {
            assert_eq!(*v, 3);
        } else {
            panic!("upto.last() did not return a value.")
        }
    }

    #[test]
    fn last() {
        let upto: UpTo<3, i32> = upto![1, 2, 3];

        assert_eq!(*upto.last(), 3);
    }

    #[test]
    fn try_last_mut() {
        let mut upto: UpTo<3, i32> = upto![1, 2, 3];

        if let Some(v) = upto.try_last_mut() {
            *v += 1;
        } else {
            panic!("upto.last_mut() did not return a value.")
        }

        assert_eq!(upto[2], 4)
    }

    #[test]
    fn last_mut() {
        let mut upto: UpTo<3, i32> = upto![1, 2, 3];

        *upto.last_mut() += 1;

        assert_eq!(upto[2], 4);
    }

    #[test]
    fn remove_swap() {
        let mut upto: UpTo<5, i32> = upto![1, 2, 3, 4, 5];

        let v = upto.remove_swap(1);

        assert_eq!(v, 2);
        assert_eq!(upto[1], 5);
    }
}