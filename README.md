
[![Crate](https://img.shields.io/badgs/crates.io-upto-v0.1.3)](https://github.com/RylanYancey/upto)

# UpTo 
Fixed-Capacity Variable Length Stack-Allocated Arrays

## When to use UpTo
UpTo is best when you know the maximum capacity a vector needs to have, but you
don't want to allocate the whole thing all at once. It is also best to keep UpTo capacities
relatively small. If you need a high-capacity container, just use a Vec<T>. 

## Safety
This crate makes heavy use of `std::mem::MaybeUninit<T>`. The UpTo type is internally a `[MaybeUninit<T>; N]`. Reading 
from a `MaybeUninit` is inherently unsafe, but we can guarantee safety since any value at an index less than `UpTo.len`
is known to be initialized. 

## Example
```
use upto::{UpTo, upto};

// allocate an array with capacity 5.
let mut upto: UpTo<5, i32> = UpTo::new();

// push values.
upto.push(720);
upto.push(1080);
upto.push(1440);
upto.push(2160);

// Iter & IterMut
// output: "720, 1080, 1440, 2160"
for v in upto.iter() {
    println!("{v}, ")
}

for v in upto.iter_mut() {
    *v += 144;
}

// Remove & Insert values.
upto.remove(3);
upto.insert(540, 0);

// Index & IndexMut.
println!("{}", upto[3]);
upto[2] += 144;

// First (try_first_mut, try_first, first, first_mut)
if let Some(v) = upto.try_first() {
    println!("{v}")
}

// Last (try_last_mut, try_last, last, last_mut)
if let Some(v) = upto.try_last_mut() {
    *v += 144;
}

// Pop
while let Some(v) = upto.pop() {
    println!("{v}")
}
```