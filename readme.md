# Sentinel

`sentinel` is a sentinel-terminated slice library.

## How it works

### Rust Slices

In Rust, the slice type `&[T]` is basically defined like that: `(*const T, usize)`. The `usize` indicates the number of `T`s referenced at the `*const T`. Knowing in advance the size of an array, like that, has numerous advantages, which won't be discussed here.

There is however two main problems with the `&[T]` type:

1. It is not (at least, yet) FFI-safe. One cannot create an `extern "C" fn(s: &[u32])` function and expect it to work when calling it from C-code.

2. The size of `&[T]` has the size of two `usize`s.

### Sentinels?

A sentinel is a special value that is used to determine the end of an array. For example, in C, the `char *` type can be a pointer to a "null-terminated" string. This is an example of sentinel-terminated slice.

```txt
CString:
char *ptr
 |
'H' 'e' 'l' 'l' 'o' '\0'
                      ^ sentinel, anything after this point may be invalid.
str:
*const u8, 5
 |
'H' 'e' 'l' 'l' 'o'
                    ^ no sentinel, we know the slice contains 5 elements.
```

This crate remains generic over how sentinels are defined. It uses the [`Sentinel`] trait, which is roughly defined like that:

```Rust
trait Sentinel<T> {
    fn is_sentinel(val: &T) -> bool;
}
```

It is used to determine whether a specific instance of `T` should be treated as a "sentinel" value.

### SSlice

Finally, in conjonction with the [`Sentinel`] trait, this crate defines the [`SSlice<T, S>`] type. It is generic over `T`, the type of stored elements, and over `S: Sentinel<T>`, defining which instances of `T` should be considered sentinel values.

```Rust
struct SSlice<T, S: Sentinel<T>> {
    _marker: PhantomData<(T, S)>,
}
```

Note that this type actually contains no data. Only references to this type can be created (i.e. `&SSlice<T, S>` or `&mut SSlice<T, S>`), and those references have the size a single `usize`.

## Features

 - `alloc` - adds support for the `alloc` crate. This adds the [`SBox<T, S>`] type.

 - `null` - this feature enables the [`Null`] type, which implements the [`Sentinel`] trait for common types (integers, pointers, Option<T>).

 - `nightly` - makes use of the unstable `extern_type` feature to make sure no instance of [`SSlice<T, S>`] can be created on the stack by making it [`!Sized`]. This feature also enables support for the new `allocator_api` unstable feature.

*`null` and `alloc` are enabled by default.*

# Old `sentinel` crate

The name `sentinel` was kindly given to me by the previous maintainer of [this](https://github.com/maidsafe-archive/sentinel) project.

Every pre-0.2 versions (on crates.io) contain the source code of that crate.
 
[`Sentinel`]: https://docs.rs/sentinel/0.2.0/sentinel/trait.Sentinel.html
[`!Sized`]: https://doc.rust-lang.org/stable/core/marker/trait.Sized.html
[`Null`]: https://docs.rs/sentinel/0.2.0/sentinel/struct.Null.html
[`SBox<T, S>`]: https://docs.rs/sentinel/0.2.0/sentinel/struct.SBox.html
[`SSlice<T, S>`]: https://docs.rs/sentinel/0.2.0/sentinel/struct.SSlice.html