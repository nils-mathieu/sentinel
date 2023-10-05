# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project **does not** adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html)
(yet). Before `1.0`, breaking change may occur every minor version.

## [0.5.2] - 05/10/2023

### Added

- Made more functions `const` when possible.

- Added functions to convert from/to slices of sentinel terminated slices.

### Breaking Changes

- Removed the `Sentinel` trait.

Having a trait to remain generic over the sentinel value(s) to keep track of was not really useful.
I've been using the library for a bit and I only ever used the `Null` sentinel. To keep the library
simple and try to prevent potential bugs, this trait is now re-purposed.

- Removed the `UnwrapSentinel` and `DefaultSentinel` traits.

Those two traits are not included in the new `Sentinel` trait.

- Removed the `sslice!` macro. This identifier will be re-used later.

### Bug Fixes

- Fixed a bound typo preventing to compare a `[T]` with a `SSLice<T>`.

## [0.4.0] - 31/01/2023

### Breaking Changes

- Removed Support for the former `CStr` type.

This type represented a null-terminated, UTF-8, slice. In practice, we had to include code to parse
UTF-8 strings into the library, which kinda doubles what the core library already does. Moreover,
the `CStr` name basically alwaysa refers to ASCII C strings in the Rust ecosystem at this point.
Chaging its meaning was already a bit surprising.

- Everything related to c-like strings is now using the `CStr` alias instead of a mix of
  `SSlice<u8>` and `SSlice<i8>`. Some function of `SSlice<i8>` are no longer available.
