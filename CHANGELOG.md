# Changelog

## [Unreleased]

- Removed Support for the former `CStr` type.

This type represented a null-terminated, UTF-8, slice. In practice, we had to include code to parse
UTF-8 strings into the library, which kinda doubles what the core library already does. Moreover,
the `CStr` name basically alwaysa refers to ASCII C strings in the Rust ecosystem at this point.
Chaging its meaning was already a bit surprising.
