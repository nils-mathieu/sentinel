# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Breaking Changes

- Removed Support for the former `CStr` type.

This type represented a null-terminated, UTF-8, slice. In practice, we had to include code to parse
UTF-8 strings into the library, which kinda doubles what the core library already does. Moreover,
the `CStr` name basically alwaysa refers to ASCII C strings in the Rust ecosystem at this point.
Chaging its meaning was already a bit surprising.
