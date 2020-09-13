# lenient-version-parser

Lenient parser for Semantic Version numbers.

### Motivation

This crate aims to provide an alternative parser for [semver `Version`s](https://crates.io/crates/semver).

Instead of adhering to the semver specification, this parser is more lenient in what it allows.
The differenc include:

- Minor and Path are optional an default to 0 (e.g. "1" parses at "1.0.0")
- Pre-release identifier may be separated by `.` as well (e.g. "1.2.3.rc1" parses at "1.2.3-rc1")
- Some pre-release identifiers are parsed as build identifier (e.g. "1.2.3.Final" parses at "1.2.3+Final")

This diagram shows lenient parsing grammar

![doc/railroad.svg](./doc/railroad.svg)

License: MIT OR Apache-2.0
