# Lenient Semantic Version Parser

Lenient parser for Semantic Version numbers.

### Motivation

This crate aims to provide an alternative parser for [semver `Version`s](https://crates.io/crates/semver).

Instead of adhering to the semver specification, this parser is more lenient in what it allows.
The differenc include:

- Minor and Path are optional an default to 0 (e.g. "1" parses at "1.0.0")
- Pre-release identifier may be separated by `.` as well (e.g. "1.2.3.rc1" parses at "1.2.3-rc1")
- Some pre-release identifiers are parsed as build identifier (e.g. "1.2.3.Final" parses at "1.2.3+Final")
- A leading `v` or `V` is allowed (e.g. "v1.2.3")

This diagram shows lenient parsing grammar

![have a look at doc/railroad.svg](https://ssl.webpack.de/ghcdn.knutwalker.de/lenient-semver/doc/railroad.svg)

### Examples

```rust
use semver::Version;

let version = lenient_semver::parse::<Version>("1.2.3");
assert_eq!(version, Ok(Version::new(1, 2, 3)));

// examples of a version that would not be accepted by semver_parser
assert_eq!(
    lenient_semver::parse::<Version>("1.2.M1").unwrap(),
    Version::parse("1.2.0-M1").unwrap()
);
assert!(Version::parse("1.2.M1").is_err());

assert_eq!(
    lenient_semver::parse::<Version>("1").unwrap(),
    Version::parse("1.0.0").unwrap()
);
assert!(Version::parse("1").is_err());

assert_eq!(
    lenient_semver::parse::<Version>("1.2.3.Final").unwrap(),
    Version::parse("1.2.3+Final").unwrap()
);
assert!(Version::parse("1.2.3.Final").is_err());

assert_eq!(
    lenient_semver::parse::<Version>("v1.2.3").unwrap(),
    Version::parse("1.2.3").unwrap()
);
assert!(Version::parse("v1.2.3").is_err());
```

License: MIT OR Apache-2.0
