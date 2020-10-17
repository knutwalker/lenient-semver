# Lenient Semantic Version Parser

Lenient parser for Semantic Version numbers.

### Motivation

This crate aims to provide an alternative parser for [semver `Version`s](https://crates.io/crates/semver).

Instead of adhering to the semver specification, this parser is more lenient in what it allows.
The differenc include:

- Minor and Path are optional an default to 0 (e.g. "1" parses as "1.0.0")
- Pre-release identifier may be separated by `.` as well (e.g. "1.2.3.rc1" parses as "1.2.3-rc1")
- Some pre-release identifiers are parsed as build identifier (e.g. "1.2.3.Final" parses as "1.2.3+Final")
- Additional numeric identifiers are parsed as build identifier (e.g "1.2.3.4.5" parses as "1.2.3+4.5")
- A leading `v` or `V` is allowed (e.g. "v1.2.3" parses as "1.2.3")
- Numbers that overflow an u64 are treated as strings (e.g. "1.2.3-9876543210987654321098765432109876543210" parses without error)

This diagram shows lenient parsing grammar

![have a look at doc/railroad.svg](https://ssl.webpack.de/ghcdn.knutwalker.de/lenient-semver/doc/railroad.svg)

### Examples

```rust
use semver::Version;

let version = lenient_semver::parse("1.2.3");
assert_eq!(version, Ok(Version::new(1, 2, 3)));

// examples of a version that would not be accepted by semver_parser
assert_eq!(
    lenient_semver::parse("1.2.M1").unwrap(),
    Version::parse("1.2.0-M1").unwrap()
);
assert!(Version::parse("1.2.M1").is_err());

assert_eq!(
    lenient_semver::parse("1").unwrap(),
    Version::parse("1.0.0").unwrap()
);
assert!(Version::parse("1").is_err());

assert_eq!(
    lenient_semver::parse("1.2.3.Final").unwrap(),
    Version::parse("1.2.3+Final").unwrap()
);
assert!(Version::parse("1.2.3.Final").is_err());

assert_eq!(
    lenient_semver::parse("1.2.3.4.5").unwrap(),
    Version::parse("1.2.3+4.5").unwrap()
);
assert!(Version::parse("1.2.3.4.5").is_err());

assert_eq!(
    lenient_semver::parse("v1.2.3").unwrap(),
    Version::parse("1.2.3").unwrap()
);
assert!(Version::parse("v1.2.3").is_err());

assert_eq!(
    lenient_semver::parse("1.2.9876543210987654321098765432109876543210").unwrap(),
    Version::parse("1.2.0-9876543210987654321098765432109876543210").unwrap()
);
assert!(Version::parse("1.2.9876543210987654321098765432109876543210").is_err());
```

### Parsing into custom versions

The parser is not fixed on returning a `semver::Version`, it instead parses into a `lenient_semver::VersionBuilder`.
The default features for this crate contain a `VersionBuilder` implementation for `semver::Version`, but any implementation can be used with `parse_into`.

#### Examples

```rust
use lenient_semver::VersionBuilder;

/// Simpler version struct that lives only on the stack
#[derive(Debug, Default)]
struct MyVersion {
    numbers: [u64; 3],
    is_pre_release: bool,
}

/// The VersionBuilder trait is generic over the lifetime of the input string.
/// We don't store references to those strings, so we don't care about the specific lifetime.
impl VersionBuilder<'_> for MyVersion {
    /// We will modify the target struct directly
    type Out = Self;

    /// Construct a new builder instance.
    /// One can only expect `set_major` to be called before `build`, all other methods are optional.
    fn new() -> Self {
        Self::default()
    }

    /// Construct the final result. In this case, we can just return ourselves.
    fn build(self) -> Self::Out {
        self
    }

    /// Called when the major component was found.
    fn set_major(&mut self, major: u64) {
        self.numbers[0] = major;
    }

    /// Called when the minor component was found.
    fn set_minor(&mut self, minor: u64) {
        self.numbers[1] = minor;
    }

    /// Called when the patch component was found.
    fn set_patch(&mut self, patch: u64) {
        self.numbers[2] = patch;
    }

    /// Called when any pre-relase metadata identifier was found.
    /// This identifier can just numeric, no attempts at parsing it into a number have been made.
    /// For this implementation, we don't care about the value, just it's presence.
    fn add_pre_release(&mut self, _pre_release: &str) {
        self.is_pre_release = true
    }
}

let input = "1.3.3.7-alpha21+build.42";
let my_version = lenient_semver::parse_into::<MyVersion>(input).unwrap();

assert_eq!([1, 3, 3], my_version.numbers);
assert!(my_version.is_pre_release);
```

The VersionBuilder has empty default implementation for the various methods, making it easy to use it for use-cases beyond just parsing.
The following example implements a function that checks if a given string represents any form of pre-release version.

```rust
use lenient_semver::VersionBuilder;

/// newtype around bool, so we can implement the VersionBuilder trait for it
#[derive(Debug, Default)]
struct IsPreRelease(bool);

impl VersionBuilder<'_> for IsPreRelease {
    /// Here we parse into a different value than Self
    type Out = bool;

    fn new() -> Self {
        Self::default()
    }

    /// Return the wrapped bool
    fn build(self) -> Self::Out {
        self.0
    }

    /// We only care about this method and can ignore all the other ones
    fn add_pre_release(&mut self, _pre_release: &str) {
        self.0 = true;
    }
}

/// This method also return false for invalid version strings,
/// which is technically true, as those are not pre-release versions.
/// Usually you would want to have a better error handling.
fn is_pre_release(v: &str) -> bool {
    lenient_semver::parse_into::<IsPreRelease>(v).unwrap_or_default()
}

assert!(is_pre_release("1.2.3-pre") == true);
assert!(is_pre_release("1.2.3") == false);
assert!(is_pre_release("1.2.3+build") == false);
```

### Features

`lenient_semver` comes with a number of features:


|   feature name | default enabled | transitive dependencies | purpose
| -------------: | --------------- | ----------------------- | --------
|       semver11 | **yes**         | `semver = "0.11.0"`     | Provides `VersionBuilder` implementation for `semver = "0.11.0"`.
|       semver10 | no              | `semver = "0.10.0"`     | Provides `VersionBuilder` implementation for `semver = "0.10.0"`.
|   version_lite | no              | `lenient_version = "*"` | A custom Version as alternative to `semver::Version` that complements some leneient features, such as additional numbers beyond patch.
| version_semver | no              | `lenient_version = "*"` | Add conversions From `lenient_version` Into `semver::Version`.
|  version_serde | no              | `serde = "1"`           | Serde Deserializer and Serializer implementation for `lenient_version`.


#### Examples

##### `semver11`

```toml
lenient_semver = { version = "*", features = [ "semver11" ] }
```

```rust
use semver::Version as Version11;

// This features is enabled by default and is usable through `parse` directly,
// but can also be used with `parse_into`.
let version = lenient_semver::parse_into::<Version11>("v1.2.3.Final").unwrap();
assert_eq!(version, Version11::parse("1.2.3+Final").unwrap());
```

##### `semver10`

```toml
lenient_semver = { version = "*", features = [ "semver10" ] }
```

```rust
// We have both version of semver available, the older one
// is renamed to `semver010`.
use semver010::Version as Version10;

// The default parse is fixed to the latest semver::Version,
// so we need to use `parse_into`.
let version = lenient_semver::parse_into::<Version10>("v1.2.3.Final").unwrap();
assert_eq!(version, Version10::parse("1.2.3+Final").unwrap());
```

##### `version_lite`

```toml
lenient_semver = { version = "*", features = [ "version_lite" ] }
```

With this features, lenient_semver now comes with it's own version.
That particular implementation supports numbers beyond patch directly.
Note that lenient_semver still parses those additional number without complaining,
but they are added as build attribute to semver Versions.

```rust
use lenient_semver::Version;

let version = lenient_semver::parse_into::<Version>("1.3.3.7").unwrap();
assert_eq!(version, Version::parse("1.3.3.7").unwrap()); // Version::parse delegates to this parser
```

The native support allows such version to be compared properly, which does not work with semver.

```rust
use lenient_semver::Version;

let version_a = Version::parse("1.3.3.7").unwrap();
let version_b = Version::parse("1.3.3.8").unwrap();
assert!(version_a < version_b);

// with semver, that fails:
let version_a = lenient_semver::parse("1.3.3.7").unwrap();
let version_b = lenient_semver::parse("1.3.3.8").unwrap();
assert_eq!(version_a < version_b, false);
assert_eq!(version_a, version_b);
```

Furthermore, `Version` does not own the data for the metadata identifiers.
The metadata can be disassociated, so the version can reference a different owner.

```rust
use lenient_semver::{Version, VersionBuilder};

let input = "1.3.3.7-beta.21+build.42";
// make an owned copy, so we don't cheat by using the 'static lifetime.
let input = String::from(input);

// This version references slices from the `input` String
let version = lenient_semver::parse_into::<Version>(input.as_ref()).unwrap();

// Which prevents us from dropping the input
// drop(input);

// We can disassociate the metadata, which allows the new version to reference something else
let (mut version, pre, build) = version.disassociate_metadata();

// We still get the referenced input slices, so we create owned copies
let pre: Vec<String> = pre.into_iter().map(ToOwned::to_owned).collect();
let build: Vec<String> = build.into_iter().map(ToOwned::to_owned).collect();

// now we can safely drop the input
drop(input);

// We can also re-add the cloned identifiers.
// The version would now be bound to the lifetime of this method.
// Just for fun, we swap pre-release and build
for pre in &pre {
    version.add_build(pre.as_ref());
}
for build in &build {
    version.add_pre_release(build.as_ref());
}

assert_eq!("1.3.3.7-build.42+beta.21".to_string(), version.to_string());
```

##### `version_semver`

```toml
lenient_semver = { version = "*", features = [ "version_semver" ] }
```

If you need to store an owned copy of the version information, you should copy into `semver::Version` or your custom version type instead.
If you only ever intend to store the version information, it might make more sense to parse directly into `semver::Version` instead.

```rust
use semver::Version;

let input = String::from("v1.3.3.7-beta-21+build-42");
let version = lenient_semver::Version::parse(&input).unwrap();
let version = Version::from(version);
assert_eq!("1.3.3-beta.21+7.build.42", &version.to_string());
```

##### `version_serde`

```toml
lenient_semver = { version = "*", features = [ "version_serde" ] }
```

This feature also enabled `version_lite` and brings serde support for the own Version type.
Since `lenient_semver::Version` does not take ownership of the metadata identifiers,
the lifetime of the deserialization result is bound to the input.

```rust
use lenient_semver::{Version, VersionBuilder};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct DependencySpec<'input> {
    /// Refer to name as owned value
    name: String,
    /// Borrows from the input string
    #[serde(borrow)]
    version: Version<'input>,
}

let input = "
    {
        \"name\": \"lenient_semver\",
        \"version\": \"1.3.3.7+build.42\"
    }";
// make an owned copy, so we don't cheat by using the 'static lifetime.
let input = String::from(input);

// use serde as one would normally do
let dep: DependencySpec = serde_json::from_str(input.as_ref()).unwrap();
println!("{:?}", dep);

// cannot move out of `input` because it is borrowed
// drop(input);

let mut expected = Version::new(1, 3, 3);
expected.add_additional(7);
expected.add_build("build");
expected.add_build("42");

assert_eq!(dep.version, expected);

// now we can drop the input
drop(input);
```

License: MIT OR Apache-2.0
