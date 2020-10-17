//! Lenient parser for Semantic Version numbers.
//!
//! ## Motivation
//!
//! This crate aims to provide an alternative parser for [semver `Version`s](https://crates.io/crates/semver).
//!
//! Instead of adhering to the semver specification, this parser is more lenient in what it allows.
//! The differenc include:
//!
//! - Minor and Path are optional an default to 0 (e.g. "1" parses as "1.0.0")
//! - Pre-release identifier may be separated by `.` as well (e.g. "1.2.3.rc1" parses as "1.2.3-rc1")
//! - Some pre-release identifiers are parsed as build identifier (e.g. "1.2.3.Final" parses as "1.2.3+Final")
//! - Additional numeric identifiers are parsed as build identifier (e.g "1.2.3.4.5" parses as "1.2.3+4.5")
//! - A leading `v` or `V` is allowed (e.g. "v1.2.3" parses as "1.2.3")
//!
//! This diagram shows lenient parsing grammar
//!
//! ![have a look at doc/railroad.svg](https://ssl.webpack.de/ghcdn.knutwalker.de/lenient-semver/doc/railroad.svg)
//!
//! ## Examples
//!
//! ```rust
//! use semver::Version;
//!
//! let version = lenient_semver::parse("1.2.3");
//! assert_eq!(version, Ok(Version::new(1, 2, 3)));
//!
//! // examples of a version that would not be accepted by semver_parser
//! assert_eq!(
//!     lenient_semver::parse("1.2.M1").unwrap(),
//!     Version::parse("1.2.0-M1").unwrap()
//! );
//! assert!(Version::parse("1.2.M1").is_err());
//!
//! assert_eq!(
//!     lenient_semver::parse("1").unwrap(),
//!     Version::parse("1.0.0").unwrap()
//! );
//! assert!(Version::parse("1").is_err());
//!
//! assert_eq!(
//!     lenient_semver::parse("1.2.3.Final").unwrap(),
//!     Version::parse("1.2.3+Final").unwrap()
//! );
//! assert!(Version::parse("1.2.3.Final").is_err());
//!
//! assert_eq!(
//!     lenient_semver::parse("1.2.3.4.5").unwrap(),
//!     Version::parse("1.2.3+4.5").unwrap()
//! );
//! assert!(Version::parse("1.2.3.4.5").is_err());
//!
//! assert_eq!(
//!     lenient_semver::parse("v1.2.3").unwrap(),
//!     Version::parse("1.2.3").unwrap()
//! );
//! assert!(Version::parse("v1.2.3").is_err());
//! ```
//!
//! ## Features
//!
//! `lenient_semver` comes with a number of features:
//!
//!
//! |  feature name | default enabled | transitive dependencies | purpose
//! | ------------: | --------------- | ----------------------- | --------
//! |      semver11 | **yes**         | `semver = "0.11.0"`     | Provides `VersionBuilder` implementation for `semver = "0.11.0"`.
//! |      semver10 | no              | `semver = "0.10.0"`     | Provides `VersionBuilder` implementation for `semver = "0.10.0"`.
//! |  version_lite | no              | `lenient_version = "*"` | A custom Version as alternative to `semver::Version` that complements some leneient features, such as additional numbers beyond patch.
//! | version_serde | no              | `serde = "1"`           | Serde Deserializer and Serializer implementation for `lenient_version`.
//!
//!
//! ### Examples
//!
//! #### `semver11`
//!
//! ```toml
//! lenient_semver = { version = "*", features = [ "semver11" ] }
//! ```
//!
//! ```rust
//! use semver::Version as Version11;
//!
//! // This features is enabled by default and is usable through `parse` directly,
//! // but can also be used with `parse_into`.
//! let version = lenient_semver::parse_into::<Version11>("v1.2.3.Final").unwrap();
//! assert_eq!(version, Version11::parse("1.2.3+Final").unwrap());
//! ```
//!
//! #### `semver10`
//!
//! ```toml
//! lenient_semver = { version = "*", features = [ "semver10" ] }
//! ```
//!
//! ```rust
//! // We have both version of semver available, the older one
//! // is renamed to `semver010`.
//! use semver010::Version as Version10;
//!
//! // The default parse is fixed to the latest semver::Version,
//! // so we need to use `parse_into`.
//! let version = lenient_semver::parse_into::<Version10>("v1.2.3.Final").unwrap();
//! assert_eq!(version, Version10::parse("1.2.3+Final").unwrap());
//! ```
//!
//! #### `version_lite`
//!
//! ```toml
//! lenient_semver = { version = "*", features = [ "version_lite" ] }
//! ```
//!
//! With this features, lenient_semver now comes with it's own version.
//! That particular implementation supports numbers beyond patch directly.
//! Note that lenient_semver still parses those additional number without complaining,
//! but they are added as build attribute to semver Versions.
//!
//! ```rust
//! use lenient_semver::Version;
//!
//! let version = lenient_semver::parse_into::<Version>("1.3.3.7").unwrap();
//! assert_eq!(version, Version::parse("1.3.3.7").unwrap()); // Version::parse delegates to this parser
//! ```
//!
//! The native support allows such version to be compared properly, which does not work with semver.
//!
//! ```rust
//! use lenient_semver::Version;
//!
//! let version_a = Version::parse("1.3.3.7").unwrap();
//! let version_b = Version::parse("1.3.3.8").unwrap();
//! assert!(version_a < version_b);
//!
//! // with semver, that fails:
//! let version_a = lenient_semver::parse("1.3.3.7").unwrap();
//! let version_b = lenient_semver::parse("1.3.3.8").unwrap();
//! assert_eq!(version_a < version_b, false);
//! assert_eq!(version_a, version_b);
//! ```
//!
//! #### `version_serde`
//!
//! ```toml
//! lenient_semver = { version = "*", features = [ "version_serde" ] }
//! ```
//!
//! This feature also enabled `version_lite` and brings serde support for the own Version type.
//! Since `lenient_semver::Version` does not take ownership of the metadata identifiers,
//! the lifetime of the deserialization result is bound to the input.
//!
//! ```rust
//! # // This example is replicated as test_serde_feature
//! # // Please try to keep them in sync
//! use lenient_semver::{Version, VersionBuilder};
//! use serde::Deserialize;
//!
//! #[derive(Debug, Deserialize)]
//! struct DependencySpec<'input> {
//!     /// Refer to name as owned value
//!     name: String,
//!     /// Borrows from the input string
//!     #[serde(borrow)]
//!     version: Version<'input>,
//! }
//!
//! let input = "
//!     {
//!         \"name\": \"lenient_semver\",
//!         \"version\": \"1.3.3.7+build.42\"
//!     }";
//! // make an owned copy, so we don't cheat by using the 'static lifetime.
//! let input = String::from(input);
//!
//! // use serde as one would normally do
//! let dep: DependencySpec = serde_json::from_str(input.as_ref()).unwrap();
//! println!("{:?}", dep);
//!
//! // cannot move out of `input` because it is borrowed
//! // drop(input);
//!
//! let mut expected = Version::new(1, 3, 3);
//! expected.add_additional(7);
//! expected.add_build("build");
//! expected.add_build("42");
//!
//! assert_eq!(dep.version, expected);
//!
//! // now we can drop the input
//! drop(input);
//! ```
pub use lenient_semver_parser::{self as parser, VersionBuilder};
#[cfg(feature = "version_lite")]
pub use lenient_version::{Version, Version as VersionLite};

/// Parse a string slice into a Version.
///
/// This parser does not require semver-specification conformant input and is more lenient in what it allows.
/// The differenc include:
///
/// - Minor and Path are optional an default to 0 (e.g. "1" parses as "1.0.0")
/// - Pre-release identifier may be separated by `.` as well (e.g. "1.2.3.rc1" parses as "1.2.3-rc1")
/// - Some pre-release identifiers are parsed as build identifier (e.g. "1.2.3.Final" parses as "1.2.3+Final")
/// - Additional numeric identifiers are parsed as build identifier (e.g "1.2.3.4.5" parses as "1.2.3+4.5")
/// - A leading `v` or `V` is allowed (e.g. "v1.2.3" parses as "1.2.3")
///
/// This diagram shows lenient parsing grammar
///
/// ![have a look at doc/railroad.svg](https://ssl.webpack.de/ghcdn.knutwalker.de/lenient-semver/doc/railroad.svg)
///
/// ## Examples
///
/// ```rust
/// # use semver::Version;
///
/// let version = lenient_semver::parse("1.2.3");
/// assert_eq!(version, Ok(Version::new(1, 2, 3)));
///
/// // examples of a version that would not be accepted by semver_parser
/// assert_eq!(
///     lenient_semver::parse("1.2.M1").unwrap(),
///     Version::parse("1.2.0-M1").unwrap()
/// );
/// assert!(Version::parse("1.2.M1").is_err());
///
/// assert_eq!(
///     lenient_semver::parse("1").unwrap(),
///     Version::parse("1.0.0").unwrap()
/// );
/// assert!(Version::parse("1").is_err());
///
/// assert_eq!(
///     lenient_semver::parse("1.2.3.Final").unwrap(),
///     Version::parse("1.2.3+Final").unwrap()
/// );
/// assert!(Version::parse("1.2.3.Final").is_err());
///
/// assert_eq!(
///     lenient_semver::parse("1.2.3.4.5").unwrap(),
///     Version::parse("1.2.3+4.5").unwrap()
/// );
/// assert!(Version::parse("1.2.3.4.5").is_err());
///
/// assert_eq!(
///     lenient_semver::parse("v1.2.3").unwrap(),
///     Version::parse("1.2.3").unwrap()
/// );
/// assert!(Version::parse("v1.2.3").is_err());
/// ```
///
/// This method is fixes to return a [`semver::Version`].
/// A more flexible variant is [`lenient_semver::parse_into`].
#[cfg(feature = "semver11")]
pub fn parse<'input>(input: &'input str) -> Result<semver::Version, parser::Error<'input>> {
    parser::parse::<semver::Version>(input)
}

/// Parse a string slice into a Version.
///
/// This parser does not require semver-specification conformant input and is more lenient in what it allows.
/// The differenc include:
///
/// - Minor and Path are optional an default to 0 (e.g. "1" parses as "1.0.0")
/// - Pre-release identifier may be separated by `.` as well (e.g. "1.2.3.rc1" parses as "1.2.3-rc1")
/// - Some pre-release identifiers are parsed as build identifier (e.g. "1.2.3.Final" parses as "1.2.3+Final")
/// - Additional numeric identifiers are parsed as build identifier (e.g "1.2.3.4.5" parses as "1.2.3+4.5")
/// - A leading `v` or `V` is allowed (e.g. "v1.2.3" parses as "1.2.3")
///
/// This diagram shows lenient parsing grammar
///
/// ![have a look at doc/railroad.svg](https://ssl.webpack.de/ghcdn.knutwalker.de/lenient-semver/doc/railroad.svg)
///
/// This method can parse anything that implements [`VersionBuilder`].
///
/// ## Examples
///
/// ```rust
/// use lenient_semver::Version;
///
/// let version = lenient_semver::parse_into::<Version>("1.2.3");
/// assert_eq!(version, Ok(Version::new(1, 2, 3)));
///
/// // examples of a version that would not be accepted by semver_parser
/// assert_eq!(
///     lenient_semver::parse_into::<Version>("1.2.M1").unwrap(),
///     Version::parse("1.2.0-M1").unwrap()
/// );
///
/// assert_eq!(
///     lenient_semver::parse_into::<Version>("1").unwrap(),
///     Version::parse("1.0.0").unwrap()
/// );
///
/// assert_eq!(
///     lenient_semver::parse_into::<Version>("1.2.3.Final").unwrap(),
///     Version::parse("1.2.3+Final").unwrap()
/// );
///
/// assert_eq!(
///     lenient_semver::parse_into::<Version>("1.2.3.4.5").unwrap(),
///     Version::parse("1.2.3.4.5").unwrap()
/// );
///
/// assert_eq!(
///     lenient_semver::parse_into::<Version>("v1.2.3").unwrap(),
///     Version::parse("1.2.3").unwrap()
/// );
/// ```
pub fn parse_into<'input, V>(input: &'input str) -> Result<V::Out, parser::Error<'input>>
where
    V: VersionBuilder<'input>,
{
    parser::parse::<V>(input)
}

#[cfg(test)]
mod tests {

    //! This test is replicated in the crate documentation as a doc test
    //! Please try to keep them in sync

    use lenient_semver_parser::VersionBuilder;
    use lenient_version::Version;
    use serde::Deserialize;
    #[derive(Debug, Deserialize)]
    struct DependencySpec<'input> {
        /// Refer to name as owned value
        name: String,
        /// Borrows from the input string
        #[serde(borrow)]
        version: Version<'input>,
    }

    #[test]
    fn test_serde_feature() {
        let input = "
            {
                \"name\": \"lenient_semver\",
                \"version\": \"1.3.3.7+build.42\"
            }";
        let input = String::from(input);
        let dep = serde_json::from_str::<DependencySpec>(input.as_ref()).unwrap();

        // cannot move out of `input` because it is borrowed
        // drop(input);

        let mut expected = Version::new(1, 3, 3);
        expected.add_additional(7);
        expected.add_build("build");
        expected.add_build("42");

        assert_eq!(dep.version, expected);

        // now we can drop the input
        drop(input);
    }
}
