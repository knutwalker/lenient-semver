//! Lenient semantic version.
//!
//! Companion version struct for the lenient_semver parser.
//! Compared to [`semver::Version`], this version:
//!  - Supports additional numeric identifiers (e.g. 1.2.3.4.5)
//!  - Does not allocate Strings for metadata (it still allocated vectors)
#![deny(
    bad_style,
    const_err,
    dead_code,
    improper_ctypes,
    missing_copy_implementations,
    missing_debug_implementations,
    missing_docs,
    no_mangle_generic_items,
    non_shorthand_field_patterns,
    overflowing_literals,
    path_statements,
    patterns_in_fns_without_body,
    private_in_public,
    rust_2018_idioms,
    trivial_casts,
    trivial_numeric_casts,
    unconditional_recursion,
    unsafe_code,
    unused_allocation,
    unused_comparisons,
    unused_extern_crates,
    unused_import_braces,
    unused_parens,
    unused_qualifications,
    unused_results,
    unused,
    while_true
)]

use std::{
    cmp::Ordering,
    convert::TryFrom,
    fmt::{self, Display, Write},
    hash,
};

/// Represents a lenient semantic version number.
///
/// The version is bound to the lifetime of the input string.
#[derive(Debug, Clone, Eq)]
pub struct Version<'input> {
    /// The major version.
    pub major: u64,
    /// The minor version.
    pub minor: u64,
    /// The patch version.
    pub patch: u64,
    /// additional version numbers.
    pub additional: Vec<u64>,
    /// The pre-release metadata.
    pub pre: Vec<&'input str>,
    /// The build metadata.
    pub build: Vec<&'input str>,
}

impl<'input> Version<'input> {
    /// Constructs a new, empty version
    ///
    /// ## Examples
    ///
    /// ```
    /// # use lenient_version::Version;
    /// let version = Version::empty();
    /// assert_eq!(version.to_string(), "0.0.0")
    /// ```
    pub const fn empty() -> Self {
        Version {
            major: 0,
            minor: 0,
            patch: 0,
            additional: Vec::new(),
            pre: Vec::new(),
            build: Vec::new(),
        }
    }

    /// Constructs a new version out of the three regular version components
    ///
    /// ## Examples
    ///
    /// ```
    /// # use lenient_version::Version;
    /// let version = Version::new(1, 2, 3);
    /// assert_eq!(version.to_string(), "1.2.3")
    /// ```
    pub const fn new(major: u64, minor: u64, patch: u64) -> Self {
        Version {
            major,
            minor,
            patch,
            additional: Vec::new(),
            pre: Vec::new(),
            build: Vec::new(),
        }
    }

    /// Parse a string slice into a Version.
    ///
    /// This parser does not require semver-specification conformant input and is more lenient in what it allows.
    /// For more information, see [`lenient_semver`].
    ///
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use lenient_version::Version;
    ///
    /// let version = Version::parse("v1.2.3.4.5+build.42");
    /// assert!(version.is_ok());
    /// ```
    #[cfg(feature = "parser")]
    pub fn parse(input: &'input str) -> Result<Self, lenient_semver::Error<'input>> {
        lenient_semver::parse::<Self>(input)
    }

    /// Bumps the major version.
    ///
    /// Sets minor, patch, and additional numbers to 0, removes pre-release and build identifier.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use lenient_version::Version;
    ///
    /// let mut version = Version::parse("1.2.3.4.5-pre+build").unwrap();
    /// version.bump_major();
    /// assert_eq!(version.to_string(), "2.0.0.0.0");
    /// ```
    pub fn bump_major(&mut self) {
        self.major += 1;
        self.minor = 0;
        self.patch = 0;
        self.additional.iter_mut().for_each(|n| *n = 0);
        self.clear_metadata();
    }

    /// Returns a new version with the major version bumped.
    ///
    /// Sets minor, patch, and additional numbers to 0, removes pre-release and build identifier.
    /// The lifetime for the resulting version can differ from the lifetime of this version.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use lenient_version::Version;
    ///
    /// let version = Version::parse("1.2.3.4.5-pre+build").unwrap();
    /// assert_eq!(version.bumped_major().to_string(), "2.0.0.0.0");
    /// ```
    pub fn bumped_major<'a>(&self) -> Version<'a> {
        Version {
            major: self.major + 1,
            minor: 0,
            patch: 0,
            additional: vec![0; self.additional.len()],
            pre: Vec::new(),
            build: Vec::new(),
        }
    }

    /// Bumps the minor version.
    ///
    /// Sets patch and additional numbers to 0, removes pre-release and build identifier.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use lenient_version::Version;
    ///
    /// let mut version = Version::parse("1.2.3.4.5-pre+build").unwrap();
    /// version.bump_minor();
    /// assert_eq!(version.to_string(), "1.3.0.0.0");
    /// ```
    pub fn bump_minor(&mut self) {
        self.minor += 1;
        self.patch = 0;
        self.additional.iter_mut().for_each(|n| *n = 0);
        self.clear_metadata();
    }

    /// Returns a new version with the minor version bumped.
    ///
    /// Sets patch and additional numbers to 0, removes pre-release and build identifier.
    /// The lifetime for the resulting version can differ from the lifetime of this version.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use lenient_version::Version;
    ///
    /// let version = Version::parse("1.2.3.4.5-pre+build").unwrap();
    /// assert_eq!(version.bumped_minor().to_string(), "1.3.0.0.0");
    /// ```
    pub fn bumped_minor<'a>(&self) -> Version<'a> {
        Version {
            major: self.major,
            minor: self.minor + 1,
            patch: 0,
            additional: vec![0; self.additional.len()],
            pre: Vec::new(),
            build: Vec::new(),
        }
    }

    /// Bumps the patch version.
    ///
    /// Sets any additional numbers to 0, removes pre-release and build identifier.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use lenient_version::Version;
    ///
    /// let mut version = Version::parse("1.2.3.4.5-pre+build").unwrap();
    /// version.bump_patch();
    /// assert_eq!(version.to_string(), "1.2.4.0.0");
    /// ```
    pub fn bump_patch(&mut self) {
        self.patch += 1;
        self.additional.iter_mut().for_each(|n| *n = 0);
        self.clear_metadata();
    }

    /// Returns a new version with the patch version bumped.
    ///
    /// Sets any additional numbers to 0, removes pre-release and build identifier.
    /// The lifetime for the resulting version can differ from the lifetime of this version.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use lenient_version::Version;
    ///
    /// let version = Version::parse("1.2.3.4.5-pre+build").unwrap();
    /// assert_eq!(version.bumped_patch().to_string(), "1.2.4.0.0");
    /// ```
    pub fn bumped_patch<'a>(&self) -> Version<'a> {
        Version {
            major: self.major,
            minor: self.minor,
            patch: self.patch + 1,
            additional: vec![0; self.additional.len()],
            pre: Vec::new(),
            build: Vec::new(),
        }
    }

    /// Bumps any additional version.
    ///
    /// Sets any following additional numbers to 0, removes pre-release and build identifier.
    /// If there are not enough additional numbers, only the pre-release and build identifier is removed.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use lenient_version::Version;
    ///
    /// let mut version = Version::parse("1.2.3.4.5-pre+build").unwrap();
    /// version.bump_additional(0);
    /// assert_eq!(version.to_string(), "1.2.3.5.0");
    ///
    /// let mut version = Version::parse("1.2.3.4.5-pre+build").unwrap();
    /// version.bump_additional(1);
    /// assert_eq!(version.to_string(), "1.2.3.4.6");
    ///
    /// let mut version = Version::parse("1.2.3.4.5-pre+build").unwrap();
    /// version.bump_additional(2);
    /// assert_eq!(version.to_string(), "1.2.3.4.5");
    /// ```
    pub fn bump_additional(&mut self, index: usize) {
        let mut add = self.additional.iter_mut().skip(index);
        if let Some(add) = add.next() {
            *add += 1;
        }
        add.for_each(|n| *n = 0);
        self.clear_metadata();
    }

    /// Returns a new version with the minor version bumped.
    ///
    /// Sets patch and additional numbers to 0, removes pre-release and build identifier.
    /// The lifetime for the resulting version can differ from the lifetime of this version.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use lenient_version::Version;
    ///
    /// let version = Version::parse("1.2.3.4.5-pre+build").unwrap();
    /// assert_eq!(version.bumped_additional(0).to_string(), "1.2.3.5.0");
    /// assert_eq!(version.bumped_additional(1).to_string(), "1.2.3.4.6");
    /// assert_eq!(version.bumped_additional(2).to_string(), "1.2.3.4.5");
    /// ```
    pub fn bumped_additional<'a>(&self, index: usize) -> Version<'a> {
        let mut version = Version {
            major: self.major,
            minor: self.minor,
            patch: self.patch,
            additional: self.additional.clone(),
            pre: Vec::new(),
            build: Vec::new(),
        };
        version.bump_additional(index);
        version
    }

    /// Returns true if this version has pre-release metadata, i.e. it represents a pre-release.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use lenient_version::Version;
    ///
    /// let version = Version::parse("1").unwrap();
    /// assert!(!version.is_pre_release());
    ///
    /// let version = Version::parse("1-pre").unwrap();
    /// assert!(version.is_pre_release());
    ///
    /// let version = Version::parse("1+build").unwrap();
    /// assert!(!version.is_pre_release());
    /// ```
    pub fn is_pre_release(&self) -> bool {
        !self.pre.is_empty()
    }

    fn clear_metadata(&mut self) {
        self.pre.clear();
        self.build.clear();
    }
}

impl Default for Version<'_> {
    fn default() -> Self {
        Self::empty()
    }
}

impl<'input> From<u64> for Version<'input> {
    fn from(x: u64) -> Self {
        Version::new(x, 0, 0)
    }
}

impl<'input> From<(u64, u64)> for Version<'input> {
    fn from((x, y): (u64, u64)) -> Self {
        Version::new(x, y, 0)
    }
}

impl<'input> From<(u64, u64, u64)> for Version<'input> {
    fn from((x, y, z): (u64, u64, u64)) -> Self {
        Version::new(x, y, z)
    }
}

impl<'input> From<[u64; 1]> for Version<'input> {
    fn from(v: [u64; 1]) -> Self {
        Version::new(v[0], 0, 0)
    }
}

impl<'input> From<[u64; 2]> for Version<'input> {
    fn from(v: [u64; 2]) -> Self {
        Version::new(v[0], v[1], 0)
    }
}

impl<'input> From<[u64; 3]> for Version<'input> {
    fn from(v: [u64; 3]) -> Self {
        Version::new(v[0], v[1], v[2])
    }
}

#[cfg(feature = "parser")]
impl<'input> TryFrom<&'input str> for Version<'input> {
    type Error = lenient_semver::Error<'input>;

    fn try_from(value: &'input str) -> Result<Self, Self::Error> {
        Self::parse(value)
    }
}

impl Display for Version<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut result = String::with_capacity(16);
        write!(result, "{}.{}.{}", self.major, self.minor, self.patch)?;
        for &additional in self.additional.iter() {
            write!(result, ".{}", additional)?;
        }

        let mut pre = self.pre.iter();
        if let Some(pre) = pre.next() {
            result.push_str("-");
            result.push_str(pre);
        }
        while let Some(pre) = pre.next() {
            result.push_str(".");
            result.push_str(pre);
        }

        let mut build = self.build.iter();
        if let Some(build) = build.next() {
            result.push_str("+");
            result.push_str(build);
        }
        while let Some(build) = build.next() {
            result.push_str(".");
            result.push_str(build);
        }

        f.pad(result.as_ref())
    }
}

impl PartialEq for Version<'_> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.major == other.major
            && self.minor == other.minor
            && self.patch == other.patch
            && self.additional == other.additional
            && self.pre == other.pre
    }
}

impl PartialOrd for Version<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Version<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.major
            .cmp(&other.major)
            .then_with(|| self.minor.cmp(&other.minor))
            .then_with(|| self.patch.cmp(&other.patch))
            .then_with(|| cmp_additional(&self.additional, &other.additional))
            .then_with(|| cmp_pre(&self.pre, &other.pre))
    }
}

fn cmp_additional(a: &[u64], b: &[u64]) -> Ordering {
    AdditionalCmp {
        a: a.iter(),
        b: b.iter(),
    }
    .find(|c| *c != Ordering::Equal)
    .unwrap_or(Ordering::Equal)
}

fn cmp_pre<'input>(a: &[&'input str], b: &[&'input str]) -> Ordering {
    match (a.is_empty(), b.is_empty()) {
        (true, true) => Ordering::Equal,
        (true, false) => Ordering::Greater,
        (false, true) => Ordering::Less,
        (false, false) => PreCmp {
            a: a.iter(),
            b: b.iter(),
        }
        .find(|c| *c != Ordering::Equal)
        .unwrap_or(Ordering::Equal),
    }
}

struct AdditionalCmp<'a, 'b> {
    a: std::slice::Iter<'a, u64>,
    b: std::slice::Iter<'b, u64>,
}

impl<'a, 'b> Iterator for AdditionalCmp<'a, 'b> {
    type Item = Ordering;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.a.next(), self.b.next()) {
            (None, None) => None,
            (Some(a), None) => Some(a.cmp(&0)),
            (None, Some(b)) => Some(0.cmp(b)),
            (Some(a), Some(b)) => Some(a.cmp(b)),
        }
    }
}

struct PreCmp<'a, 'b, 'input> {
    a: std::slice::Iter<'a, &'input str>,
    b: std::slice::Iter<'b, &'input str>,
}

impl<'a, 'b, 'input> Iterator for PreCmp<'a, 'b, 'input> {
    type Item = Ordering;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.a.next(), self.b.next()) {
            (None, None) => None,
            (Some(_), None) => Some(Ordering::Greater),
            (None, Some(_)) => Some(Ordering::Less),
            (Some(a), Some(b)) => Some(cmp_pre_str(a, b)),
        }
    }
}

fn cmp_pre_str(a: &str, b: &str) -> Ordering {
    match (a.parse::<u64>(), b.parse::<u64>()) {
        (Ok(a), Ok(b)) => a.cmp(&b),
        (Ok(_), Err(_)) => Ordering::Less,
        (Err(_), Ok(_)) => Ordering::Greater,
        (Err(_), Err(_)) => a.cmp(&b),
    }
}

impl hash::Hash for Version<'_> {
    fn hash<H: hash::Hasher>(&self, into: &mut H) {
        self.major.hash(into);
        self.minor.hash(into);
        self.patch.hash(into);
        self.additional.hash(into);
        self.pre.hash(into);
    }
}

#[cfg(feature = "parser")]
impl<'input> lenient_semver::VersionBuilder<'input> for Version<'input> {
    type Out = Self;

    fn new() -> Self {
        Version::default()
    }

    fn set_major(&mut self, major: u64) {
        self.major = major;
    }

    fn set_minor(&mut self, minor: u64) {
        self.minor = minor;
    }

    fn set_patch(&mut self, patch: u64) {
        self.patch = patch;
    }

    fn add_additional(&mut self, num: u64) {
        self.additional.push(num);
    }

    fn add_pre_release(&mut self, pre_release: &'input str) {
        self.pre.push(pre_release)
    }

    fn add_build(&mut self, build: &'input str) {
        self.build.push(build)
    }

    fn build(self) -> Self::Out {
        self
    }
}

#[cfg(all(feature = "serde", feature = "parser"))]
use serde::de::{self, Deserialize, Deserializer, Visitor};
#[cfg(feature = "serde")]
use serde::ser::{Serialize, Serializer};
#[cfg(feature = "serde")]
impl Serialize for Version<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_str(self)
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for Version<'de> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct VersionVisitor;

        impl<'de> Visitor<'de> for VersionVisitor {
            type Value = Version<'de>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a version string")
            }

            fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Version::parse(v).map_err(de::Error::custom)
            }
        }

        deserializer.deserialize_str(VersionVisitor)
    }
}

#[cfg(feature = "semver")]
impl From<Version<'_>> for semver::Version {
    fn from(v: Version<'_>) -> Self {
        semver::Version {
            major: v.major,
            minor: v.minor,
            patch: v.patch,
            pre: v.pre.into_iter().map(parse_11).collect(),
            build: v
                .additional
                .into_iter()
                .map(semver::Identifier::Numeric)
                .chain(v.build.into_iter().map(parse_11))
                .collect(),
        }
    }
}

#[cfg(feature = "semver10")]
impl From<Version<'_>> for semver10::Version {
    fn from(v: Version<'_>) -> Self {
        semver10::Version {
            major: v.major,
            minor: v.minor,
            patch: v.patch,
            pre: v.pre.into_iter().map(parse_10).collect(),
            build: v
                .additional
                .into_iter()
                .map(semver10::Identifier::Numeric)
                .chain(v.build.into_iter().map(parse_10))
                .collect(),
        }
    }
}

#[cfg(feature = "semver")]
fn parse_11(s: &str) -> semver::Identifier {
    s.parse::<u64>().map_or_else(
        |_| semver::Identifier::AlphaNumeric(String::from(s)),
        semver::Identifier::Numeric,
    )
}

#[cfg(feature = "semver10")]
fn parse_10(s: &str) -> semver10::Identifier {
    s.parse::<u64>().map_or_else(
        |_| semver10::Identifier::AlphaNumeric(String::from(s)),
        semver10::Identifier::Numeric,
    )
}

#[cfg(test)]
mod tests {
    use super::Version;
    use test_case::test_case;

    #[test]
    fn test_bump_major() {
        let mut version = Version::parse("1.2.3.4.5-pre+build").unwrap();
        version.bump_major();
        assert_eq!(version, Version::parse("2.0.0.0.0").unwrap());
    }

    #[test]
    fn test_bumped_major() {
        let version = Version::parse("1.2.3.4.5-pre+build").unwrap();
        assert_eq!(version.bumped_major(), Version::parse("2.0.0.0.0").unwrap());
    }

    #[test]
    fn test_bump_minor() {
        let mut version = Version::parse("1.2.3.4.5-pre+build").unwrap();
        version.bump_minor();
        assert_eq!(version, Version::parse("1.3.0.0.0").unwrap());
    }

    #[test]
    fn test_bumped_minor() {
        let version = Version::parse("1.2.3.4.5-pre+build").unwrap();
        assert_eq!(version.bumped_minor(), Version::parse("1.3.0.0.0").unwrap());
    }

    #[test]
    fn test_bump_patch() {
        let mut version = Version::parse("1.2.3.4.5-pre+build").unwrap();
        version.bump_patch();
        assert_eq!(version, Version::parse("1.2.4.0.0").unwrap());
    }

    #[test]
    fn test_bumped_patch() {
        let version = Version::parse("1.2.3.4.5-pre+build").unwrap();
        assert_eq!(version.bumped_patch(), Version::parse("1.2.4.0.0").unwrap());
    }

    #[test_case(0, "1.2.3.5.0")]
    #[test_case(1, "1.2.3.4.6")]
    #[test_case(2, "1.2.3.4.5")]
    fn test_bump_additional(index: usize, expected: &str) {
        let mut version = Version::parse("1.2.3.4.5-pre+build").unwrap();
        version.bump_additional(index);
        assert_eq!(version, Version::parse(expected).unwrap());
    }

    #[test_case(0, "1.2.3.5.0")]
    #[test_case(1, "1.2.3.4.6")]
    #[test_case(2, "1.2.3.4.5")]
    fn test_bumped_additional(index: usize, expected: &str) {
        let version = Version::parse("1.2.3.4.5-pre+build").unwrap();
        assert_eq!(
            version.bumped_additional(index),
            Version::parse(expected).unwrap()
        );
    }

    #[test_case("1")]
    #[test_case("1.2")]
    #[test_case("1.2.3")]
    #[test_case("1.2.3.4")]
    #[test_case("1.2.3.4.5")]
    #[test_case("1.2.3.4.5+build")]
    fn test_is_not_pre_release(input: &str) {
        assert!(!Version::parse(input).unwrap().is_pre_release());
    }

    #[test_case("1-2")]
    #[test_case("1-a")]
    #[test_case("1.2-3")]
    #[test_case("1.2-a")]
    #[test_case("1.2.3-4")]
    #[test_case("1.2.3-a")]
    #[test_case("1.2.3.4-5")]
    #[test_case("1.2.3.4-a")]
    #[test_case("1.2.3.4.5-pre")]
    fn test_is_pre_release(input: &str) {
        assert!(Version::parse(input).unwrap().is_pre_release());
    }

    #[test_case("1", "1.0.0")]
    #[test_case("1.2", "1.2.0")]
    #[test_case("1.2.3", "1.2.3")]
    #[test_case("1.2.3.4", "1.2.3.4")]
    #[test_case("1.2.3.4.5", "1.2.3.4.5")]
    #[test_case("1.2.3-pre", "1.2.3-pre")]
    #[test_case("1.2.3.pre2", "1.2.3-pre2")]
    #[test_case("1.2.3+build", "1.2.3+build")]
    #[test_case("1.2.3.4-pre-42+r-1337", "1.2.3.4-pre.42+r.1337")]
    fn test_to_string(v: &str, expected: &str) {
        assert_eq!(Version::parse(v).unwrap().to_string(), expected.to_string());
    }

    #[test]
    fn test_from_u64() {
        assert_eq!(Version::from(42), Version::new(42, 0, 0));
    }

    #[test]
    fn test_from_u64_u64() {
        assert_eq!(Version::from((42, 13)), Version::new(42, 13, 0));
    }

    #[test]
    fn test_from_u64_u64_u64() {
        assert_eq!(Version::from((42, 13, 37)), Version::new(42, 13, 37));
    }

    #[test]
    fn test_from_u64_1() {
        assert_eq!(Version::from([42]), Version::new(42, 0, 0));
    }

    #[test]
    fn test_from_u64_2() {
        assert_eq!(Version::from([42, 13]), Version::new(42, 13, 0));
    }

    #[test]
    fn test_from_u64_3() {
        assert_eq!(Version::from([42, 13, 37]), Version::new(42, 13, 37));
    }

    #[test]
    fn test_display() {
        let version = Version::parse("1.2.3.4.5-pre+build").unwrap();
        assert_eq!(
            format!("{:42}", version),
            "1.2.3.4.5-pre+build                       "
        );
        assert_eq!(
            format!("{:>42}", version),
            "                       1.2.3.4.5-pre+build"
        );
        assert_eq!(
            format!("{:^42}", version),
            "           1.2.3.4.5-pre+build            "
        );
        assert_eq!(
            format!("{:*<42}", version),
            "1.2.3.4.5-pre+build***********************"
        );
        assert_eq!(
            format!("{:*>42}", version),
            "***********************1.2.3.4.5-pre+build"
        );
        assert_eq!(
            format!("{:*^42}", version),
            "***********1.2.3.4.5-pre+build************"
        );
        assert_eq!(format!("{:.7}", version), "1.2.3.4");
    }

    #[test_case("1")]
    #[test_case("1.2")]
    #[test_case("1.2.3")]
    #[test_case("1.2.3.4")]
    #[test_case("1.2.3.4.5")]
    #[test_case("1.2.3-pre")]
    #[test_case("1.2.3+build")]
    #[test_case("1.2.3-pre+build")]
    fn test_eq(input: &str) {
        assert_eq!(Version::parse(input), Version::parse(input));
    }

    #[test_case("1", "1.0.0")]
    #[test_case("1.2", "1.2.0")]
    #[test_case("1.2.3+42", "1.2.3+1337")]
    #[test_case("1.2.3-pre", "1.2.3-pre+build")]
    fn test_eq2(v1: &str, v2: &str) {
        assert_eq!(Version::parse(v1), Version::parse(v2));
    }

    #[test_case("1", "2")]
    #[test_case("1.2", "1.3")]
    #[test_case("1.2.3", "1.2.4")]
    #[test_case("1.2.3-pre", "1.2.3")]
    #[test_case("1.2.3.4", "1.2.3")]
    #[test_case("1.2.3.4", "1.2.3.5")]
    #[test_case("1.2.3.4", "1.2.3.4.5")]
    #[test_case("1.2.3-pre", "1.2.3-pre2")]
    fn test_ne(v1: &str, v2: &str) {
        assert_ne!(Version::parse(v1), Version::parse(v2));
    }

    #[test_case("0.0.0", "0.0.1")]
    #[test_case("0.0.0", "0.1.0")]
    #[test_case("0.0.0", "1.0.0")]
    #[test_case("1.0.0", "1.0.1")]
    #[test_case("1.0.0", "1.1.0")]
    #[test_case("1.0.0", "2.0.0")]
    #[test_case("1.1.0", "1.1.1")]
    #[test_case("1.1.0", "1.2.0")]
    #[test_case("1.1.0", "2.0.0")]
    #[test_case("1.2.3", "1.2.3.4")]
    #[test_case("1.2.3.4", "1.2.3.5")]
    #[test_case("1.2.3.4", "1.2.3.4.5")]
    #[test_case("1.2.3-pre", "1.2.3")]
    #[test_case("1.2.3.4-pre", "1.2.3.4")]
    #[test_case("1.2.3.4.5-pre", "1.2.3.4.5")]
    #[test_case("1.2.3", "1.2.3.4-pre")]
    #[test_case("1.2.2", "1.2.3-pre")]
    #[test_case("1.2.0", "1.2.3-pre")]
    #[test_case("1.0.0", "1.2.3-pre")]
    #[test_case("0.4.2", "1.2.3-pre")]
    #[test_case("0.0.1", "1.2.3-pre")]
    #[test_case("1.2.3-42", "1.2.3-84")]
    #[test_case("1.2.3-42", "1.2.3-123")]
    #[test_case("1.2.3-42", "1.2.3-42foo")]
    #[test_case("1.2.3-42", "1.2.3-12foo")]
    #[test_case("1.2.3-42", "1.2.3-1foo")]
    #[test_case("1.2.3-42", "1.2.3-foo")]
    fn test_lt(v1: &str, v2: &str) {
        assert!(Version::parse(v1) < Version::parse(v2));
    }

    #[test_case("1.2.3", "1.2.3")]
    #[test_case("1.2.3.4", "1.2.3.4")]
    #[test_case("1.2.3.4.5", "1.2.3.4.5")]
    #[test_case("1.2.3", "1.2.3.0.0")]
    #[test_case("1.2.3.4", "1.2.3.4.0")]
    #[test_case("1.2.3-pre", "1.2.3-pre")]
    #[test_case("1.2.3+build", "1.2.3+build")]
    #[test_case("1.2.3+build2", "1.2.3+build3")]
    #[test_case("1.2.3+42", "1.2.3+84")]
    fn test_not_lt(v1: &str, v2: &str) {
        assert!(!(Version::parse(v1) < Version::parse(v2)));
    }

    #[test_case("0.0.0", "0.0.1")]
    #[test_case("0.0.1", "0.0.1")]
    #[test_case("0.0.0", "0.1.0")]
    #[test_case("0.1.0", "0.1.0")]
    #[test_case("0.0.0", "1.0.0")]
    #[test_case("1.0.0", "1.0.0")]
    #[test_case("1.2.3", "1.2.3.4")]
    #[test_case("1.2.3.4", "1.2.3.4")]
    #[test_case("1.2.3.4", "1.2.3.4.5")]
    #[test_case("1.2.3.4.5", "1.2.3.4.5")]
    #[test_case("1.2.3-pre", "1.2.3")]
    #[test_case("1.2.3", "1.2.3")]
    #[test_case("1.2.3+build", "1.2.3")]
    fn test_lte(v1: &str, v2: &str) {
        assert!(Version::parse(v1) <= Version::parse(v2));
    }

    #[test_case("0.0.1", "0.0.0")]
    #[test_case("0.1.0", "0.0.0")]
    #[test_case("1.0.0", "0.0.0")]
    #[test_case("1.0.1", "1.0.0")]
    #[test_case("1.1.0", "1.0.0")]
    #[test_case("2.0.0", "1.0.0")]
    #[test_case("1.1.1", "1.1.0")]
    #[test_case("1.2.0", "1.1.0")]
    #[test_case("2.0.0", "1.1.0")]
    #[test_case("1.2.3.4", "1.2.3")]
    #[test_case("1.2.3.5", "1.2.3.4")]
    #[test_case("1.2.3.4.5", "1.2.3.4")]
    #[test_case("1.2.3", "1.2.3-pre")]
    #[test_case("1.2.3.4", "1.2.3.4-pre")]
    #[test_case("1.2.3.4.5", "1.2.3.4.5-pre")]
    #[test_case("1.2.3.4-pre", "1.2.3")]
    #[test_case("1.2.3-pre", "1.2.2")]
    #[test_case("1.2.3-pre", "1.2.0")]
    #[test_case("1.2.3-pre", "1.0.0")]
    #[test_case("1.2.3-pre", "0.4.2")]
    #[test_case("1.2.3-pre", "0.0.1")]
    fn test_gt(v1: &str, v2: &str) {
        assert!(Version::parse(v1) > Version::parse(v2));
    }

    #[test_case("1.2.3", "1.2.3")]
    #[test_case("1.2.3.4", "1.2.3.4")]
    #[test_case("1.2.3.4.5", "1.2.3.4.5")]
    #[test_case("1.2.3-pre", "1.2.3-pre")]
    #[test_case("1.2.3+build", "1.2.3+build")]
    #[test_case("1.2.3+build3", "1.2.3+build2")]
    #[test_case("1.2.3+84", "1.2.3+42")]
    fn test_not_gt(v1: &str, v2: &str) {
        assert!(!(Version::parse(v1) > Version::parse(v2)));
    }

    #[test_case("0.0.1", "0.0.0")]
    #[test_case("0.0.1", "0.0.1")]
    #[test_case("0.1.0", "0.0.0")]
    #[test_case("0.1.0", "0.1.0")]
    #[test_case("1.0.0", "0.0.0")]
    #[test_case("1.0.0", "1.0.0")]
    #[test_case("1.2.3.4", "1.2.3")]
    #[test_case("1.2.3.4", "1.2.3.4")]
    #[test_case("1.2.3.4.5", "1.2.3.4")]
    #[test_case("1.2.3.4.5", "1.2.3.4.5")]
    #[test_case("1.2.3", "1.2.3-pre")]
    #[test_case("1.2.3", "1.2.3")]
    #[test_case("1.2.3", "1.2.3+build")]
    fn test_gte(v1: &str, v2: &str) {
        assert!(Version::parse(v1) >= Version::parse(v2));
    }

    #[test]
    fn test_order_per_spec_11_4() {
        let versions = [
            "1.0.0-alpha",
            "1.0.0-alpha.1",
            "1.0.0-alpha.beta",
            "1.0.0-beta",
            "1.0.0-beta.2",
            "1.0.0-beta.11",
            "1.0.0-rc.1",
            "1.0.0",
        ]
        .iter()
        .map(|v| Version::parse(v))
        .collect::<Result<Vec<_>, _>>()
        .unwrap();

        let left = versions.iter();
        let right = versions.iter().skip(1);

        for (left, right) in left.zip(right) {
            assert!(left < right, "{} < {} was violated", left, right);
        }
    }

    #[cfg(feature = "serde")]
    #[cfg_attr(feature = "serde", test)]
    fn test_ser() {
        let v = Version::new(1, 2, 3);
        assert_eq!(r#""1.2.3""#, serde_json::to_string(&v).unwrap());
    }

    #[cfg(feature = "serde")]
    #[cfg_attr(feature = "serde", test)]
    fn test_deser() {
        let v = r#""1.2.3""#;
        assert_eq!(Version::new(1, 2, 3), serde_json::from_str(v).unwrap());
    }

    #[cfg(feature = "semver")]
    #[cfg_attr(feature = "semver", test)]
    fn test_into_semver() {
        let v = Version::new(1, 2, 3);
        assert_eq!(semver::Version::new(1, 2, 3), semver::Version::from(v));
    }

    #[cfg(feature = "semver10")]
    #[cfg_attr(feature = "semver10", test)]
    fn test_into_semver10() {
        let v = Version::new(1, 2, 3);
        assert_eq!(semver10::Version::new(1, 2, 3), semver10::Version::from(v));
    }
}
