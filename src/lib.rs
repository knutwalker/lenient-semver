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
//! let version = lenient_semver::parse::<Version>("1.2.3");
//! assert_eq!(version, Ok(Version::new(1, 2, 3)));
//!
//! // examples of a version that would not be accepted by semver_parser
//! assert_eq!(
//!     lenient_semver::parse::<Version>("1.2.M1").unwrap(),
//!     Version::parse("1.2.0-M1").unwrap()
//! );
//! assert!(Version::parse("1.2.M1").is_err());
//!
//! assert_eq!(
//!     lenient_semver::parse::<Version>("1").unwrap(),
//!     Version::parse("1.0.0").unwrap()
//! );
//! assert!(Version::parse("1").is_err());
//!
//! assert_eq!(
//!     lenient_semver::parse::<Version>("1.2.3.Final").unwrap(),
//!     Version::parse("1.2.3+Final").unwrap()
//! );
//! assert!(Version::parse("1.2.3.Final").is_err());
//!
//! assert_eq!(
//!     lenient_semver::parse::<Version>("1.2.3.4.5").unwrap(),
//!     Version::parse("1.2.3+4.5").unwrap()
//! );
//! assert!(Version::parse("1.2.3.4.5").is_err());
//!
//! assert_eq!(
//!     lenient_semver::parse::<Version>("v1.2.3").unwrap(),
//!     Version::parse("1.2.3").unwrap()
//! );
//! assert!(Version::parse("v1.2.3").is_err());
//! ```

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

use std::{fmt::Display, ops::Range};

/// Parse a string slice into a Version.
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
/// use semver::Version;
///
/// let version = lenient_semver::parse::<Version>("1.2.3");
/// assert_eq!(version, Ok(Version::new(1, 2, 3)));
///
/// // examples of a version that would not be accepted by semver_parser
/// assert_eq!(
///     lenient_semver::parse::<Version>("1.2.M1").unwrap(),
///     Version::parse("1.2.0-M1").unwrap()
/// );
/// assert!(Version::parse("1.2.M1").is_err());
///
/// assert_eq!(
///     lenient_semver::parse::<Version>("1").unwrap(),
///     Version::parse("1.0.0").unwrap()
/// );
/// assert!(Version::parse("1").is_err());
///
/// assert_eq!(
///     lenient_semver::parse::<Version>("1.2.3.Final").unwrap(),
///     Version::parse("1.2.3+Final").unwrap()
/// );
/// assert!(Version::parse("1.2.3.Final").is_err());
///
/// assert_eq!(
///     lenient_semver::parse::<Version>("1.2.3.4.5").unwrap(),
///     Version::parse("1.2.3+4.5").unwrap()
/// );
/// assert!(Version::parse("1.2.3.4.5").is_err());
///
/// assert_eq!(
///     lenient_semver::parse::<Version>("v1.2.3").unwrap(),
///     Version::parse("1.2.3").unwrap()
/// );
/// assert!(Version::parse("v1.2.3").is_err());
/// ```
pub fn parse<'input, V>(input: &'input str) -> Result<V::Out, Error<'input>>
where
    V: VersionBuilder<'input>,
{
    parse_version::<_, V>(input, lex(input)).map_err(|ErrorSpan { error, span }| Error {
        input,
        span,
        error,
    })
}

/// Trait to abstract over version building.
///
/// The methods to implement in this trait represent the components of [`semver::Version`],
/// but allow for parsing into a custom type.
///
/// The trait is generic over the lifetime of the input string, so that one could
/// parse into a version without having to allocate.
pub trait VersionBuilder<'input> {
    /// The return type of the final version.
    type Out;

    /// Construct a new version builder.
    ///
    /// The function must not fail and the version (if returned from [`VersionBuilder::build`] at this point)
    /// should represent something akin to "0.0.0"
    fn new() -> Self;

    /// Set the major version component.
    ///
    /// This method is the only required component and will be called
    /// before [`VersionBuilder::build`].
    fn set_major(&mut self, major: u64);

    /// Set the minor version component.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    fn set_minor(&mut self, minor: u64);

    /// Set the patch version component.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    fn set_patch(&mut self, patch: u64);

    /// Add additional numeric components following patch and preceding pre-release.
    ///
    /// For a version like `1.2.3.4.5`, this would call add_additional with `4` and `5`.
    ///
    /// For strict semver versions, those values are invalid.
    /// For lenient semver, those values are better represented as build than pre-release,
    /// although they might be "in the same block" as pre-release.
    /// In terms of comparing versions, the values added here should still have an impact.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    fn add_additional(&mut self, num: u64);

    /// Add a pre-release identifier.
    ///
    /// The string might represent any alpha-numeric identifier,
    /// including numbers with or without leading zeroes.
    /// It is up to the implementor to parse those into more specific
    /// identifiers, if required.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    ///
    /// This method might be called multiple times.
    fn add_pre_release(&mut self, pre_release: &'input str);

    /// Add a build identifier.
    ///
    /// The string might represent any alpha-numeric identifier,
    /// including numbers with or without leading zeroes.
    /// It is up to the implementor to parse those into more specific
    /// identifiers, if required.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    ///
    /// This method might be called multiple times.
    fn add_build(&mut self, build: &'input str);

    /// Construct the final version.
    fn build(self) -> Self::Out;
}

#[cfg(any(
    test,
    feature = "semver",
    feature = "semver10",
    feature = "version_lite"
))]
fn try_num(s: &str) -> Result<u64, &str> {
    match s.parse::<u64>() {
        Ok(num) if !s.starts_with("0") || s == "0" => Ok(num),
        _ => Err(s),
    }
}

#[cfg(feature = "semver")]
fn try_num_semver(s: &str) -> semver::Identifier {
    try_num(s).map_err(String::from).map_or_else(
        semver::Identifier::AlphaNumeric,
        semver::Identifier::Numeric,
    )
}

#[cfg(feature = "semver10")]
fn try_num_semver10(s: &str) -> semver10::Identifier {
    try_num(s).map_err(String::from).map_or_else(
        semver10::Identifier::AlphaNumeric,
        semver10::Identifier::Numeric,
    )
}

#[cfg(feature = "semver")]
impl<'input> VersionBuilder<'input> for semver::Version {
    type Out = Self;

    fn new() -> Self {
        semver::Version::new(0, 0, 0)
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
        self.build.push(semver::Identifier::Numeric(num))
    }

    fn add_pre_release(&mut self, pre_release: &'input str) {
        self.pre.push(try_num_semver(pre_release))
    }

    fn add_build(&mut self, build: &'input str) {
        self.build.push(try_num_semver(build))
    }

    fn build(self) -> Self::Out {
        self
    }
}

#[cfg(feature = "semver10")]
impl<'input> VersionBuilder<'input> for semver10::Version {
    type Out = Self;

    fn new() -> Self {
        semver10::Version::new(0, 0, 0)
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
        self.build.push(semver10::Identifier::Numeric(num))
    }

    fn add_pre_release(&mut self, pre_release: &'input str) {
        self.pre.push(try_num_semver10(pre_release))
    }

    fn add_build(&mut self, build: &'input str) {
        self.build.push(try_num_semver10(build))
    }

    fn build(self) -> Self::Out {
        self
    }
}

#[cfg(any(test, feature = "version_lite"))]
/// Represents a version number.
///
/// This is a lightweight clone of `semver::Version`.
/// Without any of the bells and whistles of that type.
///
/// The version is bound to the lifetime of the input string.
///
/// # Correctness Warning
///
/// This version implements [`PartialOrd`] and [`PartialEq`] by deriving them,
/// which results in implementations that do not conform to the
/// semantic version spec.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct VersionLite<'input> {
    /// The major version.
    pub major: u64,
    /// The minor version.
    pub minor: u64,
    /// The patch version.
    pub patch: u64,
    /// The pre-release metadata.
    pub pre: Vec<IdentifierLite<'input>>,
    /// The build metadata.
    pub build: Vec<IdentifierLite<'input>>,
}

#[cfg(any(test, feature = "version_lite"))]
/// An identifier in the pre-release or build metadata.
///
/// This is clone of `semver::Identifier` while not requiring a String allocation.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum IdentifierLite<'input> {
    /// An identifier that's solely numbers.
    Numeric(u64),
    /// An identifier with letters and numbers.
    AlphaNumeric(&'input str),
}

#[cfg(any(test, feature = "version_lite"))]
impl Default for VersionLite<'_> {
    fn default() -> Self {
        VersionLite {
            major: 0,
            minor: 0,
            patch: 0,
            pre: Vec::new(),
            build: Vec::new(),
        }
    }
}

#[cfg(any(test, feature = "version_lite"))]
impl<'input> VersionBuilder<'input> for VersionLite<'input> {
    type Out = Self;

    fn new() -> Self {
        VersionLite::default()
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
        self.build.push(IdentifierLite::Numeric(num))
    }

    fn add_pre_release(&mut self, pre_release: &'input str) {
        self.pre.push(
            try_num(pre_release).map_or_else(IdentifierLite::AlphaNumeric, IdentifierLite::Numeric),
        )
    }

    fn add_build(&mut self, build: &'input str) {
        self.build
            .push(try_num(build).map_or_else(IdentifierLite::AlphaNumeric, IdentifierLite::Numeric))
    }

    fn build(self) -> Self::Out {
        self
    }
}

#[cfg(all(feature = "semver", feature = "version_lite"))]
impl From<VersionLite<'_>> for semver::Version {
    fn from(v: VersionLite<'_>) -> Self {
        semver::Version {
            major: v.major,
            minor: v.minor,
            patch: v.patch,
            pre: v.pre.into_iter().map(From::from).collect(),
            build: v.build.into_iter().map(From::from).collect(),
        }
    }
}

#[cfg(all(feature = "semver", feature = "version_lite"))]
impl From<IdentifierLite<'_>> for semver::Identifier {
    fn from(id: IdentifierLite<'_>) -> Self {
        match id {
            IdentifierLite::Numeric(v) => semver::Identifier::Numeric(v),
            IdentifierLite::AlphaNumeric(v) => semver::Identifier::AlphaNumeric(v.into()),
        }
    }
}

#[cfg(all(feature = "semver10", feature = "version_lite"))]
impl From<VersionLite<'_>> for semver10::Version {
    fn from(v: VersionLite<'_>) -> Self {
        semver10::Version {
            major: v.major,
            minor: v.minor,
            patch: v.patch,
            pre: v.pre.into_iter().map(From::from).collect(),
            build: v.build.into_iter().map(From::from).collect(),
        }
    }
}

#[cfg(all(feature = "semver10", feature = "version_lite"))]
impl From<IdentifierLite<'_>> for semver10::Identifier {
    fn from(id: IdentifierLite<'_>) -> Self {
        match id {
            IdentifierLite::Numeric(v) => semver10::Identifier::Numeric(v),
            IdentifierLite::AlphaNumeric(v) => semver10::Identifier::AlphaNumeric(v.into()),
        }
    }
}

/// Possible errors that happen during parsing
/// and the location of the token where the error occurred.
///
/// # Example
///
/// ```rust
/// use semver::Version;
///
/// let error = lenient_semver::parse::<Version>("1+").unwrap_err();
/// assert_eq!(error.to_string(), "Could not parse the build identifier: No input");
///
/// let error = lenient_semver::parse::<Version>("1!").unwrap_err();
/// assert_eq!(error.to_string(), "Unexpected `!`");
/// ```
#[derive(Debug, PartialEq, Eq)]
pub struct Error<'input> {
    input: &'input str,
    span: Span,
    error: ErrorType,
}

impl<'input> Error<'input> {
    /// Creates a new [`OwnedError`] out of this [`Error`].
    ///
    /// This is specialized version of [`Clone`] which returns a different type.
    #[inline]
    pub fn owned(&self) -> OwnedError {
        OwnedError {
            input: self.input.into(),
            span: self.span,
            error: self.error,
        }
    }

    /// Returns the original input line.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let error = lenient_semver::parse::<semver::Version>("1+").unwrap_err();
    /// assert_eq!(error.input(), "1+");
    /// ```
    #[inline]
    pub fn input(&self) -> &'input str {
        self.input
    }

    /// Returns range into the input string that points to the erroneous input.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let error = lenient_semver::parse::<semver::Version>("1+").unwrap_err();
    /// assert_eq!(error.error_span(), 1..2);
    /// ```
    #[inline]
    pub fn error_span(&self) -> Range<usize> {
        self.span.into()
    }

    /// Returns the kind of error.
    ///
    /// # Examples
    ///
    /// ```rust
    /// assert_eq!(
    ///     lenient_semver::parse::<semver::Version>("").unwrap_err().error_kind(),
    ///     lenient_semver::ErrorKind::MissingMajorNumber
    /// );
    /// assert_eq!(
    ///     lenient_semver::parse::<semver::Version>("1.").unwrap_err().error_kind(),
    ///     lenient_semver::ErrorKind::MissingMinorNumber
    /// );
    /// assert_eq!(
    ///     lenient_semver::parse::<semver::Version>("1.2.").unwrap_err().error_kind(),
    ///     lenient_semver::ErrorKind::MissingPatchNumber
    /// );
    /// assert_eq!(
    ///     lenient_semver::parse::<semver::Version>("1-").unwrap_err().error_kind(),
    ///     lenient_semver::ErrorKind::MissingPreRelease
    /// );
    /// assert_eq!(
    ///     lenient_semver::parse::<semver::Version>("1+").unwrap_err().error_kind(),
    ///     lenient_semver::ErrorKind::MissingBuild
    /// );
    /// assert_eq!(
    ///     lenient_semver::parse::<semver::Version>("1!").unwrap_err().error_kind(),
    ///     lenient_semver::ErrorKind::UnexpectedInput
    /// );
    /// ```
    #[inline]
    pub fn error_kind(&self) -> ErrorKind {
        match self.error {
            ErrorType::Missing(segment) => match segment {
                Segment::Part(part) => match part {
                    Part::Major => ErrorKind::MissingMajorNumber,
                    Part::Minor => ErrorKind::MissingMinorNumber,
                    Part::Patch => ErrorKind::MissingPatchNumber,
                },
                Segment::PreRelease => ErrorKind::MissingPreRelease,
                Segment::Build => ErrorKind::MissingBuild,
            },
            ErrorType::NotANumber(part) => match part {
                Part::Major => ErrorKind::MajorNotANumber,
                Part::Minor => ErrorKind::MinorNotANumber,
                Part::Patch => ErrorKind::PatchNotANumber,
            },
            ErrorType::Unexpected => ErrorKind::UnexpectedInput,
        }
    }

    /// Returns a slice from the original input line that triggered the error.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let error = lenient_semver::parse::<semver::Version>("1+").unwrap_err();
    /// assert_eq!(error.erroneous_input(), "+");
    /// ```
    #[inline]
    pub fn erroneous_input(&self) -> &'input str {
        &self.input[self.error_span()]
    }

    /// Returns a text representation of the error.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let error = lenient_semver::parse::<semver::Version>("1.").unwrap_err();
    /// assert_eq!(error.error_line(), String::from("Could not parse the minor identifier: No input"));
    /// ```
    ///
    /// This is equivalent to the [`Display`] implementation, which can be further customized with format specifiers.
    ///
    /// ```rust
    /// let error = lenient_semver::parse::<semver::Version>("1?").unwrap_err();
    /// assert_eq!(format!("{:!^42}", error), String::from("!!!!!!!!!!!!!!Unexpected `?`!!!!!!!!!!!!!!"));
    /// ```
    pub fn error_line(&self) -> String {
        match &self.error {
            ErrorType::Missing(segment) => {
                format!("Could not parse the {} identifier: No input", segment)
            }
            ErrorType::NotANumber(part) => format!(
                "Could not parse the {} identifier: `{}` is not a number",
                part,
                self.erroneous_input()
            ),
            ErrorType::Unexpected => format!("Unexpected `{}`", self.erroneous_input()),
        }
    }

    /// Returns a caret line indication the erroneous input if it was written under the original input line.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let error = lenient_semver::parse::<semver::Version>("foo").unwrap_err();
    /// assert_eq!(error.indicate_erroneous_input(), "^^^");
    ///
    /// let error = lenient_semver::parse::<semver::Version>("1.2.3 bar").unwrap_err();
    /// assert_eq!(error.indicate_erroneous_input(), "~~~~~~^^^");
    /// ```
    pub fn indicate_erroneous_input(&self) -> String {
        format!(
            "{0:~<start$}{0:^<width$}",
            "",
            start = self.span.start as usize,
            width = (self.span.end - self.span.start) as usize
        )
    }
}

/// Owned version of [`Error`] which clones the input string.
#[derive(Debug, PartialEq, Eq)]
pub struct OwnedError {
    input: String,
    span: Span,
    error: ErrorType,
}

impl OwnedError {
    /// Return a borrowed version of this error.
    pub fn borrowed(&self) -> Error<'_> {
        Error {
            input: &self.input,
            span: self.span,
            error: self.error,
        }
    }

    /// See [`Error::input`].
    #[inline]
    pub fn input(&self) -> &str {
        self.borrowed().input()
    }

    /// See [`Error::error_span`].
    #[inline]
    pub fn error_span(&self) -> Range<usize> {
        self.borrowed().error_span()
    }

    /// See [`Error::error_kind`].
    #[inline]
    pub fn error_kind(&self) -> ErrorKind {
        self.borrowed().error_kind()
    }

    /// See [`Error::erroneous_input`].
    #[inline]
    pub fn erroneous_input(&self) -> &str {
        self.borrowed().erroneous_input()
    }

    /// See [`Error::error_line`].
    #[inline]
    pub fn error_line(&self) -> String {
        self.borrowed().error_line()
    }

    /// See [`Error::indicate_erroneous_input`].
    #[inline]
    pub fn indicate_erroneous_input(&self) -> String {
        self.borrowed().indicate_erroneous_input()
    }
}

/// Possible errors that can happen.
/// These don't include an information as those are covered by various
/// error methods like [`Error::erroneous_input`].
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ErrorKind {
    /// Expected to parse the major number part, but nothing was found
    MissingMajorNumber,
    /// Expected to parse the minor number part, but nothing was found
    MissingMinorNumber,
    /// Expected to parse the patch number part, but nothing was found
    MissingPatchNumber,
    /// Expected to parse the pre-release identifier part, but nothing was found
    MissingPreRelease,
    /// Expected to parse the build identifier part, but nothing was found
    MissingBuild,
    /// Trying to parse the major number part, but the input was not a number
    MajorNotANumber,
    /// Trying to parse the minor number part, but the input was not a number
    MinorNotANumber,
    /// Trying to parse the patch number part, but the input was not a number
    PatchNotANumber,
    /// Found an unexpected input
    UnexpectedInput,
}

impl Display for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.pad(&self.error_line())?;
        if f.alternate() {
            writeln!(f)?;
            writeln!(f, "|    {}", self.input)?;
            writeln!(f, "|    {}", self.indicate_erroneous_input())?;
        }
        Ok(())
    }
}

impl Display for OwnedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.borrowed().fmt(f)
    }
}

impl std::error::Error for Error<'_> {}

impl std::error::Error for OwnedError {}

#[derive(Debug, PartialEq, Eq)]
struct ErrorSpan {
    error: ErrorType,
    span: Span,
}

impl ErrorSpan {
    fn new(error: ErrorType, span: Span) -> Self {
        Self { error, span }
    }

    fn missing_part(part: Part, span: Span) -> Self {
        Self {
            error: ErrorType::Missing(Segment::Part(part)),
            span,
        }
    }

    fn missing_pre(span: Span) -> Self {
        Self {
            error: ErrorType::Missing(Segment::PreRelease),
            span,
        }
    }

    fn missing_build(span: Span) -> Self {
        Self {
            error: ErrorType::Missing(Segment::Build),
            span,
        }
    }

    fn unexpected(span: Span) -> Self {
        Self {
            error: ErrorType::Unexpected,
            span,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum ErrorType {
    Missing(Segment),
    NotANumber(Part),
    Unexpected,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Part {
    Major,
    Minor,
    Patch,
}

impl Display for Part {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Part::Major => f.pad("major"),
            Part::Minor => f.pad("minor"),
            Part::Patch => f.pad("patch"),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Segment {
    Part(Part),
    PreRelease,
    Build,
}

impl Display for Segment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Segment::Part(part) => part.fmt(f),
            Segment::PreRelease => f.pad("pre-release"),
            Segment::Build => f.pad("build"),
        }
    }
}

#[derive(Debug, Copy, Clone)]
enum State {
    Part(Part),
    PreRelease,
    Build,
}

fn parse_version<'input, I, V>(input: &'input str, tokens: I) -> Result<V::Out, ErrorSpan>
where
    I: IntoIterator<Item = TokenSpan>,
    V: VersionBuilder<'input>,
{
    let mut tokens = tokens.into_iter();
    let mut version = V::new();
    let mut state = State::Part(Part::Major);
    let mut potential_dot4 = false;

    let mut token_span = match tokens.next() {
        Some(token) => token,
        None => {
            return match state {
                State::Part(Part::Major) => {
                    Err(ErrorSpan::missing_part(Part::Major, Span::default()))
                }
                State::Part(part) => Err(ErrorSpan::missing_part(part, Span::default())),
                State::PreRelease => Err(ErrorSpan::missing_pre(Span::default())),
                State::Build => Err(ErrorSpan::missing_build(Span::default())),
            }
        }
    };

    loop {
        match state {
            State::Part(Part::Major) => match token_span.token {
                // skip initial whitespace
                Token::Whitespace => {}
                _ => {
                    version.set_major(parse_number(token_span, input, Part::Major)?);
                    token_span = match tokens.next() {
                        None => return finish(version),
                        Some(token_span) => token_span,
                    };
                    state = match token_span.token {
                        Token::Dot => State::Part(Part::Minor),
                        Token::Hyphen => State::PreRelease,
                        Token::Plus => State::Build,
                        _ => return finish_token_and_tokens(token_span, tokens, version),
                    };
                }
            },
            State::Part(part) => match token_span.token {
                Token::Alpha => {
                    let v = token_span.span.at(input);
                    // things like 1.Final, early stop with a single build identifier
                    if is_release_identifier(v) {
                        version.add_build(v);
                        return finish_tokens(tokens, version);
                    }
                    // any alpha token skips right into pre-release parsing
                    // tokens = tokens.stash(Token::Alpha);
                    state = State::PreRelease;
                    continue;
                }
                // unexpected end
                Token::Whitespace => return Err(ErrorSpan::missing_part(part, token_span.span)),
                // any other token is tried as a number
                _ => {
                    let num = parse_number(token_span, input, part)?;
                    match part {
                        Part::Major => unreachable!(),
                        Part::Minor => version.set_minor(num),
                        Part::Patch => version.set_patch(num),
                    }
                    token_span = match tokens.next() {
                        None => return finish(version),
                        Some(token_span) => token_span,
                    };
                    state = match token_span.token {
                        Token::Dot => match part {
                            Part::Major => unreachable!(),
                            Part::Minor => State::Part(Part::Patch),
                            Part::Patch => {
                                potential_dot4 = true;
                                State::PreRelease
                            }
                        },
                        Token::Hyphen => State::PreRelease,
                        Token::Plus => State::Build,
                        _ => return finish_token_and_tokens(token_span, tokens, version),
                    };
                }
            },
            State::PreRelease => {
                match token_span.token {
                    Token::Alpha => {
                        let v = token_span.span.at(input);
                        // things like 1.Final, early stop with a single build identifier
                        if is_release_identifier(v) {
                            version.add_build(v);
                            return finish_tokens(tokens, version);
                        }
                        // regular pre-release part
                        version.add_pre_release(v);
                    }
                    // leading zero numbers in pre-release are alphanum
                    Token::ZeroNumeric => {
                        version.add_pre_release(token_span.span.at(input));
                    }
                    // regular pre-release part
                    Token::Numeric => {
                        if potential_dot4 {
                            // tokens = tokens.stash(Token::Numeric);
                            state = State::Build;
                            continue;
                        }
                        version.add_pre_release(token_span.span.at(input));
                    }
                    // unexpected end
                    Token::Whitespace => return Err(ErrorSpan::missing_pre(token_span.span)),
                    // any other token is invalid
                    _ => {
                        return Err(ErrorSpan::unexpected(token_span.span));
                    }
                }
                potential_dot4 = false;
                token_span = match tokens.next() {
                    None => return finish(version),
                    Some(token_span) => token_span,
                };
                state = match token_span.token {
                    Token::Dot => State::PreRelease,
                    Token::Hyphen => State::PreRelease,
                    Token::Plus => State::Build,
                    _ => return finish_token_and_tokens(token_span, tokens, version),
                };
            }
            State::Build => {
                // inline last state as we never change it
                loop {
                    let v = token_span.span.at(input);
                    match token_span.token {
                        // regular build part
                        Token::Alpha => version.add_build(v),
                        // leading zero numbers in build are alphanum
                        Token::ZeroNumeric => version.add_build(v),
                        // regular build part
                        Token::Numeric => version.add_build(v),
                        // unexpected end
                        Token::Whitespace => {
                            return Err(ErrorSpan::missing_build(token_span.span));
                        }
                        // any other token is invalid
                        _ => {
                            return Err(ErrorSpan::unexpected(token_span.span));
                        }
                    }

                    token_span = match tokens.next() {
                        None => return finish(version),
                        Some(token_span) => token_span,
                    };
                    match token_span.token {
                        Token::Dot | Token::Hyphen => {} // try next build token,
                        _ => return finish_token_and_tokens(token_span, tokens, version),
                    };
                    token_span = match tokens.next() {
                        Some(token) => token,
                        None => return Err(ErrorSpan::missing_build(token_span.span)),
                    };
                }
            }
        }

        token_span = match tokens.next() {
            Some(token) => token,
            None => {
                return match state {
                    State::Part(Part::Major) => {
                        Err(ErrorSpan::missing_part(Part::Major, token_span.span))
                    }
                    State::Part(part) => Err(ErrorSpan::missing_part(part, token_span.span)),
                    State::PreRelease => Err(ErrorSpan::missing_pre(token_span.span)),
                    State::Build => Err(ErrorSpan::missing_build(token_span.span)),
                }
            }
        };
    }
}

fn parse_number(token: TokenSpan, input: &str, part: Part) -> Result<u64, ErrorSpan> {
    parse_number_inner(token, input, part).map_err(|e| ErrorSpan::new(e, token.span))
}

fn parse_number_inner(token: TokenSpan, input: &str, part: Part) -> Result<u64, ErrorType> {
    token
        .num(part == Part::Major, input)
        .ok_or_else(|| ErrorType::NotANumber(part))
}

fn finish_tokens<'input, I, V>(tokens: I, value: V) -> Result<V::Out, ErrorSpan>
where
    I: Iterator<Item = TokenSpan>,
    V: VersionBuilder<'input>,
{
    for token in tokens {
        finish_token(token)?;
    }
    finish(value)
}

fn finish_token_and_tokens<'input, I, V>(
    token: TokenSpan,
    tokens: I,
    value: V,
) -> Result<V::Out, ErrorSpan>
where
    I: Iterator<Item = TokenSpan>,
    V: VersionBuilder<'input>,
{
    finish_token(token)?;
    finish_tokens(tokens, value)
}

fn finish_token(token: TokenSpan) -> Result<(), ErrorSpan> {
    match token.token {
        Token::Whitespace => Ok(()),
        _ => Err(ErrorSpan::unexpected(token.span)),
    }
}

#[inline]
fn finish<'input, V>(value: V) -> Result<V::Out, ErrorSpan>
where
    V: VersionBuilder<'input>,
{
    Ok(value.build())
}

fn is_release_identifier(v: &str) -> bool {
    eq_bytes_ignore_case(v, "final") || eq_bytes_ignore_case(v, "release")
}

fn eq_bytes_ignore_case(left: &str, right: &str) -> bool {
    if left.len() != right.len() {
        return false;
    }
    left.bytes()
        .map(|c| c.to_ascii_lowercase())
        .zip(right.bytes())
        .all(|(c1, c2)| c1 == c2)
}

fn lex(input: &str) -> Lexer<'_> {
    Lexer::new(input)
}

#[derive(Debug)]
struct Lexer<'input> {
    input: &'input str,
    end: usize,
    chars: std::str::CharIndices<'input>,
    peeked: Option<(usize, char)>,
}

impl<'input> Lexer<'input> {
    fn new(input: &'input str) -> Lexer<'input> {
        let mut chars = input.char_indices();
        // let span = Span::new(0, input.len());
        let peeked = chars.next();
        Lexer {
            input,
            end: input.len(),
            chars,
            peeked,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Token {
    /// Any unicode whitespace
    Whitespace,
    /// numeric component
    Numeric,
    /// numeric component that begins with a leading zero
    ZeroNumeric,
    /// numeric component that begins with a leading v
    VNumeric,
    /// alphanumeric component
    Alpha,
    /// `.`
    Dot,
    /// `+`
    Plus,
    /// `-`
    Hyphen,
    /// Error cases
    UnexpectedChar,
    InputTooLarge,
}

impl<'input> Iterator for Lexer<'input> {
    type Item = TokenSpan;

    fn next(&mut self) -> Option<Self::Item> {
        let (start, c) = self.peeked.take()?;

        let (end, token) = match c {
            ' ' | '\t' | '\n' | '\x0C' | '\r' => {
                let end = match self.chars.find(|(_, c)| !c.is_ascii_whitespace()) {
                    Some((j, c)) => {
                        self.peeked = Some((j, c));
                        j
                    }
                    None => self.end,
                };
                (end, Token::Whitespace)
            }
            '0'..='9' => {
                let (end, is_alpha) = match self.chars.find(|(_, c)| !c.is_ascii_digit()) {
                    Some((j, c)) => {
                        if c.is_ascii_alphabetic() {
                            match self.chars.find(|(_, c)| !c.is_ascii_alphanumeric()) {
                                Some((j, c)) => {
                                    self.peeked = Some((j, c));
                                    (j, true)
                                }
                                None => (self.end, true),
                            }
                        } else {
                            self.peeked = Some((j, c));
                            (j, false)
                        }
                    }
                    None => (self.end, false),
                };
                let token = if is_alpha {
                    Token::Alpha
                } else if c == '0' && end - start > 1 {
                    Token::ZeroNumeric
                } else {
                    Token::Numeric
                };
                (end, token)
            }
            'v' | 'V' => {
                let (end, is_alpha) = match self.chars.find(|(_, c)| !c.is_ascii_digit()) {
                    Some((j, c)) => {
                        if c.is_ascii_alphabetic() {
                            match self.chars.find(|(_, c)| !c.is_ascii_alphanumeric()) {
                                Some((j, c)) => {
                                    self.peeked = Some((j, c));
                                    (j, true)
                                }
                                None => (self.end, true),
                            }
                        } else {
                            self.peeked = Some((j, c));
                            (j, j - start == 1)
                        }
                    }
                    None => (self.end, false),
                };
                // self.span = Span::new(start, end);
                let token = if is_alpha {
                    Token::Alpha
                } else {
                    Token::VNumeric
                };
                (end, token)
            }
            'A'..='Z' | 'a'..='z' => {
                let end = match self.chars.find(|(_, c)| !c.is_ascii_alphanumeric()) {
                    Some((j, c)) => {
                        self.peeked = Some((j, c));
                        j
                    }
                    None => self.end,
                };
                (end, Token::Alpha)
            }
            '.' => (start + 1, Token::Dot),
            '-' => (start + 1, Token::Hyphen),
            '+' => (start + 1, Token::Plus),
            _ => (start + 1, Token::UnexpectedChar),
        };

        if self.peeked.is_none() {
            self.peeked = self.chars.next();
        }
        Some(if end <= u8::max_value() as usize {
            TokenSpan::new(token, start as u8, end as u8)
        } else if start <= u8::max_value() as usize {
            TokenSpan::new(Token::InputTooLarge, start as u8, u8::max_value())
        } else {
            TokenSpan::new(Token::InputTooLarge, u8::max_value(), u8::max_value())
        })
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct TokenSpan {
    token: Token,
    span: Span,
}

impl TokenSpan {
    fn new(token: Token, start: u8, end: u8) -> Self {
        Self {
            token,
            span: Span::new(start, end),
        }
    }

    fn num(&self, allow_vnum: bool, input: &str) -> Option<u64> {
        match self.token {
            Token::Numeric => self.span.at(input).parse::<u64>().ok(),
            Token::ZeroNumeric => self.span.at(input).parse::<u64>().ok(),
            Token::VNumeric if allow_vnum => self.span.at1(input).parse::<u64>().ok(),
            _ => None,
        }
    }
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq)]
struct Span {
    start: u8,
    end: u8,
}

impl Span {
    fn new(start: u8, end: u8) -> Self {
        Self { start, end }
    }

    fn at<'input>(&self, input: &'input str) -> &'input str {
        &input[self.start as usize..self.end as usize]
    }

    fn at1<'input>(&self, input: &'input str) -> &'input str {
        &input[(self.start + 1) as usize..self.end as usize]
    }
}

impl From<Span> for Range<usize> {
    fn from(s: Span) -> Self {
        s.start as usize..s.end as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_case::test_case;

    #[cfg(feature = "semver")]
    mod semver_helpers {
        pub(super) use semver::{Identifier, Version as SemVer};
        pub(super) type Version<'input> = SemVer;

        pub(super) trait IntoIdentifier {
            fn into_itentifier(self) -> Identifier;
        }

        impl IntoIdentifier for &str {
            fn into_itentifier(self) -> Identifier {
                Identifier::AlphaNumeric(self.into())
            }
        }

        impl IntoIdentifier for u64 {
            fn into_itentifier(self) -> Identifier {
                Identifier::Numeric(self)
            }
        }
    }

    #[cfg(all(not(feature = "semver"), feature = "semver10"))]
    mod semver_helpers {
        pub(super) use semver10::{Identifier, Version as SemVer};
        pub(super) type Version<'input> = SemVer;

        pub(super) trait IntoIdentifier {
            fn into_itentifier(self) -> Identifier;
        }

        impl IntoIdentifier for &str {
            fn into_itentifier(self) -> Identifier {
                Identifier::AlphaNumeric(self.into())
            }
        }

        impl IntoIdentifier for u64 {
            fn into_itentifier(self) -> Identifier {
                Identifier::Numeric(self)
            }
        }
    }

    #[cfg(all(not(feature = "semver"), not(feature = "semver10")))]
    mod semver_helpers {
        pub(super) use super::{IdentifierLite as Identifier, VersionLite};
        pub(super) type Version<'input> = VersionLite<'input>;

        pub(super) trait IntoIdentifier<'input> {
            fn into_itentifier(self) -> Identifier<'input>;
        }

        impl<'input> IntoIdentifier<'input> for &'input str {
            fn into_itentifier(self) -> Identifier<'input> {
                Identifier::AlphaNumeric(self)
            }
        }

        impl<'input> IntoIdentifier<'input> for u64 {
            fn into_itentifier(self) -> Identifier<'input> {
                Identifier::Numeric(self)
            }
        }
    }

    use semver_helpers::*;

    macro_rules! vers {
        ($major:literal . $minor:literal . $patch:literal) => {
            Version {
                major: $major,
                minor: $minor,
                patch: $patch,
                pre: Vec::new(),
                build: Vec::new(),
            }
        };

        ($major:literal . $minor:literal . $patch:literal - $( $pre:literal )-+ ) => {
            Version {
                major: $major,
                minor: $minor,
                patch: $patch,
                pre: vec![ $( $pre.into_itentifier(), )* ],
                build: Vec::new(),
            }
        };

        ($major:literal . $minor:literal . $patch:literal + $( $build:literal )-+ ) => {
            Version {
                major: $major,
                minor: $minor,
                patch: $patch,
                pre: Vec::new(),
                build: vec![ $( $build.into_itentifier(), )* ],
            }
        };

        ($major:literal . $minor:literal . $patch:literal - $( $pre:literal )-+ + $( $build:literal )-+ ) => {
            Version {
                major: $major,
                minor: $minor,
                patch: $patch,
                pre: vec![ $( $pre.into_itentifier(), )* ],
                build: vec![ $( $build.into_itentifier(), )* ],
            }
        };
    }

    #[test_case("1" => Ok(vers!(1 . 0 . 0)); "major only")]
    #[test_case("1.2" => Ok(vers!(1 . 2 . 0)); "major.minor only")]
    #[test_case("1.2.3" => Ok(vers!(1 . 2 . 3)); "major.minor.patch")]
    #[test_case("  1.2.3  " => Ok(vers!(1 . 2 . 3)); "with whitespace")]
    fn test_simple(input: &str) -> Result<Version<'_>, Error<'_>> {
        parse::<Version<'_>>(input)
    }

    #[test_case("1.2.3-alpha1" => Ok(vers!(1 . 2 . 3 - "alpha1")))]
    #[test_case("  1.2.3-alpha2  " => Ok(vers!(1 . 2 . 3 - "alpha2")))]
    #[test_case("3.1.0-M13-beta3" => Ok(vers!(3 . 1 . 0 - "M13" - "beta3")))]
    #[test_case("1.2.3-alpha01.drop02" => Ok(vers!(1 . 2 . 3 - "alpha01" - "drop02")))]
    #[test_case("1.4.1-alpha01" => Ok(vers!(1 . 4 . 1 - "alpha01")))]
    #[test_case("1.4-alpha02" => Ok(vers!(1 . 4 . 0 - "alpha02")))]
    #[test_case("1-alpha03" => Ok(vers!(1 . 0 . 0 - "alpha03")))]
    #[test_case("1.9.3.RC1" => Ok(vers!(1 . 9 . 3 - "RC1")))]
    #[test_case("1.9.RC2" => Ok(vers!(1 . 9 . 0 - "RC2")))]
    #[test_case("1.RC3" => Ok(vers!(1 . 0 . 0 - "RC3")))]
    #[test_case("1.3.3-7" => Ok(vers!(1 . 3 . 3 - 7)))]
    #[test_case("5.9.0-202009080501-r" => Ok(vers!(5 . 9 . 0 - 202009080501 - "r")))]
    #[test_case("1.2.3.RC.4" => Ok(vers!(1 . 2 . 3 - "RC" - 4)))]
    fn test_pre_release(input: &str) -> Result<Version<'_>, Error<'_>> {
        parse::<Version<'_>>(input)
    }

    #[test_case("1.2.3+build1" => Ok(vers!(1 . 2 . 3 + "build1")))]
    #[test_case("  1.2.3+build2  " => Ok(vers!(1 . 2 . 3 + "build2")))]
    #[test_case("3.1.0+build3-r021" => Ok(vers!(3 . 1 . 0 + "build3" - "r021")))]
    #[test_case("1.2.3+build01.drop02" => Ok(vers!(1 . 2 . 3 + "build01" - "drop02")))]
    #[test_case("1.4.1+build01" => Ok(vers!(1 . 4 . 1 + "build01")))]
    #[test_case("1.4+build02" => Ok(vers!(1 . 4 . 0 + "build02")))]
    #[test_case("1+build03" => Ok(vers!(1 . 0 . 0 + "build03")))]
    #[test_case("7.2.0+28-2f9fb552" => Ok(vers!(7 . 2 . 0 + 28 -  "2f9fb552" )))]
    #[test_case("1.3.3.7" => Ok(vers!(1 . 3 . 3 + 7)))]
    #[test_case("5.9.0.202009080501-r" => Ok(vers!(5 . 9 . 0 + 202009080501 - "r")))]
    fn test_build(input: &str) -> Result<Version<'_>, Error<'_>> {
        parse::<Version<'_>>(input)
    }

    #[test_case("1.2.3-alpha1+build5" => Ok(vers!(1 . 2 . 3 - "alpha1" + "build5" )))]
    #[test_case("   1.2.3-alpha2+build6   " => Ok(vers!(1 . 2 . 3 - "alpha2" + "build6" )))]
    #[test_case("1.2.3-1.alpha1.9+build5.7.3aedf  " => Ok(vers!(1 . 2 . 3 - 1 - "alpha1" - 9 + "build5" - 7 - "3aedf" )))]
    #[test_case("0.4.0-beta.1+0851523" => Ok(vers!(0 . 4 . 0 - "beta" - 1 + "0851523" )))]
    fn test_combined(input: &str) -> Result<Version<'_>, Error<'_>> {
        parse::<Version<'_>>(input)
    }

    #[test_case("2.7.3.Final" => Ok(vers!(2 . 7 . 3 + "Final" )); "full dot final")]
    #[test_case("2.7.3-Final" => Ok(vers!(2 . 7 . 3 + "Final" )); "full hyphen final")]
    #[test_case("2.7.3+Final" => Ok(vers!(2 . 7 . 3 + "Final" )); "full plus final")]
    #[test_case("2.7.3.Release" => Ok(vers!(2 . 7 . 3 + "Release" )); "full dot release")]
    #[test_case("2.7.3-Release" => Ok(vers!(2 . 7 . 3 + "Release" )); "full hyphen release")]
    #[test_case("2.7.3+Release" => Ok(vers!(2 . 7 . 3 + "Release" )); "full plus release")]
    #[test_case("2.7.Final" => Ok(vers!(2 . 7 . 0 + "Final" )); "minor dot final")]
    #[test_case("2.7-Final" => Ok(vers!(2 . 7 . 0 + "Final" )); "minor hyphen final")]
    #[test_case("2.7+Final" => Ok(vers!(2 . 7 . 0 + "Final" )); "minor plus final")]
    #[test_case("2.7.Release" => Ok(vers!(2 . 7 . 0 + "Release" )); "minor dot release")]
    #[test_case("2.7-Release" => Ok(vers!(2 . 7 . 0 + "Release" )); "minor hyphen release")]
    #[test_case("2.7+Release" => Ok(vers!(2 . 7 . 0 + "Release" )); "minor plus release")]
    #[test_case("2.Final" => Ok(vers!(2 . 0 . 0 + "Final" )); "major dot final")]
    #[test_case("2-Final" => Ok(vers!(2 . 0 . 0 + "Final" )); "major hyphen final")]
    #[test_case("2+Final" => Ok(vers!(2 . 0 . 0 + "Final" )); "major plus final")]
    #[test_case("2.Release" => Ok(vers!(2 . 0 . 0 + "Release" )); "major dot release")]
    #[test_case("2-Release" => Ok(vers!(2 . 0 . 0 + "Release" )); "major hyphen release")]
    #[test_case("2+Release" => Ok(vers!(2 . 0 . 0 + "Release" )); "major plus release")]
    fn test_with_release_identifier(input: &str) -> Result<Version<'_>, Error<'_>> {
        parse::<Version<'_>>(input)
    }

    #[test_case("2020.4.9" => Ok(vers!(2020 . 4 . 9)))]
    #[test_case("2020.04.09" => Ok(vers!(2020 . 4 . 9)))]
    #[test_case("2020.4" => Ok(vers!(2020 . 4 . 0)))]
    #[test_case("2020.04" => Ok(vers!(2020 . 4 . 0)))]
    fn test_date_versions(input: &str) -> Result<Version<'_>, Error<'_>> {
        parse::<Version<'_>>(input)
    }

    #[test_case("1" => Ok(vers!(1 . 0 . 0)))]
    #[test_case("01" => Ok(vers!(1 . 0 . 0)))]
    #[test_case("00001" => Ok(vers!(1 . 0 . 0)))]
    #[test_case("1.2.3-1" => Ok(vers!(1 . 2 . 3 - 1)))]
    #[test_case("1.2.3-01" => Ok(vers!(1 . 2 . 3 - "01")))]
    #[test_case("1.2.3-0001" => Ok(vers!(1 . 2 . 3 - "0001")))]
    #[test_case("2.3.4+1" => Ok(vers!(2 . 3 . 4 + 1)))]
    #[test_case("2.3.4+01" => Ok(vers!(2 . 3 . 4 + "01")))]
    #[test_case("2.3.4+0001" => Ok(vers!(2 . 3 . 4 + "0001")))]
    fn test_leading_zeroes(input: &str) -> Result<Version<'_>, Error<'_>> {
        parse::<Version<'_>>(input)
    }

    #[test_case("v1" => Ok(vers!(1 . 0 . 0)))]
    #[test_case("  v2  " => Ok(vers!(2 . 0 . 0)))]
    #[test_case("v1.2.3" => Ok(vers!(1 . 2 . 3)))]
    #[test_case("v1.3.3-7" => Ok(vers!(1 . 3 . 3 - 7)))]
    #[test_case("V3" => Ok(vers!(3 . 0 . 0)))]
    #[test_case("  V5  " => Ok(vers!(5 . 0 . 0)))]
    #[test_case("V2.3.4" => Ok(vers!(2 . 3 . 4)))]
    #[test_case("V4.2.4-2" => Ok(vers!(4 . 2 . 4 - 2)))]
    fn test_leading_v(input: &str) -> Result<Version<'_>, Error<'_>> {
        parse::<Version<'_>>(input)
    }

    #[test_case("" => Err(ErrorSpan::new(ErrorType::Missing(Segment::Part(Part::Major)), Span::new(0, 0))))]
    #[test_case("  " => Err(ErrorSpan::new(ErrorType::Missing(Segment::Part(Part::Major)), Span::new(0, 2))))]
    #[test_case("1. " => Err(ErrorSpan::new(ErrorType::Missing(Segment::Part(Part::Minor)), Span::new(2, 3))))]
    #[test_case("1.2. " => Err(ErrorSpan::new(ErrorType::Missing(Segment::Part(Part::Patch)), Span::new(4, 5))))]
    #[test_case("1.2.3-" => Err(ErrorSpan::new(ErrorType::Missing(Segment::PreRelease), Span::new(5, 6))))]
    #[test_case("1.2.3-." => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 7))); "pre release trailing dot")]
    #[test_case("1.2.3--" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 7))); "pre release trailing hyphen")]
    #[test_case("1.2.3-+" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 7))); "pre release trailing plus")]
    #[test_case("1.2.3+" => Err(ErrorSpan::new(ErrorType::Missing(Segment::Build), Span::new(5, 6))))]
    #[test_case("1.2.3+." => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 7))); "build trailing dot")]
    #[test_case("1.2.3+-" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 7))); "build trailing hyphen")]
    #[test_case("1.2.3++" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 7))); "build trailing plus")]
    #[test_case("v.1.2.3" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Major), Span::new(0, 1))))]
    #[test_case("v-2.3.4" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Major), Span::new(0, 1))))]
    #[test_case("v+3.4.5" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Major), Span::new(0, 1))))]
    #[test_case("vv1.2.3" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Major), Span::new(0, 3))))]
    #[test_case("v v1.2.3" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Major), Span::new(0, 1))))]
    #[test_case("a.b.c" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Major), Span::new(0, 1))))]
    #[test_case("1.+.0" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Minor), Span::new(2, 3))))]
    #[test_case("1.2.." => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Patch), Span::new(4, 5))))]
    #[test_case("123456789012345678901234567890" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Major), Span::new(0, 30))))]
    #[test_case("1 abc" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(2, 5))))]
    #[test_case("1.2.3 abc" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 9))))]
    fn test_simple_errors(input: &str) -> Result<Version<'_>, ErrorSpan> {
        parse_version::<_, Version<'_>>(input, lex(input))
    }

    #[test_case("" => r#"Could not parse the major identifier: No input
|    
|    
"#; "empty string")]
    #[test_case("  " => r#"Could not parse the major identifier: No input
|      
|    ^^
"#; "blank string")]
    #[test_case("1.2.3-" => r#"Could not parse the pre-release identifier: No input
|    1.2.3-
|    ~~~~~^
"#)]
    #[test_case("1.2.3+" => r#"Could not parse the build identifier: No input
|    1.2.3+
|    ~~~~~^
"#)]
    #[test_case("a.b.c" => r#"Could not parse the major identifier: `a` is not a number
|    a.b.c
|    ^
"#)]
    #[test_case("1.+.0" => r#"Could not parse the minor identifier: `+` is not a number
|    1.+.0
|    ~~^
"#)]
    #[test_case("1.2.." => r#"Could not parse the patch identifier: `.` is not a number
|    1.2..
|    ~~~~^
"#)]
    #[test_case("123456789012345678901234567890" => r#"Could not parse the major identifier: `123456789012345678901234567890` is not a number
|    123456789012345678901234567890
|    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
"#)]
    #[test_case("1.2.3 abc" => r#"Unexpected `abc`
|    1.2.3 abc
|    ~~~~~~^^^
"#)]
    fn test_full_errors(input: &str) -> String {
        format!("{:#}", parse::<Version<'_>>(input).unwrap_err())
    }

    #[test]
    fn test_lexer() {
        // TODO: assert on spans
        let tokens = lex(" v v1.2.3-1.alpha1.9+build5.7.3aedf-01337  ")
            .map(|s| s.token)
            .collect::<Vec<_>>();
        assert_eq!(
            tokens,
            vec![
                Token::Whitespace,
                Token::Alpha,
                Token::Whitespace,
                Token::VNumeric,
                Token::Dot,
                Token::Numeric,
                Token::Dot,
                Token::Numeric,
                Token::Hyphen,
                Token::Numeric,
                Token::Dot,
                Token::Alpha,
                Token::Dot,
                Token::Numeric,
                Token::Plus,
                Token::Alpha,
                Token::Dot,
                Token::Numeric,
                Token::Dot,
                Token::Alpha,
                Token::Hyphen,
                Token::ZeroNumeric,
                Token::Whitespace,
            ]
        );
    }

    #[test]
    fn test_lexer_numbers() {
        // TODO: assert on spans
        let tokens = lex("1.0.00.08.09.8.9").map(|s| s.token).collect::<Vec<_>>();
        assert_eq!(
            tokens,
            vec![
                Token::Numeric,
                Token::Dot,
                Token::Numeric,
                Token::Dot,
                Token::ZeroNumeric,
                Token::Dot,
                Token::ZeroNumeric,
                Token::Dot,
                Token::ZeroNumeric,
                Token::Dot,
                Token::Numeric,
                Token::Dot,
                Token::Numeric,
            ]
        );
    }

    #[test]
    fn test_lexer_invalid_number() {
        // TODO: assert on spans
        let input = "123456789012345678901234567890";
        let tokens = lex(input).map(|s| s.token).collect::<Vec<_>>();
        assert_eq!(tokens, vec![Token::Numeric]);
    }

    #[test]
    fn test_lexer_invalid_token() {
        // TODO: assert on spans
        let input = "!#∰~[🙈]";
        let tokens = lex(input).map(|s| s.token).collect::<Vec<_>>();
        assert_eq!(
            tokens,
            vec![
                Token::UnexpectedChar,
                Token::UnexpectedChar,
                Token::UnexpectedChar,
                Token::UnexpectedChar,
                Token::UnexpectedChar,
                Token::UnexpectedChar,
                Token::UnexpectedChar
            ]
        );
    }

    #[test]
    fn test_lexer_whitespace() {
        let input = " \t\r\n";
        let tokens = lex(input).map(|s| s.token).collect::<Vec<_>>();
        assert_eq!(tokens, vec![Token::Whitespace]);
    }

    #[test]
    fn test_parse_tokens() {
        let tokens = vec![
            TokenSpan::new(Token::Whitespace, 0, 2),
            TokenSpan::new(Token::Numeric, 2, 3),
            TokenSpan::new(Token::Dot, 3, 4),
            TokenSpan::new(Token::Numeric, 4, 5),
            TokenSpan::new(Token::Dot, 5, 6),
            TokenSpan::new(Token::Numeric, 6, 7),
            TokenSpan::new(Token::Hyphen, 7, 8),
            TokenSpan::new(Token::Numeric, 8, 9),
            TokenSpan::new(Token::Dot, 9, 10),
            TokenSpan::new(Token::Alpha, 10, 16),
            TokenSpan::new(Token::Dot, 16, 17),
            TokenSpan::new(Token::Numeric, 17, 18),
            TokenSpan::new(Token::Plus, 18, 19),
            TokenSpan::new(Token::Alpha, 19, 25),
            TokenSpan::new(Token::Dot, 25, 26),
            TokenSpan::new(Token::Numeric, 26, 27),
            TokenSpan::new(Token::Dot, 27, 28),
            TokenSpan::new(Token::Alpha, 28, 33),
            TokenSpan::new(Token::Whitespace, 33, 36),
        ];
        assert_eq!(
            // TODO: assert on spans
            parse_version::<_, Version<'_>>("  1.2.3-1.alpha1.9+build5.7.3aedf   ", tokens),
            Ok(Version {
                major: 1,
                minor: 2,
                patch: 3,
                pre: vec![
                    Identifier::Numeric(1),
                    Identifier::AlphaNumeric("alpha1".into()),
                    Identifier::Numeric(9),
                ],
                build: vec![
                    Identifier::AlphaNumeric("build5".into()),
                    Identifier::Numeric(7),
                    Identifier::AlphaNumeric("3aedf".into()),
                ],
            })
        );
    }

    #[test]
    fn parse_version_number_numeric() {
        assert_eq!(
            parse_number(TokenSpan::new(Token::Numeric, 0, 2), "42", Part::Major),
            Ok(42)
        )
    }

    #[test]
    fn parse_version_number_zero_numeric() {
        assert_eq!(
            parse_number(TokenSpan::new(Token::ZeroNumeric, 0, 3), "042", Part::Major),
            Ok(42)
        )
    }

    #[test]
    fn parse_version_number_v_numeric() {
        assert_eq!(
            parse_number(TokenSpan::new(Token::VNumeric, 0, 3), "v42", Part::Major),
            Ok(42)
        )
    }

    #[test_case((Token::Dot, Part::Patch) => Err(ErrorType::NotANumber(Part::Patch)))]
    #[test_case((Token::Plus, Part::Patch) => Err(ErrorType::NotANumber(Part::Patch)))]
    #[test_case((Token::Hyphen, Part::Patch) => Err(ErrorType::NotANumber(Part::Patch)))]
    #[test_case((Token::Whitespace, Part::Patch) => Err(ErrorType::NotANumber(Part::Patch)))]
    #[test_case((Token::Alpha, Part::Patch) => Err(ErrorType::NotANumber(Part::Patch)))]
    #[test_case((Token::UnexpectedChar, Part::Patch) => Err(ErrorType::NotANumber(Part::Patch)))]
    fn parse_version_number_error(v: (Token, Part)) -> Result<u64, ErrorType> {
        let (token, part) = v;
        parse_number_inner(TokenSpan::new(token, 0, 1), "x", part)
    }

    #[test_case("Final"; "final pascal")]
    #[test_case("FINAL"; "final upper")]
    #[test_case("final"; "final lower")]
    #[test_case("FiNaL"; "final upper sponge")]
    #[test_case("fInAL"; "final lower sponge")]
    #[test_case("Release"; "release pascal")]
    #[test_case("RELEASE"; "release upper")]
    #[test_case("release"; "release lower")]
    #[test_case("ReLeAsE"; "release upper sponge")]
    #[test_case("rElEAse"; "release lower sponge")]
    fn test_is_release_identifier(v: &str) {
        assert!(is_release_identifier(v));
    }

    #[cfg_attr(any(feature = "semver", feature = "semver10"), test_case("1.2.3" => parse::<Version<'_>>("1.2.3.Final"); "dot final"))]
    #[cfg_attr(any(feature = "semver", feature = "semver10"), test_case("1.2.3" => parse::<Version<'_>>("1.2.3.Release"); "dot release"))]
    #[cfg_attr(any(feature = "semver", feature = "semver10"), test_case("1.2.3" => parse::<Version<'_>>("1.2.3-Final"); "hyphen final"))]
    #[cfg_attr(any(feature = "semver", feature = "semver10"), test_case("1.2.3" => parse::<Version<'_>>("1.2.3-Release"); "hyphen release"))]
    #[cfg_attr(any(feature = "semver", feature = "semver10"), test_case("1.2.3" => parse::<Version<'_>>("1.2.3+Final"); "plus final"))]
    #[cfg_attr(any(feature = "semver", feature = "semver10"), test_case("1.2.3" => parse::<Version<'_>>("1.2.3+Release"); "plus release"))]
    #[cfg(any(feature = "semver", feature = "semver10"))]
    fn test_release_cmp(v: &str) -> Result<Version<'_>, Error<'_>> {
        parse::<Version<'_>>(v)
    }

    #[cfg_attr(
        all(
            any(
                all(not(feature = "semver"), feature = "semver10"),
                all(feature = "semver", not(feature = "semver10"))
            ),
            feature = "version_lite"
        ),
        test_case("1.2.3")
    )]
    #[cfg_attr(
        all(
            any(
                all(not(feature = "semver"), feature = "semver10"),
                all(feature = "semver", not(feature = "semver10"))
            ),
            feature = "version_lite"
        ),
        test_case("1.2.3-alpha01")
    )]
    #[cfg_attr(
        all(
            any(
                all(not(feature = "semver"), feature = "semver10"),
                all(feature = "semver", not(feature = "semver10"))
            ),
            feature = "version_lite"
        ),
        test_case("1.2.3+build02")
    )]
    #[cfg_attr(
        all(
            any(
                all(not(feature = "semver"), feature = "semver10"),
                all(feature = "semver", not(feature = "semver10"))
            ),
            feature = "version_lite"
        ),
        test_case("1.2.3-beta03+r4")
    )]
    #[cfg(all(
        any(
            all(not(feature = "semver"), feature = "semver10"),
            all(feature = "semver", not(feature = "semver10"))
        ),
        feature = "version_lite"
    ))]
    fn test_semver_and_lite(v: &str) {
        let sem = parse::<SemVer>(v).unwrap();
        let lite = parse::<VersionLite<'_>>(v).unwrap();
        let sem_from_lite = SemVer::from(lite);
        assert_eq!(sem, sem_from_lite);
    }
}
