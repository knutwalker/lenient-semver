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

#![warn(
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
    parse_version::<_, V>(lex(input)).map_err(|ErrorSpan { error, span }| Error {
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

    /// Add an alpha-numeric pre-release identifier.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    ///
    /// This method might be called multiple times.
    fn add_pre_release_str(&mut self, pre_release: &'input str);

    /// Add a numeric pre-release identifier.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    ///
    /// This method might be called multiple times.
    fn add_pre_release_num(&mut self, pre_release: u64);

    /// Add an alpha-numeric build identifier.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    ///
    /// This method might be called multiple times.
    fn add_build_str(&mut self, build: &'input str);

    /// Add a numeric build identifier.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    ///
    /// This method might be called multiple times.
    fn add_build_num(&mut self, build: u64);

    /// Construct the final version.
    fn build(self) -> Self::Out;
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

    fn add_pre_release_str(&mut self, pre_release: &'input str) {
        self.pre
            .push(semver::Identifier::AlphaNumeric(pre_release.into()))
    }

    fn add_pre_release_num(&mut self, pre_release: u64) {
        self.pre.push(semver::Identifier::Numeric(pre_release))
    }

    fn add_build_str(&mut self, build: &'input str) {
        self.build
            .push(semver::Identifier::AlphaNumeric(build.into()))
    }

    fn add_build_num(&mut self, build: u64) {
        self.build.push(semver::Identifier::Numeric(build))
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

    fn add_pre_release_str(&mut self, pre_release: &'input str) {
        self.pre.push(IdentifierLite::AlphaNumeric(pre_release))
    }

    fn add_pre_release_num(&mut self, pre_release: u64) {
        self.pre.push(IdentifierLite::Numeric(pre_release))
    }

    fn add_build_str(&mut self, build: &'input str) {
        self.build.push(IdentifierLite::AlphaNumeric(build))
    }

    fn add_build_num(&mut self, build: u64) {
        self.build.push(IdentifierLite::Numeric(build))
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
            start = self.span.start,
            width = self.span.end - self.span.start
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

// TODO: parsers as iterator over some ast that is
// Major(num), Minor(num), etc
//

enum Op<'input> {
    Major(u64),
    Minor(u64),
    Patch(u64),
    Dot4(u64),
    PreReleaseNum(u64),
    PreRelease(&'input str),
    BuildNum(u64),
    Build(&'input str),
    Failed(ErrorSpan),
}

#[derive(Debug, Copy, Clone)]
enum State {
    Part(Part),
    PreRelease,
    Build,
}

struct Tokens<'input, I> {
    tokens: I,
    span: Span,
    stash: Option<Token<'input>>,
}

impl<'input, I> Tokens<'input, I> {
    fn new(tokens: I) -> Self {
        Self {
            tokens,
            span: Span::new(0, 0),
            stash: None,
        }
    }

    fn stash(mut self, token: Token<'input>) -> Self {
        self.stashing(token);
        self
    }

    fn stashing(&mut self, token: Token<'input>) {
        if let Some(old) = self.stash.replace(token) {
            panic!("double stash, old value: {:?}", old)
        }
    }

    fn stashed(&mut self, token: Token<'input>) -> &mut Self {
        self.stashing(token);
        self
    }
}

impl<'input, I> Iterator for Tokens<'input, I>
where
    I: Iterator<Item = TokenSpan<'input>>,
{
    type Item = Token<'input>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(token) = self.stash.take() {
            return Some(token);
        }
        let TokenSpan { token, span } = self.tokens.next()?;
        self.span = span;
        Some(token)
    }
}

#[derive(Debug, Copy, Clone)]
enum State2 {
    Major,
    AfterMajor,
    Minor,
    AfterMinor,
    Patch,
    AfterPatch,
    PossibleDot4,
    Dot4,
    AfterDot4,
    PreRelease,
    AfterPreRelease,
    Build,
    AfterBuild,
    Finish,
}

struct Parser<'input, I> {
    tokens: Tokens<'input, I>,
    state: State2,
    leading_v: bool,
    potential_dot4: bool,
    done: bool,
}

impl<'input, I> Parser<'input, I> {
    fn new(tokens: Tokens<'input, I>) -> Self {
        Self {
            tokens,
            state: State2::Major,
            leading_v: false,
            potential_dot4: false,
            done: false,
        }
    }
}

impl<'input, I> Parser<'input, I>
where
    I: Iterator<Item = TokenSpan<'input>>,
{
    fn try_next(&mut self) -> Result<Option<Op<'input>>, ErrorSpan> {
        loop {
            match self.state {
                State2::Major => match self.tokens.next() {
                    // unexpected end
                    None => {
                        return Err(ErrorSpan::missing_part(Part::Major, self.tokens.span));
                    }
                    // skip initial whitespace
                    Some(Token::Whitespace) => {}
                    // Skip leading v that is a separate token
                    Some(Token::Alpha(v)) if !self.leading_v && (v == "v" || v == "V") => {
                        self.leading_v = true;
                    }
                    Some(token) => {
                        let num =
                            parse_number(token, !self.leading_v, Part::Major, self.tokens.span)?;
                        self.state = State2::AfterMajor;
                        return Ok(Some(Op::Major(num)));
                    }
                },
                State2::AfterMajor => {
                    self.state = match self.tokens.next() {
                        None => return Ok(None),
                        Some(Token::Dot) => State2::Minor,
                        Some(Token::Hyphen) => State2::PreRelease,
                        Some(Token::Plus) => State2::Build,
                        Some(token) => return finish_tokens2(self.tokens.stashed(token)),
                    }
                }
                State2::Minor => match self.tokens.next() {
                    // things like 1.Final, early stop with a single build identifier
                    Some(Token::Alpha(v)) if is_release_identifier(v) => {
                        self.state = State2::Finish;
                        return Ok(Some(Op::Build(v)));
                    }
                    // any alpha token skips right into pre-release parsing
                    Some(Token::Alpha(v)) => {
                        self.state = State2::AfterPreRelease;
                        return Ok(Some(Op::PreRelease(v)));
                    }
                    // unexpected end
                    Some(Token::Whitespace) | None => {
                        return Err(ErrorSpan::missing_part(Part::Minor, self.tokens.span));
                    }
                    // any other token is tried as a number
                    Some(token) => {
                        let num = parse_number(token, false, Part::Minor, self.tokens.span)?;
                        self.state = State2::AfterMinor;
                        return Ok(Some(Op::Minor(num)));
                    }
                },
                State2::AfterMinor => {
                    self.state = match self.tokens.next() {
                        None => return Ok(None),
                        Some(Token::Dot) => State2::Patch,
                        Some(Token::Hyphen) => State2::PreRelease,
                        Some(Token::Plus) => State2::Build,
                        Some(token) => return finish_tokens2(self.tokens.stashed(token)),
                    }
                }
                State2::Patch => match self.tokens.next() {
                    // things like 1.Final, early stop with a single build identifier
                    Some(Token::Alpha(v)) if is_release_identifier(v) => {
                        self.state = State2::Finish;
                        return Ok(Some(Op::Build(v)));
                    }
                    // any alpha token skips right into pre-release parsing
                    Some(Token::Alpha(v)) => {
                        self.state = State2::AfterPreRelease;
                        return Ok(Some(Op::PreRelease(v)));
                    }
                    // unexpected end
                    Some(Token::Whitespace) | None => {
                        return Err(ErrorSpan::missing_part(Part::Patch, self.tokens.span));
                    }
                    // any other token is tried as a number
                    Some(token) => {
                        let num = parse_number(token, false, Part::Patch, self.tokens.span)?;
                        self.state = State2::AfterPatch;
                        return Ok(Some(Op::Patch(num)));
                    }
                },
                State2::AfterPatch => {
                    self.state = match self.tokens.next() {
                        None => return Ok(None),
                        Some(Token::Dot) => State2::PossibleDot4,
                        Some(Token::Hyphen) => State2::PreRelease,
                        Some(Token::Plus) => State2::Build,
                        Some(token) => {
                            self.tokens.stashing(token);
                            State2::Finish
                        }
                    }
                }
                State2::PossibleDot4 => {
                    match self.tokens.next() {
                        // things like 1.2.3.Final, need to interpret this as a build identifier
                        Some(Token::Alpha(v)) if is_release_identifier(v) => {
                            self.state = State2::Finish;
                            return Ok(Some(Op::Build(v)));
                        }
                        // regular pre-release part
                        Some(Token::Alpha(v)) => {
                            self.state = State2::AfterPreRelease;
                            return Ok(Some(Op::PreRelease(v)));
                        }
                        // leading zero numbers in pre-release are alphanum
                        Some(Token::ZeroNum(v, _)) => {
                            self.state = State2::AfterPreRelease;
                            return Ok(Some(Op::PreRelease(v)));
                        }
                        // continued version numbers
                        Some(Token::Number(v)) => {
                            self.state = State2::AfterDot4;
                            return Ok(Some(Op::Dot4(v)));
                        }
                        // unexpected end
                        Some(Token::Whitespace) | None => {
                            return Err(ErrorSpan::missing_pre(self.tokens.span))
                        }
                        // any other token is invalid
                        Some(_) => {
                            return Err(ErrorSpan::unexpected(self.tokens.span));
                        }
                    }
                }
                State2::Dot4 => {
                    match self.tokens.next() {
                        // regular build part
                        Some(Token::Alpha(v)) => {
                            self.state = State2::AfterBuild;
                            return Ok(Some(Op::Build(v)));
                        }
                        // leading zero numbers in build are alphanum
                        Some(Token::ZeroNum(v, _)) => {
                            self.state = State2::AfterBuild;
                            return Ok(Some(Op::Build(v)));
                        }
                        // continued version numbers
                        Some(Token::Number(v)) => {
                            self.state = State2::AfterDot4;
                            return Ok(Some(Op::Dot4(v)));
                        }
                        // unexpected end
                        Some(Token::Whitespace) | None => {
                            return Err(ErrorSpan::missing_build(self.tokens.span))
                        }
                        // any other token is invalid
                        Some(_) => {
                            return Err(ErrorSpan::unexpected(self.tokens.span));
                        }
                    }
                }
                State2::AfterDot4 => {
                    self.state = match self.tokens.next() {
                        None => return Ok(None),
                        Some(Token::Dot) | Some(Token::Hyphen) => State2::Dot4,
                        Some(Token::Plus) => State2::Build,
                        Some(token) => return finish_tokens2(self.tokens.stashed(token)),
                    };
                }
                State2::PreRelease => {
                    match self.tokens.next() {
                        // things like 1.2.3.Final, need to interpret this as a build identifier
                        Some(Token::Alpha(v)) if is_release_identifier(v) => {
                            self.state = State2::Finish;
                            return Ok(Some(Op::Build(v)));
                        }
                        // regular pre-release part
                        Some(Token::Alpha(v)) => {
                            self.state = State2::AfterPreRelease;
                            return Ok(Some(Op::PreRelease(v)));
                        }
                        // leading zero numbers in pre-release are alphanum
                        Some(Token::ZeroNum(v, _)) => {
                            self.state = State2::AfterPreRelease;
                            return Ok(Some(Op::PreRelease(v)));
                        }
                        // regular pre-release part
                        Some(Token::Number(v)) => {
                            self.state = State2::AfterPreRelease;
                            return Ok(Some(Op::PreReleaseNum(v)));
                        }
                        // unexpected end
                        Some(Token::Whitespace) | None => {
                            return Err(ErrorSpan::missing_pre(self.tokens.span))
                        }
                        // any other token is invalid
                        Some(_) => {
                            return Err(ErrorSpan::unexpected(self.tokens.span));
                        }
                    }
                }
                State2::AfterPreRelease => {
                    self.state = match self.tokens.next() {
                        None => return Ok(None),
                        Some(Token::Dot) | Some(Token::Hyphen) => State2::PreRelease,
                        Some(Token::Plus) => State2::Build,
                        Some(token) => return finish_tokens2(self.tokens.stashed(token)),
                    };
                }
                State2::Build => {
                    match self.tokens.next() {
                        // regular build part
                        Some(Token::Alpha(v)) => {
                            self.state = State2::AfterBuild;
                            return Ok(Some(Op::Build(v)));
                        }
                        // leading zero numbers in build are alphanum
                        Some(Token::ZeroNum(v, _)) => {
                            self.state = State2::AfterBuild;
                            return Ok(Some(Op::Build(v)));
                        }
                        // regular build part
                        Some(Token::Number(v)) => {
                            self.state = State2::AfterBuild;
                            return Ok(Some(Op::BuildNum(v)));
                        }
                        // unexpected end
                        Some(Token::Whitespace) | None => {
                            return Err(ErrorSpan::missing_build(self.tokens.span));
                        }
                        // any other token is invalid
                        Some(_) => {
                            return Err(ErrorSpan::unexpected(self.tokens.span));
                        }
                    }
                }
                State2::AfterBuild => {
                    self.state = match self.tokens.next() {
                        None => return Ok(None),
                        Some(Token::Dot) | Some(Token::Hyphen) => State2::Build,
                        Some(token) => return finish_tokens2(self.tokens.stashed(token)),
                    };
                }
                State2::Finish => {
                    return finish_tokens2(&mut self.tokens);
                }
            }
        }
    }
}
impl<'input, I> Iterator for Parser<'input, I>
where
    I: Iterator<Item = TokenSpan<'input>>,
{
    type Item = Op<'input>;

    fn next(&mut self) -> Option<Self::Item> {
        self.try_next().unwrap_or_else(|e| Some(Op::Failed(e)))
    }
}

fn parse_version<'input, I, V>(tokens: I) -> Result<V::Out, ErrorSpan>
where
    I: IntoIterator<Item = TokenSpan<'input>>,
    V: VersionBuilder<'input>,
{
    // parse_version1::<'input, I, V>(tokens)
    // parse_version2::<'input, I, V>(tokens)
    parse_version3::<'input, I, V>(tokens)
}

fn parse_version1<'input, I, V>(tokens: I) -> Result<V::Out, ErrorSpan>
where
    I: IntoIterator<Item = TokenSpan<'input>>,
    V: VersionBuilder<'input>,
{
    let tokens = tokens.into_iter();
    let mut tokens = Tokens::new(tokens);
    let mut version = V::new();

    let mut state = State::Part(Part::Major);
    let mut leading_v = false;
    let mut potential_dot4 = false;

    loop {
        match state {
            State::Part(Part::Major) => match tokens.next() {
                // unexpected end
                None => return Err(ErrorSpan::missing_part(Part::Major, tokens.span)),
                // skip initial whitespace
                Some(Token::Whitespace) => {}
                // Skip leading v that is a separate token
                Some(Token::Alpha(v)) if !leading_v && (v == "v" || v == "V") => {
                    leading_v = true;
                }
                Some(token) => {
                    version.set_major(parse_number(token, !leading_v, Part::Major, tokens.span)?);
                    state = match tokens.next() {
                        None => return finish(version),
                        Some(Token::Dot) => State::Part(Part::Minor),
                        Some(Token::Hyphen) => State::PreRelease,
                        Some(Token::Plus) => State::Build,
                        Some(token) => {
                            return finish_tokens(tokens.stash(token), version);
                        }
                    };
                }
            },
            State::Part(part) => match tokens.next() {
                // things like 1.Final, early stop with a single build identifier
                Some(Token::Alpha(v)) if is_release_identifier(v) => {
                    version.add_build_str(v);
                    return finish_tokens(tokens, version);
                }
                // any alpha token skips right into pre-release parsing
                Some(Token::Alpha(v)) => {
                    tokens = tokens.stash(Token::Alpha(v));
                    state = State::PreRelease;
                }
                // unexpected end
                Some(Token::Whitespace) | None => {
                    return Err(ErrorSpan::missing_part(part, tokens.span))
                }
                // any other token is tried as a number
                Some(token) => {
                    let num = parse_number(token, false, part, tokens.span)?;
                    match part {
                        Part::Major => unreachable!(),
                        Part::Minor => version.set_minor(num),
                        Part::Patch => version.set_patch(num),
                    }
                    state = match tokens.next() {
                        None => return finish(version),
                        Some(Token::Dot) => match part {
                            Part::Major => unreachable!(),
                            Part::Minor => State::Part(Part::Patch),
                            Part::Patch => {
                                potential_dot4 = true;
                                State::PreRelease
                            }
                        },
                        Some(Token::Hyphen) => State::PreRelease,
                        Some(Token::Plus) => State::Build,
                        Some(token) => return finish_tokens(tokens.stash(token), version),
                    };
                }
            },
            State::PreRelease => {
                match tokens.next() {
                    // things like 1.2.3.Final, need to interpret this as a build identifier
                    Some(Token::Alpha(v)) if is_release_identifier(v) => {
                        version.add_build_str(v);
                        return finish_tokens(tokens, version);
                    }
                    // regular pre-release part
                    Some(Token::Alpha(v)) => {
                        version.add_pre_release_str(v);
                    }
                    // leading zero numbers in pre-release are alphanum
                    Some(Token::ZeroNum(v, _)) => {
                        version.add_pre_release_str(v);
                    }
                    // regular pre-release part
                    Some(Token::Number(v)) => {
                        if potential_dot4 {
                            tokens = tokens.stash(Token::Number(v));
                            state = State::Build;
                            continue;
                        }
                        version.add_pre_release_num(v);
                    }
                    // unexpected end
                    Some(Token::Whitespace) | None => {
                        return Err(ErrorSpan::missing_pre(tokens.span))
                    }
                    // any other token is invalid
                    Some(_) => {
                        return Err(ErrorSpan::unexpected(tokens.span));
                    }
                }
                potential_dot4 = false;
                state = match tokens.next() {
                    None => return finish(version),
                    Some(Token::Dot) | Some(Token::Hyphen) => State::PreRelease,
                    Some(Token::Plus) => State::Build,
                    Some(token) => return finish_tokens(tokens.stash(token), version),
                };
            }
            State::Build => {
                // inline last state as we never change it
                loop {
                    match tokens.next() {
                        // regular build part
                        Some(Token::Alpha(v)) => {
                            version.add_build_str(v);
                        }
                        // leading zero numbers in build are alphanum
                        Some(Token::ZeroNum(v, _)) => {
                            version.add_build_str(v);
                        }
                        // regular build part
                        Some(Token::Number(v)) => {
                            version.add_build_num(v);
                        }
                        // unexpected end
                        Some(Token::Whitespace) | None => {
                            return Err(ErrorSpan::missing_build(tokens.span));
                        }
                        // any other token is invalid
                        Some(_) => {
                            return Err(ErrorSpan::unexpected(tokens.span));
                        }
                    }
                    match tokens.next() {
                        None => return finish(version),
                        Some(Token::Dot) | Some(Token::Hyphen) => {
                            // try next build token
                        }
                        Some(token) => return finish_tokens(tokens.stash(token), version),
                    };
                }
            }
        }
    }
}

fn parse_version2<'input, I, V>(tokens: I) -> Result<V::Out, ErrorSpan>
where
    I: IntoIterator<Item = TokenSpan<'input>>,
    V: VersionBuilder<'input>,
{
    let tokens = tokens.into_iter();
    let tokens = Tokens::new(tokens);
    let version = V::new();
    parse_leading_whitespace_or_v(tokens, version)
}

fn parse_version3<'input, I, V>(tokens: I) -> Result<V::Out, ErrorSpan>
where
    I: IntoIterator<Item = TokenSpan<'input>>,
    V: VersionBuilder<'input>,
{
    let tokens = tokens.into_iter();
    let tokens = Tokens::new(tokens);
    let mut version = V::new();

    let parser = Parser::new(tokens);
    for op in parser {
        match op {
            Op::Major(num) => version.set_major(num),
            Op::Minor(num) => version.set_minor(num),
            Op::Patch(num) => version.set_patch(num),
            Op::Dot4(num) => version.add_build_num(num),
            Op::PreReleaseNum(num) => version.add_pre_release_num(num),
            Op::PreRelease(v) => version.add_pre_release_str(v),
            Op::BuildNum(num) => version.add_build_num(num),
            Op::Build(v) => version.add_build_str(v),
            Op::Failed(err) => return Err(err),
        }
    }

    Ok(version.build())
}

fn parse_leading_whitespace_or_v<'input, I, V>(
    mut tokens: Tokens<'input, I>,
    version: V,
) -> Result<V::Out, ErrorSpan>
where
    I: Iterator<Item = TokenSpan<'input>>,
    V: VersionBuilder<'input>,
{
    while let Some(token) = tokens.next() {
        match token {
            // skip initial whitespace
            Token::Whitespace => {}
            // Skip leading v that is a separate token
            Token::Alpha("v") | Token::Alpha("V") => {
                return parse_leading_whitespace_with_v(tokens, version);
            }
            token => {
                return parse_major(tokens.stash(token), version, false);
            }
        }
    }
    // unexpected end
    Err(ErrorSpan::missing_part(Part::Major, tokens.span))
}

fn parse_leading_whitespace_with_v<'input, I, V>(
    mut tokens: Tokens<'input, I>,
    version: V,
) -> Result<V::Out, ErrorSpan>
where
    I: Iterator<Item = TokenSpan<'input>>,
    V: VersionBuilder<'input>,
{
    while let Some(token) = tokens.next() {
        match token {
            // skip initial whitespace
            Token::Whitespace => {}
            token => {
                return parse_major(tokens.stash(token), version, true);
            }
        }
    }
    // unexpected end
    Err(ErrorSpan::missing_part(Part::Major, tokens.span))
}

fn parse_major<'input, I, V>(
    mut tokens: Tokens<'input, I>,
    mut version: V,
    leading_v: bool,
) -> Result<V::Out, ErrorSpan>
where
    I: Iterator<Item = TokenSpan<'input>>,
    V: VersionBuilder<'input>,
{
    if let Some(token) = tokens.next() {
        let num = parse_number(token, !leading_v, Part::Major, tokens.span)?;
        version.set_major(num);
        match tokens.next() {
            None => finish(version),
            Some(Token::Dot) => parse_minor(tokens, version),
            Some(Token::Hyphen) => parse_pre_release_meta(tokens, version),
            Some(Token::Plus) => parse_build_meta(tokens, version),
            Some(token) => finish_tokens(tokens.stash(token), version),
        }
    } else {
        // unexpected end
        Err(ErrorSpan::missing_part(Part::Major, tokens.span))
    }
}

fn parse_minor<'input, I, V>(
    mut tokens: Tokens<'input, I>,
    mut version: V,
) -> Result<V::Out, ErrorSpan>
where
    I: Iterator<Item = TokenSpan<'input>>,
    V: VersionBuilder<'input>,
{
    match tokens.next() {
        // things like 1.Final, early stop with a single build identifier
        Some(Token::Alpha(v)) if is_release_identifier(v) => {
            version.add_build_str(v);
            finish_tokens(tokens, version)
        }
        // any alpha token skips right into pre-release parsing
        Some(Token::Alpha(v)) => parse_pre_release_meta(tokens.stash(Token::Alpha(v)), version),
        // unexpected end
        Some(Token::Whitespace) | None => Err(ErrorSpan::missing_part(Part::Minor, tokens.span)),
        // any other token is tried as a number
        Some(token) => {
            let num = parse_number(token, false, Part::Minor, tokens.span)?;
            version.set_minor(num);
            match tokens.next() {
                None => finish(version),
                Some(Token::Dot) => parse_patch(tokens, version),
                Some(Token::Hyphen) => parse_pre_release_meta(tokens, version),
                Some(Token::Plus) => parse_build_meta(tokens, version),
                Some(token) => finish_tokens(tokens.stash(token), version),
            }
        }
    }
}

fn parse_patch<'input, I, V>(
    mut tokens: Tokens<'input, I>,
    mut version: V,
) -> Result<V::Out, ErrorSpan>
where
    I: Iterator<Item = TokenSpan<'input>>,
    V: VersionBuilder<'input>,
{
    match tokens.next() {
        // things like 1.Final, early stop with a single build identifier
        Some(Token::Alpha(v)) if is_release_identifier(v) => {
            version.add_build_str(v);
            finish_tokens(tokens, version)
        }
        // any alpha token skips right into pre-release parsing
        Some(Token::Alpha(v)) => parse_pre_release_meta(tokens.stash(Token::Alpha(v)), version),
        // unexpected end
        Some(Token::Whitespace) | None => Err(ErrorSpan::missing_part(Part::Patch, tokens.span)),
        // any other token is tried as a number
        Some(token) => {
            let num = parse_number(token, false, Part::Patch, tokens.span)?;
            version.set_patch(num);
            match tokens.next() {
                None => finish(version),
                Some(Token::Dot) => parse_dot4_or_pre_release_meta(tokens, version),
                Some(Token::Hyphen) => parse_pre_release_meta(tokens, version),
                Some(Token::Plus) => parse_build_meta(tokens, version),
                Some(token) => finish_tokens(tokens.stash(token), version),
            }
        }
    }
}

fn parse_dot4_or_pre_release_meta<'input, I, V>(
    mut tokens: Tokens<'input, I>,
    mut version: V,
) -> Result<V::Out, ErrorSpan>
where
    I: Iterator<Item = TokenSpan<'input>>,
    V: VersionBuilder<'input>,
{
    match tokens.next() {
        // things like 1.2.3.Final, need to interpret this as a build identifier
        Some(Token::Alpha(v)) if is_release_identifier(v) => {
            version.add_build_str(v);
            return finish_tokens(tokens, version);
        }
        // regular pre-release part
        Some(Token::Alpha(v)) => {
            version.add_pre_release_str(v);
        }
        // leading zero numbers in pre-release are alphanum
        Some(Token::ZeroNum(v, _)) => {
            version.add_pre_release_str(v);
        }
        // regular pre-release part
        Some(Token::Number(v)) => {
            return parse_build_meta(tokens.stash(Token::Number(v)), version);
        }
        // unexpected end
        Some(Token::Whitespace) | None => return Err(ErrorSpan::missing_pre(tokens.span)),
        // any other token is invalid
        Some(_) => return Err(ErrorSpan::unexpected(tokens.span)),
    }
    match tokens.next() {
        None => finish(version),
        Some(Token::Dot) | Some(Token::Hyphen) => parse_pre_release_meta(tokens, version),
        Some(Token::Plus) => parse_build_meta(tokens, version),
        Some(token) => finish_tokens(tokens.stash(token), version),
    }
}

fn parse_pre_release_meta<'input, I, V>(
    mut tokens: Tokens<'input, I>,
    mut version: V,
) -> Result<V::Out, ErrorSpan>
where
    I: Iterator<Item = TokenSpan<'input>>,
    V: VersionBuilder<'input>,
{
    while let Some(token) = tokens.next() {
        match token {
            // things like 1.2.3.Final, need to interpret this as a build identifier
            Token::Alpha(v) if is_release_identifier(v) => {
                version.add_build_str(v);
                return finish_tokens(tokens, version);
            }
            // regular pre-release part
            Token::Alpha(v) => {
                version.add_pre_release_str(v);
            }
            // leading zero numbers in pre-release are alphanum
            Token::ZeroNum(v, _) => {
                version.add_pre_release_str(v);
            }
            // regular pre-release part
            Token::Number(v) => {
                version.add_pre_release_num(v);
            }
            // unexpected end
            Token::Whitespace => return Err(ErrorSpan::missing_pre(tokens.span)),
            // any other token is invalid
            _ => return Err(ErrorSpan::unexpected(tokens.span)),
        }
        match tokens.next() {
            None => return finish(version),
            Some(Token::Dot) | Some(Token::Hyphen) => {
                // try next pre-release token
            }
            Some(Token::Plus) => return parse_build_meta(tokens, version),
            Some(token) => return finish_tokens(tokens.stash(token), version),
        };
    }
    Err(ErrorSpan::missing_pre(tokens.span))
}

fn parse_build_meta<'input, I, V>(
    mut tokens: Tokens<'input, I>,
    mut version: V,
) -> Result<V::Out, ErrorSpan>
where
    I: Iterator<Item = TokenSpan<'input>>,
    V: VersionBuilder<'input>,
{
    while let Some(token) = tokens.next() {
        match token {
            // regular build part
            Token::Alpha(v) => {
                version.add_build_str(v);
            }
            // leading zero numbers in build are alphanum
            Token::ZeroNum(v, _) => {
                version.add_build_str(v);
            }
            // regular build part
            Token::Number(v) => {
                version.add_build_num(v);
            }
            // unexpected end
            Token::Whitespace => {
                return Err(ErrorSpan::missing_build(tokens.span));
            }
            // any other token is invalid
            _ => {
                return Err(ErrorSpan::unexpected(tokens.span));
            }
        }
        match tokens.next() {
            None => return finish(version),
            Some(Token::Dot) | Some(Token::Hyphen) => {
                // try next build token
            }
            Some(token) => return finish_tokens(tokens.stash(token), version),
        };
    }
    Err(ErrorSpan::missing_build(tokens.span))
}

fn parse_number(
    token: Token<'_>,
    allow_vnum: bool,
    part: Part,
    span: Span,
) -> Result<u64, ErrorSpan> {
    parse_number_inner(token, allow_vnum, part).map_err(|e| ErrorSpan::new(e, span))
}

fn parse_number_inner(token: Token<'_>, allow_vnum: bool, part: Part) -> Result<u64, ErrorType> {
    match token {
        Token::Number(n) => Ok(n),
        Token::ZeroNum(_, n) => Ok(n),
        Token::VNum(_, n) if allow_vnum => Ok(n),
        _ => Err(ErrorType::NotANumber(part)),
    }
}

fn finish_tokens<'input, I, V>(mut tokens: Tokens<'input, I>, value: V) -> Result<V::Out, ErrorSpan>
where
    I: Iterator<Item = TokenSpan<'input>>,
    V: VersionBuilder<'input>,
{
    for token in &mut tokens {
        if token != Token::Whitespace {
            return Err(ErrorSpan::unexpected(tokens.span));
        }
    }
    finish(value)
}

fn finish_tokens2<'input, I: Iterator<Item = TokenSpan<'input>>>(
    tokens: &mut Tokens<'input, I>,
) -> Result<Option<Op<'input>>, ErrorSpan> {
    while let Some(token) = tokens.next() {
        if token != Token::Whitespace {
            return Err(ErrorSpan::unexpected(tokens.span));
        }
    }
    Ok(None)
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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Span {
    start: usize,
    end: usize,
}

impl Span {
    fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }
}

impl From<Span> for Range<usize> {
    fn from(s: Span) -> Self {
        s.start..s.end
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Token<'input> {
    /// Any unicode whitespace
    Whitespace,
    /// numeric component
    Number(u64),
    /// alphanumeric component
    Alpha(&'input str),
    /// numeric component that begins with a leading zero
    ZeroNum(&'input str, u64),
    /// numeric component that begins with a leading zero
    VNum(&'input str, u64),
    /// `.`
    Dot,
    /// `+`
    Plus,
    /// `-`
    Hyphen,
    /// Error cases
    UnexpectedChar(char, usize),
}

#[derive(Debug, PartialEq, Eq)]
struct TokenSpan<'input> {
    token: Token<'input>,
    span: Span,
}

impl<'input> TokenSpan<'input> {
    fn new(start: usize, end: usize, token: Token<'input>) -> Self {
        Self {
            token,
            span: Span::new(start, end),
        }
    }
}

fn lex(input: &str) -> Lexer<'_> {
    Lexer::new(input)
}

#[derive(Debug)]
struct Lexer<'input> {
    input: &'input str,
    chars: std::str::CharIndices<'input>,
    peeked: Option<(usize, char)>,
}

impl<'input> Lexer<'input> {
    fn new(input: &'input str) -> Lexer<'input> {
        let mut chars = input.char_indices();
        let peeked = chars.next();
        Lexer {
            input,
            chars,
            peeked,
        }
    }
}

// TODO: peekable lexer, look at custom lexer docs from https://github.com/lalrpop/lalrpop or something
impl<'input> Iterator for Lexer<'input> {
    type Item = TokenSpan<'input>;

    fn next(&mut self) -> Option<Self::Item> {
        let (start, c) = self.peeked.take()?;
        if c.is_whitespace() {
            let mut end = self.input.len();
            while let Some((j, c)) = self.chars.next() {
                if !c.is_whitespace() {
                    end = j;
                    self.peeked = Some((j, c));
                    break;
                }
            }
            return Some(TokenSpan::new(start, end, Token::Whitespace));
        }
        if c.is_ascii_digit() {
            let mut end = self.input.len();
            while let Some((j, c)) = self.chars.next() {
                if c.is_alphanumeric() {
                    continue;
                }
                end = j;
                self.peeked = Some((j, c));
                break;
            }
            let number = &self.input[start..end];
            let token = match number.parse::<u64>() {
                Ok(num) => {
                    if number.len() > 1 && number.starts_with('0') {
                        Token::ZeroNum(number, num)
                    } else {
                        Token::Number(num)
                    }
                }
                Err(_) => Token::Alpha(number),
            };
            return Some(TokenSpan::new(start, end, token));
        }
        if c.is_alphanumeric() {
            let v_num = c == 'v' || c == 'V';
            let mut end = self.input.len();
            while let Some((j, c)) = self.chars.next() {
                if !c.is_alphanumeric() {
                    end = j;
                    self.peeked = Some((j, c));
                    break;
                }
            }
            let text = &self.input[start..end];
            let token = if v_num {
                match self.input[start + 1..end].parse::<u64>() {
                    Ok(num) => Token::VNum(text, num),
                    Err(_) => Token::Alpha(text),
                }
            } else {
                Token::Alpha(text)
            };
            return Some(TokenSpan::new(start, end, token));
        }
        let token = match c {
            '.' => Token::Dot,
            '-' => Token::Hyphen,
            '+' => Token::Plus,
            _ => Token::UnexpectedChar(c, start),
        };

        self.peeked = self.chars.next();
        Some(TokenSpan::new(start, start + 1, token))
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

    #[cfg(not(feature = "semver"))]
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
    #[test_case("v 2" => Ok(vers!(2 . 0 . 0)))]
    #[test_case("  v    3  " => Ok(vers!(3 . 0 . 0)))]
    #[test_case("v1.2.3" => Ok(vers!(1 . 2 . 3)))]
    #[test_case("v 1.3.3-7" => Ok(vers!(1 . 3 . 3 - 7)))]
    #[test_case("V3" => Ok(vers!(3 . 0 . 0)))]
    #[test_case("V 4" => Ok(vers!(4 . 0 . 0)))]
    #[test_case("  V    5  " => Ok(vers!(5 . 0 . 0)))]
    #[test_case("V2.3.4" => Ok(vers!(2 . 3 . 4)))]
    #[test_case("V 4.2.4-2" => Ok(vers!(4 . 2 . 4 - 2)))]
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
    #[test_case("v.1.2.3" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Major), Span::new(1, 2))))]
    #[test_case("v-2.3.4" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Major), Span::new(1, 2))))]
    #[test_case("v+3.4.5" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Major), Span::new(1, 2))))]
    #[test_case("vv1.2.3" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Major), Span::new(0, 3))))]
    #[test_case("v v1.2.3" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Major), Span::new(2, 4))))]
    #[test_case("a.b.c" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Major), Span::new(0, 1))))]
    #[test_case("1.+.0" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Minor), Span::new(2, 3))))]
    #[test_case("1.2.." => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Patch), Span::new(4, 5))))]
    #[test_case("123456789012345678901234567890" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Major), Span::new(0, 30))))]
    #[test_case("1 abc" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(2, 5))))]
    #[test_case("1.2.3 abc" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 9))))]
    fn test_simple_errors(input: &str) -> Result<Version<'_>, ErrorSpan> {
        parse_version::<_, Version<'_>>(lex(input))
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
        let tokens = lex(" v v1.2.3-1.alpha1.9+build5.7.3aedf-01337  ")
            .map(|s| s.token)
            .collect::<Vec<_>>();
        assert_eq!(
            tokens,
            vec![
                Token::Whitespace,
                Token::Alpha("v"),
                Token::Whitespace,
                Token::VNum("v1", 1),
                Token::Dot,
                Token::Number(2),
                Token::Dot,
                Token::Number(3),
                Token::Hyphen,
                Token::Number(1),
                Token::Dot,
                Token::Alpha("alpha1"),
                Token::Dot,
                Token::Number(9),
                Token::Plus,
                Token::Alpha("build5"),
                Token::Dot,
                Token::Number(7),
                Token::Dot,
                Token::Alpha("3aedf"),
                Token::Hyphen,
                Token::ZeroNum("01337", 1337),
                Token::Whitespace,
            ]
        );
    }
    #[test]
    fn test_lexer_numbers() {
        let tokens = lex("1.0.00.08.09.8.9").map(|s| s.token).collect::<Vec<_>>();
        assert_eq!(
            tokens,
            vec![
                Token::Number(1),
                Token::Dot,
                Token::Number(0),
                Token::Dot,
                Token::ZeroNum("00", 0),
                Token::Dot,
                Token::ZeroNum("08", 8),
                Token::Dot,
                Token::ZeroNum("09", 9),
                Token::Dot,
                Token::Number(8),
                Token::Dot,
                Token::Number(9),
            ]
        );
    }

    #[test]
    fn test_lexer_invalid_number() {
        let input = "123456789012345678901234567890";
        let tokens = lex(input).map(|s| s.token).collect::<Vec<_>>();
        assert_eq!(tokens, vec![Token::Alpha(input)]);
    }

    #[test]
    fn test_lexer_invalid_token() {
        let input = "!#∰~[🙈]";
        let tokens = lex(input).map(|s| s.token).collect::<Vec<_>>();
        assert_eq!(
            tokens,
            vec![
                Token::UnexpectedChar('!', 0),
                Token::UnexpectedChar('#', 1),
                Token::UnexpectedChar('∰', 2),
                Token::UnexpectedChar('~', 5),
                Token::UnexpectedChar('[', 6),
                Token::UnexpectedChar('🙈', 7),
                Token::UnexpectedChar(']', 11)
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
            Token::Whitespace,
            Token::Number(1),
            Token::Dot,
            Token::Number(2),
            Token::Dot,
            Token::Number(3),
            Token::Hyphen,
            Token::Number(1),
            Token::Dot,
            Token::Alpha("alpha1"),
            Token::Dot,
            Token::Number(9),
            Token::Plus,
            Token::Alpha("build5"),
            Token::Dot,
            Token::Number(7),
            Token::Dot,
            Token::Alpha("3aedf"),
            Token::Whitespace,
        ];

        assert_eq!(
            parse_version::<_, Version<'_>>(tokens.into_iter().map(|t| TokenSpan {
                token: t,
                span: Span::new(1, 2)
            })),
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

    #[test_case(Token::Number(42))]
    #[test_case(Token::ZeroNum("042", 42))]
    #[test_case(Token::VNum("v42", 42))]
    fn parse_version_number(token: Token<'_>) {
        assert_eq!(
            parse_number(token, true, Part::Major, Span::new(1, 2)),
            Ok(42)
        )
    }

    #[test_case((Token::Dot, Part::Patch) => Err(ErrorType::NotANumber(Part::Patch)))]
    #[test_case((Token::Plus, Part::Patch) => Err(ErrorType::NotANumber(Part::Patch)))]
    #[test_case((Token::Hyphen, Part::Patch) => Err(ErrorType::NotANumber(Part::Patch)))]
    #[test_case((Token::Whitespace, Part::Patch) => Err(ErrorType::NotANumber(Part::Patch)))]
    #[test_case((Token::Alpha("foo"), Part::Patch) => Err(ErrorType::NotANumber(Part::Patch)))]
    #[test_case((Token::UnexpectedChar('🙈', 42), Part::Patch) => Err(ErrorType::NotANumber(Part::Patch)))]
    fn parse_version_number_error(v: (Token<'_>, Part)) -> Result<u64, ErrorType> {
        let (token, part) = v;
        parse_number_inner(token, false, part)
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

    #[cfg_attr(feature = "semver", test_case("1.2.3" => parse::<Version<'_>>("1.2.3.Final"); "dot final"))]
    #[cfg_attr(feature = "semver", test_case("1.2.3" => parse::<Version<'_>>("1.2.3.Release"); "dot release"))]
    #[cfg_attr(feature = "semver", test_case("1.2.3" => parse::<Version<'_>>("1.2.3-Final"); "hyphen final"))]
    #[cfg_attr(feature = "semver", test_case("1.2.3" => parse::<Version<'_>>("1.2.3-Release"); "hyphen release"))]
    #[cfg_attr(feature = "semver", test_case("1.2.3" => parse::<Version<'_>>("1.2.3+Final"); "plus final"))]
    #[cfg_attr(feature = "semver", test_case("1.2.3" => parse::<Version<'_>>("1.2.3+Release"); "plus release"))]
    #[cfg(feature = "semver")]
    fn test_release_cmp(v: &str) -> Result<Version<'_>, Error<'_>> {
        parse::<Version<'_>>(v)
    }

    #[cfg_attr(all(feature = "semver", feature = "version_lite"), test_case("1.2.3"))]
    #[cfg_attr(
        all(feature = "semver", feature = "version_lite"),
        test_case("1.2.3-alpha01")
    )]
    #[cfg_attr(
        all(feature = "semver", feature = "version_lite"),
        test_case("1.2.3+build02")
    )]
    #[cfg_attr(
        all(feature = "semver", feature = "version_lite"),
        test_case("1.2.3-beta03+r4")
    )]
    #[cfg(all(feature = "semver", feature = "version_lite"))]
    fn test_semver_and_lite(v: &str) {
        let sem = parse::<SemVer>(v).unwrap();
        let lite = parse::<VersionLite<'_>>(v).unwrap();
        let sem_from_lite = SemVer::from(lite);
        assert_eq!(sem, sem_from_lite);
    }

    #[cfg_attr(feature = "semver", test)]
    #[cfg(feature = "semver")]
    fn test_regex() {
        use regex::Regex;

        let semver_re = r"^\s*(?P<major>0|[1-9]\d*)\.(?P<minor>0|[1-9]\d*)\.(?P<patch>0|[1-9]\d*)(?:-(?P<prerelease>(?:0|[1-9]\d*|\d*[a-zA-Z-][0-9a-zA-Z-]*)(?:\.(?:0|[1-9]\d*|\d*[a-zA-Z-][0-9a-zA-Z-]*))*))?(?:\+(?P<buildmetadata>[0-9a-zA-Z-]+(?:\.[0-9a-zA-Z-]+)*))?\s*$";
        let re = Regex::new(semver_re).unwrap();
        let text = "  1.2.3-1.alpha1.9+build5.7.3aedf.01337  ";
        let caps = re.captures(text).unwrap();

        let mut version = Version::new(
            caps.name("major").unwrap().as_str().parse().unwrap(),
            caps.name("minor").unwrap().as_str().parse().unwrap(),
            caps.name("patch").unwrap().as_str().parse().unwrap(),
        );

        fn parse_id(v: &str) -> Identifier {
            match v.parse::<u64>() {
                Ok(n) => {
                    if v.len() > 1 && v.starts_with('0') {
                        Identifier::AlphaNumeric(v.into())
                    } else {
                        Identifier::Numeric(n)
                    }
                }
                Err(_) => Identifier::AlphaNumeric(v.into()),
            }
        }

        if let Some(pre) = caps.name("prerelease") {
            let pre = pre.as_str().split('.').map(parse_id).collect::<Vec<_>>();
            version.pre = pre;
        }
        if let Some(build) = caps.name("buildmetadata") {
            let build = build.as_str().split('.').map(parse_id).collect::<Vec<_>>();
            version.build = build;
        }

        let expected = parse::<SemVer>(text).unwrap();

        assert_eq!(version.to_string(), expected.to_string());
    }
}
