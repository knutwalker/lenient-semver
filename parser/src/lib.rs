//! Lenient parser for Semantic Version numbers.
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
///
/// This parser does not require semver-specification conformant input and is more lenient in what it allows.
/// The differenc include:
///
/// - Minor and Path are optional an default to 0 (e.g. "1" parses as "1.0.0")
/// - Pre-release identifier may be separated by `.` as well (e.g. "1.2.3.rc1" parses as "1.2.3-rc1")
/// - Some pre-release identifiers are parsed as build identifier (e.g. "1.2.3.Final" parses as "1.2.3+Final")
/// - Additional numeric identifiers are parsed as build identifier (e.g "1.2.3.4.5" parses as "1.2.3+4.5")
/// - A leading `v` or `V` is allowed (e.g. "v1.2.3" parses as "1.2.3")
/// - Numbers that overflow an u64 are treated as strings (e.g. "1.2.3-9876543210987654321098765432109876543210" parses without error)
///
/// This diagram shows lenient parsing grammar
///
/// ![have a look at doc/railroad.svg](https://knutwalker.s3.eu-central-1.amazonaws.com/lenient-semver/doc/railroad.svg)
///
/// ## Examples
///
/// ```rust
/// use semver::Version;
///
/// let version = lenient_semver_parser::parse::<Version>("1.2.3");
/// assert_eq!(version, Ok(Version::new(1, 2, 3)));
///
/// // examples of a version that would not be accepted by semver_parser
/// assert_eq!(
///     lenient_semver_parser::parse::<Version>("1.2.M1").unwrap(),
///     Version::parse("1.2.0-M1").unwrap()
/// );
/// assert!(Version::parse("1.2.M1").is_err());
///
/// assert_eq!(
///     lenient_semver_parser::parse::<Version>("1").unwrap(),
///     Version::parse("1.0.0").unwrap()
/// );
/// assert!(Version::parse("1").is_err());
///
/// assert_eq!(
///     lenient_semver_parser::parse::<Version>("1.2.3.Final").unwrap(),
///     Version::parse("1.2.3+Final").unwrap()
/// );
/// assert!(Version::parse("1.2.3.Final").is_err());
///
/// assert_eq!(
///     lenient_semver_parser::parse::<Version>("1.2.3.4.5").unwrap(),
///     Version::parse("1.2.3+4.5").unwrap()
/// );
/// assert!(Version::parse("1.2.3.4.5").is_err());
///
/// assert_eq!(
///     lenient_semver_parser::parse::<Version>("v1.2.3").unwrap(),
///     Version::parse("1.2.3").unwrap()
/// );
/// assert!(Version::parse("v1.2.3").is_err());
///
/// assert_eq!(
///     lenient_semver_parser::parse::<Version>("1.2.9876543210987654321098765432109876543210").unwrap(),
///     Version::parse("1.2.0-9876543210987654321098765432109876543210").unwrap()
/// );
/// assert!(Version::parse("1.2.9876543210987654321098765432109876543210").is_err());
/// ```
pub fn parse<'input, V>(input: &'input str) -> Result<V::Out, Error<'input>>
where
    V: VersionBuilder<'input>,
{
    parse_internal::<V>(input).map_err(|ErrorSpan { error, span }| Error { input, span, error })
}

/// Trait to abstract over version building.
///
/// The methods to implement in this trait represent the components of [`semver::Version`],
/// but allow for parsing into a custom type.
///
/// The trait is generic over the lifetime of the input string, so that one could
/// parse into a version without having to allocate.
///
/// Most methods have a default implementation that does nothing and ignores the input.
/// This can be used to implement some form of validation without needing to keep the result.
///
/// ## Example
///
/// ```rust
/// # use lenient_semver_parser::VersionBuilder;
///
/// struct IsPreRelease(bool);
///
/// impl<'input> VersionBuilder<'input> for IsPreRelease {
///     type Out = bool;
///
///     fn new() -> Self {
///        IsPreRelease(false)
///     }
///
///     fn add_pre_release(&mut self, _input: &'input str) {
///         self.0 = true;
///     }
///
///     fn build(self) -> Self::Out {
///         self.0
///     }
/// }
///
/// fn is_pre_release(v: &str) -> bool {
///     lenient_semver_parser::parse::<IsPreRelease>(v).unwrap_or_default()
/// }
///
/// assert!(is_pre_release("1.2.3-pre"));
/// assert!(!is_pre_release("1.2.3"));
/// assert!(!is_pre_release("1.2.3+build"));
/// ```
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
    #[allow(unused)]
    fn set_major(&mut self, major: u64) {}

    /// Set the minor version component.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    #[allow(unused)]
    fn set_minor(&mut self, minor: u64) {}

    /// Set the patch version component.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    #[allow(unused)]
    fn set_patch(&mut self, patch: u64) {}

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
    #[allow(unused)]
    fn add_additional(&mut self, num: u64) {}

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
    #[allow(unused)]
    fn add_pre_release(&mut self, pre_release: &'input str) {}

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
    #[allow(unused)]
    fn add_build(&mut self, build: &'input str) {}

    /// Construct the final version.
    fn build(self) -> Self::Out;
}

#[cfg(any(test, feature = "semver", feature = "semver10",))]
fn try_num(s: &str) -> Result<u64, &str> {
    match s.parse::<u64>() {
        Ok(num) if !s.starts_with("0") || s == "0" => Ok(num),
        _ => Err(s),
    }
}

#[cfg(any(test, feature = "semver"))]
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

#[cfg(any(test, feature = "semver"))]
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

/// Possible errors that happen during parsing
/// and the location of the token where the error occurred.
///
/// # Example
///
/// ```rust
/// use semver::Version;
///
/// let error = lenient_semver_parser::parse::<Version>("1+").unwrap_err();
/// assert_eq!(error.to_string(), "Could not parse the build identifier: No input");
///
/// let error = lenient_semver_parser::parse::<Version>("1!").unwrap_err();
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
    /// let error = lenient_semver_parser::parse::<semver::Version>("1+").unwrap_err();
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
    /// let error = lenient_semver_parser::parse::<semver::Version>("1!").unwrap_err();
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
    ///     lenient_semver_parser::parse::<semver::Version>("").unwrap_err().error_kind(),
    ///     lenient_semver_parser::ErrorKind::MissingMajorNumber
    /// );
    /// assert_eq!(
    ///     lenient_semver_parser::parse::<semver::Version>("1.").unwrap_err().error_kind(),
    ///     lenient_semver_parser::ErrorKind::MissingMinorNumber
    /// );
    /// assert_eq!(
    ///     lenient_semver_parser::parse::<semver::Version>("1.2.").unwrap_err().error_kind(),
    ///     lenient_semver_parser::ErrorKind::MissingPatchNumber
    /// );
    /// assert_eq!(
    ///     lenient_semver_parser::parse::<semver::Version>("1-").unwrap_err().error_kind(),
    ///     lenient_semver_parser::ErrorKind::MissingPreRelease
    /// );
    /// assert_eq!(
    ///     lenient_semver_parser::parse::<semver::Version>("1+").unwrap_err().error_kind(),
    ///     lenient_semver_parser::ErrorKind::MissingBuild
    /// );
    /// assert_eq!(
    ///     lenient_semver_parser::parse::<semver::Version>("1!").unwrap_err().error_kind(),
    ///     lenient_semver_parser::ErrorKind::UnexpectedInput
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
            ErrorType::MajorNotNumeric => ErrorKind::MajorNotANumber,
            ErrorType::Unexpected => ErrorKind::UnexpectedInput,
        }
    }

    /// Returns a slice from the original input line that triggered the error.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let error = lenient_semver_parser::parse::<semver::Version>("1!").unwrap_err();
    /// assert_eq!(error.erroneous_input(), "!");
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
    /// let error = lenient_semver_parser::parse::<semver::Version>("1.").unwrap_err();
    /// assert_eq!(error.error_line(), String::from("Could not parse the minor identifier: No input"));
    /// ```
    ///
    /// This is equivalent to the [`Display`] implementation, which can be further customized with format specifiers.
    ///
    /// ```rust
    /// let error = lenient_semver_parser::parse::<semver::Version>("1?").unwrap_err();
    /// assert_eq!(format!("{:!^42}", error), String::from("!!!!!!!!!!!!!!Unexpected `?`!!!!!!!!!!!!!!"));
    /// ```
    pub fn error_line(&self) -> String {
        match &self.error {
            ErrorType::Missing(segment) => {
                format!("Could not parse the {} identifier: No input", segment)
            }
            ErrorType::MajorNotNumeric => format!(
                "Could not parse the major identifier: `{}` is not a number",
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
    /// let error = lenient_semver_parser::parse::<semver::Version>("foo").unwrap_err();
    /// assert_eq!(error.indicate_erroneous_input(), "^");
    ///
    /// let error = lenient_semver_parser::parse::<semver::Version>("1.2.3 bar").unwrap_err();
    /// assert_eq!(error.indicate_erroneous_input(), "~~~~~~^");
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

impl PartialOrd for Error<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.error.partial_cmp(&other.error)
    }
}

impl Ord for Error<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.error.cmp(&other.error)
    }
}

#[derive(Debug, PartialEq, Eq)]
struct ErrorSpan {
    error: ErrorType,
    span: Span,
}

impl ErrorSpan {
    fn new(error: ErrorType, span: Span) -> Self {
        Self { error, span }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum ErrorType {
    Missing(Segment),
    MajorNotNumeric,
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

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq)]
struct Span {
    start: u8,
    end: u8,
}

impl Span {
    fn new(start: u8, end: u8) -> Self {
        Self { start, end }
    }
}

impl From<Span> for Range<usize> {
    fn from(s: Span) -> Self {
        s.start as usize..s.end as usize
    }
}

fn is_release_identifier(v: &str) -> bool {
    v == "r" || eq_bytes_ignore_case(v, "final") || eq_bytes_ignore_case(v, "release")
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

/// This constant maps the first 5 bits of a code unit to the one less than the length in utf-8.
/// There are 32 possible values for the first 5 bits. The length in utf-8 is in [1, 4].
/// Subtracting 1 gives us [0, 3], which can be encoded in 2 bits.
/// The utf-8 length for a given byte can be determined by looking at the first 5 bits and all the
/// lengths are packed into this constant.
///
/// 1. `byte >> 3`   produces to first 5 bits: `000xxxxx`
/// 2. `_ << 1`      multiply by 2 as the length is encoded with 2 bits
/// 3. `MAGIC >> _`  selects the cooresponding length "entry"
/// 4. `_ & 0b11`    retains only the last two bits
/// 5. `_ + 1`       returns the actual length in [1, 4]
const MAGIC: u64 = 0x3A55000000000000;
const fn utf8_len(input: u8) -> usize {
    ((MAGIC >> ((input >> 3) << 1)) & 0b11) as usize + 1
}

const STATES: usize = 15;

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
#[repr(u8)]
enum State {
    ExpectMajor,
    ParseMajor,
    ExpectMinor,
    ParseMinor,
    ExpectPatch,
    ParsePatch,
    ExpectAdd,
    ParseAdd,
    ExpectPre,
    ParsePre,
    ExpectBuild,
    ParseBuild,
    RequireMajor,
    EndOfInput,
    Error,
}

impl Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.pad(&format!("{:?}", self))
    }
}

const CLASSES: usize = 9;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
enum Class {
    Number,
    Alpha,
    Dot,
    Hyphen,
    Plus,
    V,
    Whitespace,
    EndOfInput,
    Unexpected,
}

impl Display for Class {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Class::Number => f.pad("[0-9]"),
            Class::Alpha => f.pad("[a-zA-Z]"),
            Class::Dot => f.pad("[.]"),
            Class::Hyphen => f.pad("[-]"),
            Class::Plus => f.pad("[+]"),
            Class::V => f.pad("[vV]"),
            Class::Whitespace => f.pad("<whitespace>"),
            Class::EndOfInput => f.pad("EOI"),
            Class::Unexpected => f.pad("<otherwise>"),
        }
    }
}

const EMITS: usize = 14;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(u8)]
enum Emit {
    None,
    SaveStart,
    Major,
    Minor,
    Patch,
    Add,
    Pre,
    Build,
    ErrorMissingMajor,
    ErrorMissingMinor,
    ErrorMissingPatch,
    ErrorMissingPre,
    ErrorMissingBuild,
    ErrorUnexpected,
}

type Lookup = [Class; 256];

const fn class_lookup() -> Lookup {
    let error_class = Class::Unexpected;
    let mut table = [error_class; 256];
    let mut c = 0_usize;
    while c <= 0xFF {
        let class = match c as u8 as char {
            '.' => Class::Dot,
            '-' => Class::Hyphen,
            '+' => Class::Plus,
            'v' | 'V' => Class::V,
            '0'..='9' => Class::Number,
            'A'..='Z' | 'a'..='z' => Class::Alpha,
            '\t' | '\n' | '\x0C' | '\r' | ' ' => Class::Whitespace,
            _ => Class::Unexpected,
        };
        table[c] = class;
        c += 1;
    }
    table
}

#[inline(always)]
const fn dfa_index(s: State, c: Class) -> u8 {
    (s as u8) * (CLASSES as u8) + (c as u8)
}

macro_rules! dfa {
        ($transitions:ident: $($cls:ident @ $state:ident -> $target:ident),+,) => {
            $($transitions[dfa_index(State::$state, Class::$cls) as usize] = State::$target;)+
        };
    }

macro_rules! emit {
        ($emits:ident: $($($cls:ident)|+ @ $state:ident -> $emit:ident),+,) => {
            $(
                $(
                    $emits[dfa_index(State::$state, Class::$cls) as usize] = Emit::$emit;
                )+
            )+
        };
    }

type Dfa = ([State; STATES * CLASSES], [Emit; STATES * CLASSES]);

const fn dfa() -> Dfa {
    let mut transitions = [State::Error; STATES * CLASSES];
    dfa!(transitions:

    Whitespace @ ExpectMajor  -> ExpectMajor,
             V @ ExpectMajor  -> RequireMajor,
        Number @ ExpectMajor  -> ParseMajor,

        Number @ RequireMajor -> ParseMajor,

    EndOfInput @ ParseMajor   -> EndOfInput,
    Whitespace @ ParseMajor   -> EndOfInput,
        Number @ ParseMajor   -> ParseMajor,
           Dot @ ParseMajor   -> ExpectMinor,
        Hyphen @ ParseMajor   -> ExpectPre,
          Plus @ ParseMajor   -> ExpectBuild,


        Number @ ExpectMinor  -> ParseMinor,
             V @ ExpectMinor  -> ParsePre,
         Alpha @ ExpectMinor  -> ParsePre,

    EndOfInput @ ParseMinor   -> EndOfInput,
    Whitespace @ ParseMinor   -> EndOfInput,
        Number @ ParseMinor   -> ParseMinor,
             V @ ParseMinor   -> ParsePre,
         Alpha @ ParseMinor   -> ParsePre,
           Dot @ ParseMinor   -> ExpectPatch,
        Hyphen @ ParseMinor   -> ExpectPre,
          Plus @ ParseMinor   -> ExpectBuild,


        Number @ ExpectPatch  -> ParsePatch,
             V @ ExpectPatch  -> ParsePre,
         Alpha @ ExpectPatch  -> ParsePre,

    EndOfInput @ ParsePatch   -> EndOfInput,
    Whitespace @ ParsePatch   -> EndOfInput,
        Number @ ParsePatch   -> ParsePatch,
             V @ ParsePatch   -> ParsePre,
         Alpha @ ParsePatch   -> ParsePre,
           Dot @ ParsePatch   -> ExpectAdd,
        Hyphen @ ParsePatch   -> ExpectPre,
          Plus @ ParsePatch   -> ExpectBuild,


        Number @ ExpectAdd    -> ParseAdd,
             V @ ExpectAdd    -> ParsePre,
         Alpha @ ExpectAdd    -> ParsePre,

    EndOfInput @ ParseAdd     -> EndOfInput,
    Whitespace @ ParseAdd     -> EndOfInput,
        Number @ ParseAdd     -> ParseAdd,
             V @ ParseAdd     -> ParsePre,
         Alpha @ ParseAdd     -> ParsePre,
           Dot @ ParseAdd     -> ExpectAdd,
        Hyphen @ ParseAdd     -> ExpectPre,
          Plus @ ParseAdd     -> ExpectBuild,


        Number @ ExpectPre    -> ParsePre,
             V @ ExpectPre    -> ParsePre,
         Alpha @ ExpectPre    -> ParsePre,

    EndOfInput @ ParsePre     -> EndOfInput,
    Whitespace @ ParsePre     -> EndOfInput,
        Number @ ParsePre     -> ParsePre,
             V @ ParsePre     -> ParsePre,
         Alpha @ ParsePre     -> ParsePre,
           Dot @ ParsePre     -> ExpectPre,
        Hyphen @ ParsePre     -> ExpectPre,
          Plus @ ParsePre     -> ExpectBuild,


        Number @ ExpectBuild  -> ParseBuild,
             V @ ExpectBuild  -> ParseBuild,
         Alpha @ ExpectBuild  -> ParseBuild,

    EndOfInput @ ParseBuild   -> EndOfInput,
    Whitespace @ ParseBuild   -> EndOfInput,
        Number @ ParseBuild   -> ParseBuild,
             V @ ParseBuild   -> ParseBuild,
         Alpha @ ParseBuild   -> ParseBuild,
           Dot @ ParseBuild   -> ExpectBuild,
        Hyphen @ ParseBuild   -> ExpectBuild,


    EndOfInput @ EndOfInput   -> EndOfInput,
    Whitespace @ EndOfInput   -> EndOfInput,
    );

    let mut emits = [Emit::None; STATES * CLASSES];
    emit!(emits:
        Number @ ExpectMajor  -> SaveStart,
    EndOfInput @ ExpectMajor  -> ErrorMissingMajor,
    Alpha | Dot | Hyphen | Plus | Unexpected
               @ ExpectMajor  -> ErrorUnexpected,

        Number @ RequireMajor -> SaveStart,
    EndOfInput @ RequireMajor -> ErrorMissingMajor,
    Whitespace | Alpha | V | Dot | Hyphen | Plus | Unexpected
               @ RequireMajor -> ErrorUnexpected,

    Whitespace | EndOfInput | Dot | Hyphen | Plus
               @ ParseMajor   -> Major,
    Alpha | V | Unexpected
               @ ParseMajor   -> ErrorUnexpected,

    Number | V | Alpha
               @ ExpectMinor  -> SaveStart,
    EndOfInput @ ExpectMinor  -> ErrorMissingMinor,
    Whitespace | Dot | Hyphen | Plus | Unexpected
               @ ExpectMinor  -> ErrorUnexpected,

    Whitespace | EndOfInput | Dot | Hyphen | Plus
               @ ParseMinor   -> Minor,
    Unexpected @ ParseMinor   -> ErrorUnexpected,

    Number | V | Alpha
               @ ExpectPatch  -> SaveStart,
    EndOfInput @ ExpectPatch  -> ErrorMissingPatch,
    Whitespace | Dot | Hyphen | Plus | Unexpected
               @ ExpectPatch  -> ErrorUnexpected,

    Whitespace | EndOfInput | Dot | Hyphen | Plus
               @ ParsePatch   -> Patch,
    Unexpected @ ParsePatch   -> ErrorUnexpected,

    Number | V | Alpha
               @ ExpectAdd    -> SaveStart,
    EndOfInput @ ExpectAdd    -> ErrorMissingPre,
    Whitespace | Dot | Hyphen | Plus | Unexpected
               @ ExpectAdd    -> ErrorUnexpected,

    Whitespace | EndOfInput | Dot | Hyphen | Plus
               @ ParseAdd     -> Add,
    Unexpected @ ParseAdd     -> ErrorUnexpected,

    Number | V | Alpha
               @ ExpectPre    -> SaveStart,
    EndOfInput @ ExpectPre    -> ErrorMissingPre,
    Whitespace | Dot | Hyphen | Plus | Unexpected
               @ ExpectPre    -> ErrorUnexpected,

    Whitespace | EndOfInput | Dot | Hyphen | Plus
               @ ParsePre     -> Pre,
    Unexpected @ ParsePre     -> ErrorUnexpected,

    Number | V | Alpha
               @ ExpectBuild  -> SaveStart,
    EndOfInput @ ExpectBuild  -> ErrorMissingBuild,
    Whitespace | Dot | Hyphen | Plus | Unexpected
               @ ExpectBuild  -> ErrorUnexpected,

    Whitespace | EndOfInput | Dot | Hyphen | Plus
               @ ParseBuild   -> Build,
    Unexpected @ ParseBuild   -> ErrorUnexpected,

    Alpha | V | Number | Dot | Hyphen | Plus | Unexpected
               @ EndOfInput   -> ErrorUnexpected,
    );

    (transitions, emits)
}

static LOOKUP: Lookup = class_lookup();
static DFA: Dfa = dfa();

#[inline(always)]
const fn transduce(class_lookup: &Lookup, dfa: &Dfa, s: State, b: u8) -> (State, Emit) {
    transition(dfa, s, class_lookup[b as usize])
}

#[inline(always)]
const fn transition(dfa: &Dfa, s: State, class: Class) -> (State, Emit) {
    let index = dfa_index(s, class) as usize;
    (dfa.0[index], dfa.1[index])
}

fn do_nothing<'input, V>(
    _input: &'input str,
    _v: &mut V,
    _start: &mut usize,
    _new_state: &mut State,
    _index: usize,
) -> Result<(), ErrorSpan>
where
    V: VersionBuilder<'input>,
{
    Ok(())
}

fn save_start<'input, V>(
    _input: &'input str,
    _v: &mut V,
    start: &mut usize,
    _new_state: &mut State,
    index: usize,
) -> Result<(), ErrorSpan>
where
    V: VersionBuilder<'input>,
{
    *start = index;
    Ok(())
}

fn parse_major<'input, V>(
    input: &'input str,
    v: &mut V,
    start: &mut usize,
    _new_state: &mut State,
    index: usize,
) -> Result<(), ErrorSpan>
where
    V: VersionBuilder<'input>,
{
    match input[*start..index].parse::<u64>() {
        Ok(num) => {
            v.set_major(num);
            Ok(())
        }
        _ => Err(ErrorSpan::new(
            ErrorType::MajorNotNumeric,
            Span::new(*start as u8, index as u8),
        )),
    }
}

fn parse_minor<'input, V>(
    input: &'input str,
    v: &mut V,
    start: &mut usize,
    new_state: &mut State,
    index: usize,
) -> Result<(), ErrorSpan>
where
    V: VersionBuilder<'input>,
{
    let segment = &input[*start..index];
    match segment.parse::<u64>() {
        Ok(num) => v.set_minor(num),
        _ => {
            v.add_pre_release(segment);
            if *new_state < State::ExpectPre {
                *new_state = State::ExpectPre;
            }
        }
    };
    Ok(())
}

fn parse_patch<'input, V>(
    input: &'input str,
    v: &mut V,
    start: &mut usize,
    new_state: &mut State,
    index: usize,
) -> Result<(), ErrorSpan>
where
    V: VersionBuilder<'input>,
{
    let segment = &input[*start..index];
    match segment.parse::<u64>() {
        Ok(num) => v.set_patch(num),
        _ => {
            v.add_pre_release(segment);
            if *new_state < State::ExpectPre {
                *new_state = State::ExpectPre;
            }
        }
    };
    Ok(())
}

fn parse_add<'input, V>(
    input: &'input str,
    v: &mut V,
    start: &mut usize,
    new_state: &mut State,
    index: usize,
) -> Result<(), ErrorSpan>
where
    V: VersionBuilder<'input>,
{
    let segment = &input[*start..index];
    match segment.parse::<u64>() {
        Ok(num) => v.add_additional(num),
        _ => {
            v.add_pre_release(segment);
            if *new_state < State::ExpectPre {
                *new_state = State::ExpectPre;
            }
        }
    };
    Ok(())
}

fn parse_pre_release<'input, V>(
    input: &'input str,
    v: &mut V,
    start: &mut usize,
    new_state: &mut State,
    index: usize,
) -> Result<(), ErrorSpan>
where
    V: VersionBuilder<'input>,
{
    let segment = &input[*start..index];
    if is_release_identifier(segment) {
        if *new_state < State::EndOfInput {
            return error_unexpected(input, v, start, new_state, index);
        }
        v.add_build(segment);
    } else {
        v.add_pre_release(segment);
    }

    Ok(())
}

fn parse_build<'input, V>(
    input: &'input str,
    v: &mut V,
    start: &mut usize,
    _new_state: &mut State,
    index: usize,
) -> Result<(), ErrorSpan>
where
    V: VersionBuilder<'input>,
{
    v.add_build(&input[*start..index]);
    Ok(())
}

fn error_missing_major<'input, V>(
    input: &'input str,
    _v: &mut V,
    _start: &mut usize,
    _new_state: &mut State,
    index: usize,
) -> Result<(), ErrorSpan>
where
    V: VersionBuilder<'input>,
{
    error_missing(Segment::Part(Part::Major), input, index)
}

fn error_missing_minor<'input, V>(
    input: &'input str,
    _v: &mut V,
    _start: &mut usize,
    _new_state: &mut State,
    index: usize,
) -> Result<(), ErrorSpan>
where
    V: VersionBuilder<'input>,
{
    error_missing(Segment::Part(Part::Minor), input, index)
}

fn error_missing_patch<'input, V>(
    input: &'input str,
    _v: &mut V,
    _start: &mut usize,
    _new_state: &mut State,
    index: usize,
) -> Result<(), ErrorSpan>
where
    V: VersionBuilder<'input>,
{
    error_missing(Segment::Part(Part::Patch), input, index)
}

fn error_missing_pre<'input, V>(
    input: &'input str,
    _v: &mut V,
    _start: &mut usize,
    _new_state: &mut State,
    index: usize,
) -> Result<(), ErrorSpan>
where
    V: VersionBuilder<'input>,
{
    error_missing(Segment::PreRelease, input, index)
}

fn error_missing_build<'input, V>(
    input: &'input str,
    _v: &mut V,
    _start: &mut usize,
    _new_state: &mut State,
    index: usize,
) -> Result<(), ErrorSpan>
where
    V: VersionBuilder<'input>,
{
    error_missing(Segment::Build, input, index)
}

fn error_missing(segment: Segment, input: &str, index: usize) -> Result<(), ErrorSpan> {
    let span = if index < input.len() {
        span_from(input, index)
    } else {
        Span::new(index as u8, index as u8)
    };
    Err(ErrorSpan::new(ErrorType::Missing(segment), span))
}

fn error_unexpected<'input, V>(
    input: &'input str,
    _v: &mut V,
    _start: &mut usize,
    _new_state: &mut State,
    index: usize,
) -> Result<(), ErrorSpan>
where
    V: VersionBuilder<'input>,
{
    Err(ErrorSpan::new(
        ErrorType::Unexpected,
        span_from(input, index),
    ))
}

#[inline]
fn span_from(input: &str, index: usize) -> Span {
    Span::new(
        index as u8,
        (index + utf8_len(input.as_bytes()[index])) as u8,
    )
}

fn parse_internal<'input, V>(input: &'input str) -> Result<V::Out, ErrorSpan>
where
    V: VersionBuilder<'input>,
{
    let actions: [for<'local> fn(
        &'input str,
        &'local mut V,
        &'local mut usize,
        &'local mut State,
        usize,
    ) -> Result<(), ErrorSpan>; EMITS] = [
        do_nothing,
        save_start,
        parse_major,
        parse_minor,
        parse_patch,
        parse_add,
        parse_pre_release,
        parse_build,
        error_missing_major,
        error_missing_minor,
        error_missing_patch,
        error_missing_pre,
        error_missing_build,
        error_unexpected,
    ];
    let mut start = 0_usize;
    let mut v = V::new();
    let mut state = State::ExpectMajor;

    let mut_v = &mut v;
    let mut_s = &mut start;
    for (index, b) in input.bytes().enumerate() {
        let (mut new_state, emits) = transduce(&LOOKUP, &DFA, state, b);
        (actions[emits as u8 as usize])(input, mut_v, mut_s, &mut new_state, index)?;
        state = new_state;
    }
    let (mut new_state, emits) = transition(&DFA, state, Class::EndOfInput);
    (actions[emits as u8 as usize])(input, mut_v, mut_s, &mut new_state, input.len())?;
    Ok(v.build())
}

/// for benchmarks
#[cfg(feature = "generator")]
pub mod generator {
    #[cfg(test)]
    use std::collections::HashMap;

    use super::*;

    /// for benchmarks
    // woudl be const fn but need to inc #[const_eval_limit]
    pub fn generate_20000(seed: u32) -> [u8; 20_000] {
        let classes = [
            Class::Number,
            Class::Alpha,
            Class::Dot,
            Class::Hyphen,
            Class::Plus,
            Class::V,
        ];
        let dfa = dfa();

        let mut seed = if seed == 0 { 0xBAD_5EED } else { seed };
        let mut state = State::ExpectMajor;
        let mut candidates = [Class::Whitespace; 6];

        let mut result = [0x20_u8; 20_000];
        let size = 20_000_usize;
        let mut index = 0_usize;
        while index < size {
            let mut cls = 0;
            let mut num_candidates = 0;
            while cls < classes.len() {
                let possible_state = transition(&dfa, state, classes[cls]).0;
                if possible_state as u8 != State::Error as u8 {
                    candidates[num_candidates] = classes[cls];
                    num_candidates += 1;
                }
                cls += 1;
            }
            let (new_seed, candidate) = roll(seed, num_candidates);
            let candidate = candidates[candidate];
            let (new_seed, ch) = char_for(new_seed, candidate);
            seed = new_seed;
            state = transition(&dfa, state, candidate).0;
            result[index] = ch;
            index += 1;
        }

        result
    }

    const fn char_for(seed: u32, class: Class) -> (u32, u8) {
        match class {
            Class::Number => {
                let (seed, number) = roll(seed, 10);
                (seed, b'0' + number as u8)
            }
            Class::Alpha => {
                let (seed, use_upper) = roll(seed, 2);
                let (seed, number) = roll(seed, 26);
                let start = if use_upper == 0 { b'a' } else { b'A' };
                (seed, start + number as u8)
            }
            Class::Dot => (seed, b'.'),
            Class::Hyphen => (seed, b'-'),
            Class::Plus => (seed, b'+'),
            Class::V => {
                let (seed, use_upper) = roll(seed, 2);
                let value = if use_upper == 0 { b'v' } else { b'V' };
                (seed, value)
            }
            Class::Whitespace | Class::EndOfInput | Class::Unexpected => (seed, b' '),
        }
    }

    const fn roll(seed: u32, upper: usize) -> (u32, usize) {
        let x = seed;
        let x = x ^ x.wrapping_shl(13);
        let x = x ^ x.wrapping_shr(17);
        let x = x ^ x.wrapping_shl(5);
        (x, x as usize % upper)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_case::test_case;

    #[cfg(feature = "semver")]
    #[cfg_attr(feature = "semver", test)]
    fn test_parse_semver() {
        let actual = parse::<Version>("   v1.2.3.4.5-Foo-bar+baz-qux  ").ok();
        let expected = semver::Version::parse("1.2.3-Foo.bar+4.5.baz.qux").ok();
        assert_eq!(actual, expected)
    }

    #[cfg(feature = "semver10")]
    #[cfg_attr(feature = "semver10", test)]
    fn test_parse_semver10() {
        let actual = parse::<semver10::Version>("   v1.2.3.4.5-Foo-bar+baz-qux  ").ok();
        let expected = semver10::Version::parse("1.2.3-Foo.bar+4.5.baz.qux").ok();
        assert_eq!(actual, expected)
    }

    mod semver_helpers {
        pub(super) use semver::{Identifier, Version};

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
    fn test_simple(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
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
    #[test_case("5.9.0-202009080501-r" => Ok(vers!(5 . 9 . 0 - 202009080501 + "r")))]
    #[test_case("1.2.3.RC.4" => Ok(vers!(1 . 2 . 3 - "RC" - 4)))]
    fn test_pre_release(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
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
    fn test_build(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
    }

    #[test_case("1.3.3.7" => Ok(vers!(1 . 3 . 3 + 7)))]
    #[test_case("1.3.3.0" => Ok(vers!(1 . 3 . 3 + 0)))]
    #[test_case("1.3.3.00" => Ok(vers!(1 . 3 . 3 + 0)))]
    #[test_case("1.3.3.07" => Ok(vers!(1 . 3 . 3 + 7)))]
    #[test_case("1.3.3.7.4.2" => Ok(vers!(1 . 3 . 3 + 7 - 4 - 2)))]
    #[test_case("1.3.3.7.04.02" => Ok(vers!(1 . 3 . 3 + 7 - 4 - 2)))]
    #[test_case("1.3.3.9876543210987654321098765432109876543210" => Ok(vers!(1 . 3 . 3 - "9876543210987654321098765432109876543210")))]
    #[test_case("1.3.3.9876543210987654321098765432109876543210.4.2" => Ok(vers!(1 . 3 . 3 - "9876543210987654321098765432109876543210" - 4 - 2)))]
    #[test_case("1.3.3.7.foo" => Ok(vers!(1 . 3 . 3 - "foo" + 7)))]
    #[test_case("1.3.3.7-bar" => Ok(vers!(1 . 3 . 3 - "bar" + 7)))]
    #[test_case("1.3.3.7+baz" => Ok(vers!(1 . 3 . 3 + 7 - "baz")))]
    fn test_additional_numbers(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
    }

    #[test_case("1.2.3-alpha1+build5" => Ok(vers!(1 . 2 . 3 - "alpha1" + "build5" )))]
    #[test_case("   1.2.3-alpha2+build6   " => Ok(vers!(1 . 2 . 3 - "alpha2" + "build6" )))]
    #[test_case("1.2.3-1.alpha1.9+build5.7.3aedf  " => Ok(vers!(1 . 2 . 3 - 1 - "alpha1" - 9 + "build5" - 7 - "3aedf" )))]
    #[test_case("0.4.0-beta.1+0851523" => Ok(vers!(0 . 4 . 0 - "beta" - 1 + "0851523" )))]
    fn test_combined(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
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
    #[test_case("2.7.3.r" => Ok(vers!(2 . 7 . 3 + "r" )); "full dot r")]
    #[test_case("2.7.3-r" => Ok(vers!(2 . 7 . 3 + "r" )); "full hyphen r")]
    #[test_case("2.7.3+r" => Ok(vers!(2 . 7 . 3 + "r" )); "full plus r")]
    #[test_case("2.7.r" => Ok(vers!(2 . 7 . 0 + "r" )); "minor dot r")]
    #[test_case("2.7-r" => Ok(vers!(2 . 7 . 0 + "r" )); "minor hyphen r")]
    #[test_case("2.7+r" => Ok(vers!(2 . 7 . 0 + "r" )); "minor plus r")]
    #[test_case("2.r" => Ok(vers!(2 . 0 . 0 + "r" )); "major dot r")]
    #[test_case("2-r" => Ok(vers!(2 . 0 . 0 + "r" )); "major hyphen r")]
    #[test_case("2+r" => Ok(vers!(2 . 0 . 0 + "r" )); "major plus r")]
    fn test_with_release_identifier(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
    }

    #[test_case("2020.4.9" => Ok(vers!(2020 . 4 . 9)))]
    #[test_case("2020.04.09" => Ok(vers!(2020 . 4 . 9)))]
    #[test_case("2020.4" => Ok(vers!(2020 . 4 . 0)))]
    #[test_case("2020.04" => Ok(vers!(2020 . 4 . 0)))]
    fn test_date_versions(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
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
    fn test_leading_zeroes(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
    }

    #[test_case("v1" => Ok(vers!(1 . 0 . 0)))]
    #[test_case("  v2  " => Ok(vers!(2 . 0 . 0)))]
    #[test_case("v1.2.3" => Ok(vers!(1 . 2 . 3)))]
    #[test_case("v1.3.3-7" => Ok(vers!(1 . 3 . 3 - 7)))]
    #[test_case("V3" => Ok(vers!(3 . 0 . 0)))]
    #[test_case("  V5  " => Ok(vers!(5 . 0 . 0)))]
    #[test_case("V2.3.4" => Ok(vers!(2 . 3 . 4)))]
    #[test_case("V4.2.4-2" => Ok(vers!(4 . 2 . 4 - 2)))]
    fn test_leading_v(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
    }

    #[test_case("1.v2" => Ok(vers!(1 . 0 . 0 - "v2")))]
    #[test_case("1-v3" => Ok(vers!(1 . 0 . 0 - "v3")))]
    #[test_case("1+v4" => Ok(vers!(1 . 0 . 0 + "v4")))]
    #[test_case("1.2.v3" => Ok(vers!(1 . 2 . 0 - "v3")))]
    #[test_case("1.2-v4" => Ok(vers!(1 . 2 . 0 - "v4")))]
    #[test_case("1.2+v5" => Ok(vers!(1 . 2 . 0 + "v5")))]
    #[test_case("1.2.3.v4" => Ok(vers!(1 . 2 . 3 - "v4")))]
    #[test_case("1.2.3-v5" => Ok(vers!(1 . 2 . 3 - "v5")))]
    #[test_case("1.2.3+v6" => Ok(vers!(1 . 2 . 3 + "v6")))]
    #[test_case("1.2.3-alpha.v4" => Ok(vers!(1 . 2 . 3 - "alpha" - "v4")))]
    #[test_case("1.2.3-alpha-v5" => Ok(vers!(1 . 2 . 3 - "alpha" - "v5")))]
    #[test_case("1.2.3-alpha+v6" => Ok(vers!(1 . 2 . 3 - "alpha" + "v6")))]
    #[test_case("1.2.3+build.v4" => Ok(vers!(1 . 2 . 3 + "build" - "v4")))]
    #[test_case("1.2.3+build-v5" => Ok(vers!(1 . 2 . 3 + "build" - "v5")))]
    #[test_case("1.2.3-alpha.v6+build.v7" => Ok(vers!(1 . 2 . 3 - "alpha" - "v6" + "build" - "v7")))]
    fn test_v_num_in_the_middle(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
    }

    #[test_case("1.9876543210987654321098765432109876543210" => Ok(vers!(1 . 0 . 0 - "9876543210987654321098765432109876543210")))]
    #[test_case("1.9876543210987654321098765432109876543210.2" => Ok(vers!(1 . 0 . 0 - "9876543210987654321098765432109876543210" - 2)))]
    #[test_case("1.2.9876543210987654321098765432109876543210" => Ok(vers!(1 . 2 . 0 - "9876543210987654321098765432109876543210")))]
    #[test_case("1.2.3.9876543210987654321098765432109876543210" => Ok(vers!(1 . 2 . 3 - "9876543210987654321098765432109876543210")))]
    #[test_case("1.2.3-9876543210987654321098765432109876543211" => Ok(vers!(1 . 2 . 3 - "9876543210987654321098765432109876543211")))]
    #[test_case("1.2.3+9876543210987654321098765432109876543213" => Ok(vers!(1 . 2 . 3 + "9876543210987654321098765432109876543213")))]
    fn test_too_large_numbers(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
    }

    #[test_case("" => Err(ErrorSpan::new(ErrorType::Missing(Segment::Part(Part::Major)), Span::new(0, 0))); "empty input")]
    #[test_case("  " => Err(ErrorSpan::new(ErrorType::Missing(Segment::Part(Part::Major)), Span::new(2, 2))); "whitespace input")]
    #[test_case("." => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(0, 1))); "dot")]
    #[test_case("🙈" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(0, 4))); "emoji")]
    #[test_case("v" => Err(ErrorSpan::new(ErrorType::Missing(Segment::Part(Part::Major)), Span::new(1, 1))); "v")]
    #[test_case("val" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(1, 2))); "val")]
    #[test_case("v🙈" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(1, 5))); "v-emoji")]
    #[test_case("1🙈" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(1, 5))); "1-emoji")]
    #[test_case("1." => Err(ErrorSpan::new(ErrorType::Missing(Segment::Part(Part::Minor)), Span::new(2, 2))); "eoi after major")]
    #[test_case("1. " => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(2, 3))); "whitespace after major")]
    #[test_case("1.2." => Err(ErrorSpan::new(ErrorType::Missing(Segment::Part(Part::Patch)), Span::new(4, 4))); "eoi after minor")]
    #[test_case("1.2. " => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(4, 5))); "whitespace after minor")]
    #[test_case("1.2.3-" => Err(ErrorSpan::new(ErrorType::Missing(Segment::PreRelease), Span::new(6, 6))); "eoi after hyphen")]
    #[test_case("1.2.3- " => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 7))); "whitespace after hyphen")]
    #[test_case("1.2.3.4-" => Err(ErrorSpan::new(ErrorType::Missing(Segment::PreRelease), Span::new(8, 8))); "eoi after additional")]
    #[test_case("1.2.3.4- " => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(8, 9))); "whitespace after additional")]
    #[test_case("1.2.3+" => Err(ErrorSpan::new(ErrorType::Missing(Segment::Build), Span::new(6, 6))); "eoi after plus")]
    #[test_case("1.2.3+ " => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 7))); "whitespace after plus")]
    #[test_case("1.2.3-." => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 7))); "pre release trailing dot")]
    #[test_case("1.2.3--" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 7))); "pre release trailing hyphen")]
    #[test_case("1.2.3-+" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 7))); "pre release trailing plus")]
    #[test_case("1.2.3-🙈" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 10))); "pre release trailing emoji")]
    #[test_case("1.2.3+." => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 7))); "build trailing dot")]
    #[test_case("1.2.3+-" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 7))); "build trailing hyphen")]
    #[test_case("1.2.3++" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 7))); "build trailing plus")]
    #[test_case("1.2.3-🙈" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 10))); "build trailing emoji")]
    #[test_case("v.1.2.3" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(1, 2))); "v followed by dot")]
    #[test_case("v-2.3.4" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(1, 2))); "v followed by hyphen")]
    #[test_case("v+3.4.5" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(1, 2))); "v followed by plus")]
    #[test_case("vv1.2.3" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(1, 2))); "v followed by v")]
    #[test_case("v v1.2.3" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(1, 2))); "v followed by whitespace")]
    #[test_case("a1.2.3" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(0, 1))); "starting with a-1")]
    #[test_case("a.b.c" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(0, 1))); "starting with a-dot")]
    #[test_case("1.+.0" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(2, 3))); "plus as minor")]
    #[test_case("1.2.." => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(4, 5))); "dot as patch")]
    #[test_case("123456789012345678901234567890" => Err(ErrorSpan::new(ErrorType::MajorNotNumeric, Span::new(0, 30))); "number overflows u64")]
    #[test_case("1 abc" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(2, 3))); "a following parsed number 1")]
    #[test_case("1.2.3 abc" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 7))); "a following parsed number 1.2.3")]
    fn test_simple_errors(input: &str) -> Result<Version, ErrorSpan> {
        parse_internal::<Version>(input)
    }

    #[test_case("" => r#"Could not parse the major identifier: No input
|    
|    
"#; "empty string")]
    #[test_case("  " => r#"Could not parse the major identifier: No input
|      
|    ~~
"#; "blank string")]
    #[test_case("1.2.3-" => r#"Could not parse the pre-release identifier: No input
|    1.2.3-
|    ~~~~~~
"#)]
    #[test_case("1.2.3+" => r#"Could not parse the build identifier: No input
|    1.2.3+
|    ~~~~~~
"#)]
    #[test_case("a.b.c" => r#"Unexpected `a`
|    a.b.c
|    ^
"#)]
    #[test_case("1.+.0" => r#"Unexpected `+`
|    1.+.0
|    ~~^
"#)]
    #[test_case("1.2.." => r#"Unexpected `.`
|    1.2..
|    ~~~~^
"#)]
    #[test_case("123456789012345678901234567890" => r#"Could not parse the major identifier: `123456789012345678901234567890` is not a number
|    123456789012345678901234567890
|    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
"#)]
    #[test_case("1.2.3 abc" => r#"Unexpected `a`
|    1.2.3 abc
|    ~~~~~~^
"#)]
    fn test_full_errors(input: &str) -> String {
        format!("{:#}", parse::<Version>(input).unwrap_err())
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
    #[test_case("r"; "release lower r")]
    fn test_is_release_identifier(v: &str) {
        assert!(is_release_identifier(v));
    }

    #[test_case("1.2.3" => parse::<Version>("1.2.3.Final"); "dot final")]
    #[test_case("1.2.3" => parse::<Version>("1.2.3.Release"); "dot release")]
    #[test_case("1.2.3" => parse::<Version>("1.2.3-Final"); "hyphen final")]
    #[test_case("1.2.3" => parse::<Version>("1.2.3-Release"); "hyphen release")]
    #[test_case("1.2.3" => parse::<Version>("1.2.3+Final"); "plus final")]
    #[test_case("1.2.3" => parse::<Version>("1.2.3+Release"); "plus release")]
    fn test_release_cmp(v: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(v)
    }

    #[test_case(" ", ' '; "space")]
    #[test_case("  ", ' '; "two spaces")]
    #[test_case("1", '1'; "singel ascii number")]
    #[test_case("123", '1'; "first ascii numbner")]
    #[test_case("🦀", '🦀'; "emoji")]
    #[test_case("🦀🦀", '🦀'; "multiple emoji")]
    #[test_case("🦀🙉🦀", '🦀'; "different emoji")]
    #[test_case("🙉🦀🙉", '🙉'; "other emoji")]
    #[test_case("3🦀", '3'; "ascii and emoji")]
    #[test_case("🦀3", '🦀'; "emoji and ascii")]
    #[test_case("∰42", '∰'; "whatever that is")]
    #[test_case("ßss", 'ß'; "the esszett")]
    #[test_case("äae", 'ä'; "ae")]
    #[test_case("åao", 'å'; "ao")]
    fn test_utf8_len(input: &str, expected: char) {
        let len = utf8_len(input.bytes().next().unwrap());
        assert_eq!(
            len,
            expected.len_utf8(),
            "input {} has not the same length as '{}', expected {} but got {} instead",
            input,
            expected,
            len,
            expected.len_utf8()
        );
    }
}
