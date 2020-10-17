//! Lenient parser for Semantic Version numbers.
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

use std::{fmt::Display, ops::Range, str::FromStr};

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
/// ![have a look at doc/railroad.svg](https://ssl.webpack.de/ghcdn.knutwalker.de/lenient-semver/doc/railroad.svg)
///
/// ## Examples
///
/// ```rust
/// use semver::Version;
///
/// let version = lenient_semver_parser::parse::<Version, _>("1.2.3");
/// assert_eq!(version, Ok(Version::new(1, 2, 3)));
///
/// // examples of a version that would not be accepted by semver_parser
/// assert_eq!(
///     lenient_semver_parser::parse::<Version, _>("1.2.M1").unwrap(),
///     Version::parse("1.2.0-M1").unwrap()
/// );
/// assert!(Version::parse("1.2.M1").is_err());
///
/// assert_eq!(
///     lenient_semver_parser::parse::<Version, _>("1").unwrap(),
///     Version::parse("1.0.0").unwrap()
/// );
/// assert!(Version::parse("1").is_err());
///
/// assert_eq!(
///     lenient_semver_parser::parse::<Version, _>("1.2.3.Final").unwrap(),
///     Version::parse("1.2.3+Final").unwrap()
/// );
/// assert!(Version::parse("1.2.3.Final").is_err());
///
/// assert_eq!(
///     lenient_semver_parser::parse::<Version, _>("1.2.3.4.5").unwrap(),
///     Version::parse("1.2.3+4.5").unwrap()
/// );
/// assert!(Version::parse("1.2.3.4.5").is_err());
///
/// assert_eq!(
///     lenient_semver_parser::parse::<Version, _>("v1.2.3").unwrap(),
///     Version::parse("1.2.3").unwrap()
/// );
/// assert!(Version::parse("v1.2.3").is_err());
///
/// assert_eq!(
///     lenient_semver_parser::parse::<Version, _>("1.2.9876543210987654321098765432109876543210").unwrap(),
///     Version::parse("1.2.0-9876543210987654321098765432109876543210").unwrap()
/// );
/// assert!(Version::parse("1.2.9876543210987654321098765432109876543210").is_err());
/// ```
pub fn parse<'input, V, N>(input: &'input str) -> Result<V::Out, Error<'input>>
where
    N: FromStr,
    V: VersionBuilder<'input, N>,
{
    parse_version::<_, N, V>(input, lex(input)).map_err(|ErrorSpan { error, span }| Error {
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
///     lenient_semver_parser::parse::<IsPreRelease, _>(v).unwrap_or_default()
/// }
///
/// assert!(is_pre_release("1.2.3-pre"));
/// assert!(!is_pre_release("1.2.3"));
/// assert!(!is_pre_release("1.2.3+build"));
/// ```
pub trait VersionBuilder<'input, N: FromStr = u64> {
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
    fn set_major(&mut self, major: N) {}

    /// Set the minor version component.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    #[allow(unused)]
    fn set_minor(&mut self, minor: N) {}

    /// Set the patch version component.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    #[allow(unused)]
    fn set_patch(&mut self, patch: N) {}

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
    fn add_additional(&mut self, num: N) {}

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
/// let error = lenient_semver_parser::parse::<Version, _>("1+").unwrap_err();
/// assert_eq!(error.to_string(), "Could not parse the build identifier: No input");
///
/// let error = lenient_semver_parser::parse::<Version, _>("1!").unwrap_err();
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
    /// let error = lenient_semver_parser::parse::<semver::Version, _>("1+").unwrap_err();
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
    /// let error = lenient_semver_parser::parse::<semver::Version, _>("1+").unwrap_err();
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
    ///     lenient_semver_parser::parse::<semver::Version, _>("").unwrap_err().error_kind(),
    ///     lenient_semver_parser::ErrorKind::MissingMajorNumber
    /// );
    /// assert_eq!(
    ///     lenient_semver_parser::parse::<semver::Version, _>("1.").unwrap_err().error_kind(),
    ///     lenient_semver_parser::ErrorKind::MissingMinorNumber
    /// );
    /// assert_eq!(
    ///     lenient_semver_parser::parse::<semver::Version, _>("1.2.").unwrap_err().error_kind(),
    ///     lenient_semver_parser::ErrorKind::MissingPatchNumber
    /// );
    /// assert_eq!(
    ///     lenient_semver_parser::parse::<semver::Version, _>("1-").unwrap_err().error_kind(),
    ///     lenient_semver_parser::ErrorKind::MissingPreRelease
    /// );
    /// assert_eq!(
    ///     lenient_semver_parser::parse::<semver::Version, _>("1+").unwrap_err().error_kind(),
    ///     lenient_semver_parser::ErrorKind::MissingBuild
    /// );
    /// assert_eq!(
    ///     lenient_semver_parser::parse::<semver::Version, _>("1!").unwrap_err().error_kind(),
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
    /// let error = lenient_semver_parser::parse::<semver::Version, _>("1+").unwrap_err();
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
    /// let error = lenient_semver_parser::parse::<semver::Version, _>("1.").unwrap_err();
    /// assert_eq!(error.error_line(), String::from("Could not parse the minor identifier: No input"));
    /// ```
    ///
    /// This is equivalent to the [`Display`] implementation, which can be further customized with format specifiers.
    ///
    /// ```rust
    /// let error = lenient_semver_parser::parse::<semver::Version, _>("1?").unwrap_err();
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
    /// let error = lenient_semver_parser::parse::<semver::Version, _>("foo").unwrap_err();
    /// assert_eq!(error.indicate_erroneous_input(), "^^^");
    ///
    /// let error = lenient_semver_parser::parse::<semver::Version, _>("1.2.3 bar").unwrap_err();
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

#[derive(Debug, Copy, Clone)]
enum State {
    Part(Part),
    Dot4,
    PreRelease,
    Build,
}

fn parse_version<'input, I, N, V>(input: &'input str, tokens: I) -> Result<V::Out, ErrorSpan>
where
    I: IntoIterator<Item = TokenSpan>,
    N: FromStr,
    V: VersionBuilder<'input, N>,
{
    let mut tokens = tokens.into_iter();
    let mut version = V::new();
    let mut state = State::Part(Part::Major);

    let mut token_span = match tokens.next() {
        Some(token) => token,
        None => return Err(ErrorSpan::missing_part(Part::Major, Span::default())),
    };

    loop {
        match state {
            State::Part(Part::Major) => match token_span.token {
                // skip initial whitespace
                Token::Whitespace => {}
                _ => {
                    version.set_major(parse_number_or_vnumber(token_span, input)?);
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
                Token::Alpha | Token::VNumeric => {
                    let v = token_span.span.at(input);
                    // things like 1.Final, early stop with a single build identifier
                    if is_release_identifier(v) {
                        version.add_build(v);
                        return finish_tokens(tokens, version);
                    }
                    // any alpha token skips right into pre-release parsing
                    state = State::PreRelease;
                    continue;
                }
                // unexpected end
                Token::Whitespace => return Err(ErrorSpan::missing_part(part, token_span.span)),
                // any other token is tried as a number
                _ => {
                    let v = token_span.span.at(input);
                    let num = match try_as_number(token_span.token, v) {
                        Some(num) => num,
                        None => {
                            // numeric overflow, interpret as alpha token and skip right into pre-release parsing
                            state = State::PreRelease;
                            continue;
                        }
                    };
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
                            Part::Patch => State::Dot4,
                        },
                        Token::Hyphen => State::PreRelease,
                        Token::Plus => State::Build,
                        _ => return finish_token_and_tokens(token_span, tokens, version),
                    };
                }
            },
            State::Dot4 => {
                let next_dot_state = match token_span.token {
                    // leading zero numbers are still interpreted as numbers
                    Token::Numeric => {
                        let v = token_span.span.at(input);
                        match try_as_number(token_span.token, v) {
                            Some(num) => {
                                version.add_additional(num);
                                State::Dot4
                            }
                            None => {
                                version.add_pre_release(v);
                                State::PreRelease
                            }
                        }
                    }
                    // all other tokens directly jump into the pre-release parser
                    _ => {
                        state = State::PreRelease;
                        continue;
                    }
                };
                token_span = match tokens.next() {
                    None => return finish(version),
                    Some(token_span) => token_span,
                };
                state = match token_span.token {
                    Token::Dot => next_dot_state,
                    Token::Hyphen => State::PreRelease,
                    Token::Plus => State::Build,
                    _ => return finish_token_and_tokens(token_span, tokens, version),
                };
            }
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
                    // numbers in pre-release are alphanum
                    Token::Numeric | Token::VNumeric => {
                        version.add_pre_release(token_span.span.at(input));
                    }
                    // unexpected end
                    Token::Whitespace => return Err(ErrorSpan::missing_pre(token_span.span)),
                    // any other token is invalid
                    _ => {
                        return Err(ErrorSpan::unexpected(token_span.span));
                    }
                }
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
                        // alpha, numeric and vnums are all alphanum build parts
                        Token::Alpha | Token::Numeric | Token::VNumeric => version.add_build(v),
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
                    State::PreRelease | State::Dot4 => Err(ErrorSpan::missing_pre(token_span.span)),
                    State::Build => Err(ErrorSpan::missing_build(token_span.span)),
                }
            }
        };
    }
}

#[inline]
fn parse_number_or_vnumber<N: FromStr>(token: TokenSpan, input: &str) -> Result<N, ErrorSpan> {
    let input = match token.token {
        Token::Numeric => token.span.at(input),
        Token::VNumeric => token.span.at1(input),
        _ => return Err(ErrorSpan::new(ErrorType::MajorNotNumeric, token.span)),
    };
    match input.parse::<N>() {
        Ok(num) => Ok(num),
        _ => Err(ErrorSpan::new(ErrorType::MajorNotNumeric, token.span)),
    }
}

#[inline]
fn try_as_number<N: FromStr>(token: Token, input: &str) -> Option<N> {
    match token {
        Token::Numeric => input.parse::<N>().ok(),
        _ => None,
    }
}

fn finish_tokens<'input, I, N, V>(tokens: I, value: V) -> Result<V::Out, ErrorSpan>
where
    I: Iterator<Item = TokenSpan>,
    N: FromStr,
    V: VersionBuilder<'input, N>,
{
    for token in tokens {
        finish_token(token)?;
    }
    finish(value)
}

fn finish_token_and_tokens<'input, I, N, V>(
    token: TokenSpan,
    tokens: I,
    value: V,
) -> Result<V::Out, ErrorSpan>
where
    I: Iterator<Item = TokenSpan>,
    N: FromStr,
    V: VersionBuilder<'input, N>,
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
fn finish<'input, N, V>(value: V) -> Result<V::Out, ErrorSpan>
where
    N: FromStr,
    V: VersionBuilder<'input, N>,
{
    Ok(value.build())
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
            '0'..='9' => match self.chars.find(|(_, c)| !c.is_ascii_digit()) {
                Some((j, c)) => {
                    if c.is_ascii_alphabetic() {
                        match self.chars.find(|(_, c)| !c.is_ascii_alphanumeric()) {
                            Some((j, c)) => {
                                self.peeked = Some((j, c));
                                (j, Token::Alpha)
                            }
                            None => (self.end, Token::Alpha),
                        }
                    } else {
                        self.peeked = Some((j, c));
                        (j, Token::Numeric)
                    }
                }
                None => (self.end, Token::Numeric),
            },
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
    #[cfg_attr(feature = "semver", test)]
    fn test_parse_semver() {
        let actual = parse::<Version, u64>("   v1.2.3.4.5-Foo-bar+baz-qux  ").ok();
        let expected = semver::Version::parse("1.2.3-Foo.bar+4.5.baz.qux").ok();
        assert_eq!(actual, expected)
    }

    #[cfg(feature = "semver10")]
    #[cfg_attr(feature = "semver10", test)]
    fn test_parse_semver10() {
        let actual = parse::<semver10::Version, u64>("   v1.2.3.4.5-Foo-bar+baz-qux  ").ok();
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
        parse::<Version, u64>(input)
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
        parse::<Version, u64>(input)
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
        parse::<Version, u64>(input)
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
        parse::<Version, u64>(input)
    }

    #[test_case("1.2.3-alpha1+build5" => Ok(vers!(1 . 2 . 3 - "alpha1" + "build5" )))]
    #[test_case("   1.2.3-alpha2+build6   " => Ok(vers!(1 . 2 . 3 - "alpha2" + "build6" )))]
    #[test_case("1.2.3-1.alpha1.9+build5.7.3aedf  " => Ok(vers!(1 . 2 . 3 - 1 - "alpha1" - 9 + "build5" - 7 - "3aedf" )))]
    #[test_case("0.4.0-beta.1+0851523" => Ok(vers!(0 . 4 . 0 - "beta" - 1 + "0851523" )))]
    fn test_combined(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version, u64>(input)
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
        parse::<Version, u64>(input)
    }

    #[test_case("2020.4.9" => Ok(vers!(2020 . 4 . 9)))]
    #[test_case("2020.04.09" => Ok(vers!(2020 . 4 . 9)))]
    #[test_case("2020.4" => Ok(vers!(2020 . 4 . 0)))]
    #[test_case("2020.04" => Ok(vers!(2020 . 4 . 0)))]
    fn test_date_versions(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version, u64>(input)
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
        parse::<Version, u64>(input)
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
        parse::<Version, u64>(input)
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
        parse::<Version, u64>(input)
    }

    #[test_case("1.9876543210987654321098765432109876543210" => Ok(vers!(1 . 0 . 0 - "9876543210987654321098765432109876543210")))]
    #[test_case("1.9876543210987654321098765432109876543210.2" => Ok(vers!(1 . 0 . 0 - "9876543210987654321098765432109876543210" - 2)))]
    #[test_case("1.2.9876543210987654321098765432109876543210" => Ok(vers!(1 . 2 . 0 - "9876543210987654321098765432109876543210")))]
    #[test_case("1.2.3.9876543210987654321098765432109876543210" => Ok(vers!(1 . 2 . 3 - "9876543210987654321098765432109876543210")))]
    #[test_case("1.2.3-9876543210987654321098765432109876543211" => Ok(vers!(1 . 2 . 3 - "9876543210987654321098765432109876543211")))]
    #[test_case("1.2.3+9876543210987654321098765432109876543213" => Ok(vers!(1 . 2 . 3 + "9876543210987654321098765432109876543213")))]
    fn test_too_large_numbers(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version, u64>(input)
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
    #[test_case("v.1.2.3" => Err(ErrorSpan::new(ErrorType::MajorNotNumeric, Span::new(0, 1))))]
    #[test_case("v-2.3.4" => Err(ErrorSpan::new(ErrorType::MajorNotNumeric, Span::new(0, 1))))]
    #[test_case("v+3.4.5" => Err(ErrorSpan::new(ErrorType::MajorNotNumeric, Span::new(0, 1))))]
    #[test_case("vv1.2.3" => Err(ErrorSpan::new(ErrorType::MajorNotNumeric, Span::new(0, 3))))]
    #[test_case("v v1.2.3" => Err(ErrorSpan::new(ErrorType::MajorNotNumeric, Span::new(0, 1))))]
    #[test_case("a.b.c" => Err(ErrorSpan::new(ErrorType::MajorNotNumeric, Span::new(0, 1))))]
    #[test_case("1.+.0" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(2, 3))))]
    #[test_case("1.2.." => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(4, 5))))]
    #[test_case("123456789012345678901234567890" => Err(ErrorSpan::new(ErrorType::MajorNotNumeric, Span::new(0, 30))))]
    #[test_case("1 abc" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(2, 5))))]
    #[test_case("1.2.3 abc" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 9))))]
    fn test_simple_errors(input: &str) -> Result<Version, ErrorSpan> {
        parse_version::<_, _, Version>(input, lex(input))
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
    #[test_case("1.2.3 abc" => r#"Unexpected `abc`
|    1.2.3 abc
|    ~~~~~~^^^
"#)]
    fn test_full_errors(input: &str) -> String {
        format!("{:#}", parse::<Version, u64>(input).unwrap_err())
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
                Token::Numeric,
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
                Token::Numeric,
                Token::Dot,
                Token::Numeric,
                Token::Dot,
                Token::Numeric,
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
            parse_version::<_, _, Version>("  1.2.3-1.alpha1.9+build5.7.3aedf   ", tokens),
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
    fn test_parse_number_or_vnumber_numeric() {
        assert_eq!(
            parse_number_or_vnumber(TokenSpan::new(Token::Numeric, 0, 2), "42"),
            Ok(42)
        )
    }

    #[test]
    fn test_parse_number_or_vnumber_zero_numeric() {
        assert_eq!(
            parse_number_or_vnumber(TokenSpan::new(Token::Numeric, 0, 3), "042"),
            Ok(42)
        )
    }

    #[test]
    fn test_parse_number_or_vnumber_v_numeric() {
        assert_eq!(
            parse_number_or_vnumber(TokenSpan::new(Token::VNumeric, 0, 3), "v42"),
            Ok(42)
        )
    }

    #[test_case(Token::Dot => Err(ErrorType::MajorNotNumeric))]
    #[test_case(Token::Plus => Err(ErrorType::MajorNotNumeric))]
    #[test_case(Token::Hyphen => Err(ErrorType::MajorNotNumeric))]
    #[test_case(Token::Whitespace => Err(ErrorType::MajorNotNumeric))]
    #[test_case(Token::Alpha => Err(ErrorType::MajorNotNumeric))]
    #[test_case(Token::UnexpectedChar => Err(ErrorType::MajorNotNumeric))]
    fn parse_version_number_error(token: Token) -> Result<u64, ErrorType> {
        parse_number_or_vnumber(TokenSpan::new(token, 0, 1), "x").map_err(|e| e.error)
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

    #[test_case("1.2.3" => parse::<Version, u64>("1.2.3.Final"); "dot final")]
    #[test_case("1.2.3" => parse::<Version, u64>("1.2.3.Release"); "dot release")]
    #[test_case("1.2.3" => parse::<Version, u64>("1.2.3-Final"); "hyphen final")]
    #[test_case("1.2.3" => parse::<Version, u64>("1.2.3-Release"); "hyphen release")]
    #[test_case("1.2.3" => parse::<Version, u64>("1.2.3+Final"); "plus final")]
    #[test_case("1.2.3" => parse::<Version, u64>("1.2.3+Release"); "plus release")]
    fn test_release_cmp(v: &str) -> Result<Version, Error<'_>> {
        parse::<Version, u64>(v)
    }
}
