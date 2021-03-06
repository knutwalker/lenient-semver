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

pub use lenient_semver_version_builder::VersionBuilder;
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
/// # use semver_v100 as semver;
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
///
/// ## Custom version builder example
///
/// A custom version builder can be used to implement some form of validation without needing to keep the result.
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
pub fn parse<'input, V>(input: &'input str) -> Result<V::Out, Error<'input>>
where
    V: VersionBuilder<'input>,
{
    parse_internal::<V>(input, &DFA, &LOOKUP)
}

/// Parse a string slice into a Version without failing on unexpected input.
///
/// This function tries to parse the string into a version and then stops when the input
/// no longer parsed into a version. The remainder if the input is returned alongside the version.
/// There still needs to be some valid version at the beginning of the string. That means
/// parsing anything that does not start with a version still fails.
///
/// All differences mentioned in [`parse`] apply to this function as well.
///
/// ## Examples
///
/// ```rust
/// # use semver_v100 as semver;
/// use semver::Version;
///
/// assert_eq!(
///     lenient_semver_parser::parse_partial::<Version>("1.2.3 and the rest").unwrap(),
///     (Version::new(1, 2, 3), "and the rest")
/// );
///
/// assert_eq!(
///     lenient_semver_parser::parse_partial::<Version>("1,2").unwrap(),
///     (Version::new(1, 0, 0), ",2")
/// );
///
/// assert_eq!(
///     lenient_semver_parser::parse_partial::<Version>("1 - 2").unwrap(),
///     (Version::new(1, 0, 0), "- 2")
/// );
/// ```
#[cfg(feature = "partial")]
pub fn parse_partial<'input, V>(input: &'input str) -> Result<(V::Out, &'input str), Error<'input>>
where
    V: VersionBuilder<'input>,
{
    parse_partial_internal::<V>(input, &DFA, &EXTRA_LOOKUP)
}

/// Possible errors that happen during parsing
/// and the location of the token where the error occurred.
///
/// # Example
///
/// ```rust
/// # use semver_v100 as semver;
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
    error: ErrorKind,
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
    /// # use semver_v100 as semver;
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
    /// # use semver_v100 as semver;
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
    /// # use semver_v100 as semver;
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
        self.error
    }

    /// Returns a slice from the original input line that triggered the error.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use semver_v100 as semver;
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
    /// # use semver_v100 as semver;
    /// let error = lenient_semver_parser::parse::<semver::Version>("1.").unwrap_err();
    /// assert_eq!(error.error_line(), String::from("Could not parse the minor identifier: No input"));
    /// ```
    ///
    /// This is equivalent to the [`Display`] implementation, which can be further customized with format specifiers.
    ///
    /// ```rust
    /// # use semver_v100 as semver;
    /// let error = lenient_semver_parser::parse::<semver::Version>("1?").unwrap_err();
    /// assert_eq!(format!("{:!^42}", error), String::from("!!!!!!!!!!!!!!Unexpected `?`!!!!!!!!!!!!!!"));
    /// ```
    pub fn error_line(&self) -> String {
        match &self.error {
            ErrorKind::MissingMajorNumber => {
                String::from("Could not parse the major identifier: No input")
            }
            ErrorKind::MissingMinorNumber => {
                String::from("Could not parse the minor identifier: No input")
            }
            ErrorKind::MissingPatchNumber => {
                String::from("Could not parse the patch identifier: No input")
            }
            ErrorKind::MissingPreRelease => {
                String::from("Could not parse the pre-release identifier: No input")
            }
            ErrorKind::MissingBuild => {
                String::from("Could not parse the build identifier: No input")
            }
            ErrorKind::NumberOverflow => format!(
                "The value `{}` overflows the range of an u64",
                self.erroneous_input()
            ),
            ErrorKind::UnexpectedInput => format!("Unexpected `{}`", self.erroneous_input()),
        }
    }

    /// Returns a caret line indication the erroneous input if it was written under the original input line.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use semver_v100 as semver;
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
            start = self.span.start,
            width = (self.span.end - self.span.start)
        )
    }
}

/// Owned version of [`Error`] which clones the input string.
#[derive(Debug, PartialEq, Eq)]
pub struct OwnedError {
    input: String,
    span: Span,
    error: ErrorKind,
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
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
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
    /// Trying to parse a number part, but the input overflowed a u64
    NumberOverflow,
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

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq)]
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

#[derive(Debug)]
struct InternalError {
    state: State,
    span: Span,
    error: ErrorKind,
}

macro_rules! accepts {
    (
        $op: ident,
        $index: ident,
        $partial: ident,
        $state: ident,
        $new_state: ident,
        $start: ident,
        $v: ident,
        $num: ident,
        $input: ident
    ) => {
        #[allow(unused_assignments)]
        {
            match $op {
                Accept::None => {}
                Accept::SaveStart => {
                    $start = $index;
                }
                Accept::Major => match $input[$start..$index].parse::<u64>() {
                    Ok(num) => $v.set_major(num),
                    _ => {
                        return Err(InternalError {
                            state: $state,
                            error: ErrorKind::NumberOverflow,
                            span: Span::new($start, $index),
                        });
                    }
                },
                Accept::Minor | Accept::MinorAtEnd => {
                    let segment = &$input[$start..$index];
                    match segment.parse::<u64>() {
                        Ok(num) => $v.set_minor(num),
                        _ if $op == Accept::MinorAtEnd => $v.add_pre_release(segment),
                        _ if $new_state < State::ParsePre => $new_state = State::ParsePre,
                        _ => {}
                    }
                }
                #[cfg(feature = "strict")]
                Accept::RequireMinor => match $input[$start..$index].parse::<u64>() {
                    Ok(num) => $v.set_minor(num),
                    _ => {
                        return Err(InternalError {
                            state: $state,
                            error: ErrorKind::NumberOverflow,
                            span: Span::new($start, $index),
                        });
                    }
                },
                Accept::Patch | Accept::PatchAtEnd => {
                    let segment = &$input[$start..$index];
                    match segment.parse::<u64>() {
                        Ok(num) => $v.set_patch(num),
                        _ if $op == Accept::PatchAtEnd => $v.add_pre_release(segment),
                        _ if $new_state < State::ParsePre => $new_state = State::ParsePre,
                        _ => {}
                    }
                }
                #[cfg(feature = "strict")]
                Accept::RequirePatch => match $input[$start..$index].parse::<u64>() {
                    Ok(num) => $v.set_patch(num),
                    _ => {
                        return Err(InternalError {
                            state: $state,
                            error: ErrorKind::NumberOverflow,
                            span: Span::new($start, $index),
                        });
                    }
                },
                Accept::Add | Accept::AddAtEnd => {
                    let segment = &$input[$start..$index];
                    match segment.parse::<u64>() {
                        Ok(num) => $v.add_additional(num),
                        _ if $op == Accept::AddAtEnd => $v.add_pre_release(segment),
                        _ if $new_state < State::ParsePre => $new_state = State::ParsePre,
                        _ => {}
                    }
                }
                Accept::Pre => {
                    let segment = &$input[$start..$index];
                    if is_release_identifier(segment) {
                        if $new_state < State::EndOfInput {
                            return Err(InternalError {
                                state: $state,
                                error: ErrorKind::UnexpectedInput,
                                span: span_from($input, $index),
                            });
                        }
                        $v.add_build(segment);
                    } else {
                        $v.add_pre_release(segment);
                    }
                }
                Accept::Build => {
                    $v.add_build(&$input[$start..$index]);
                }
                Accept::ErrorMissing => {
                    let start_index = start_index!($index, $partial, $state);
                    let span = if start_index < $input.len() {
                        span_from($input, start_index)
                    } else {
                        Span::new(start_index, start_index)
                    };
                    let error = match $state {
                        State::ExpectMajor | State::RequireMajor => ErrorKind::MissingMajorNumber,
                        State::ExpectMinor | State::ParseMajor => ErrorKind::MissingMinorNumber,
                        State::ExpectPatch | State::ParseMinor => ErrorKind::MissingPatchNumber,
                        State::ExpectAdd | State::ExpectPre => ErrorKind::MissingPreRelease,
                        State::ExpectBuild => ErrorKind::MissingBuild,
                        _ => unreachable!(),
                    };
                    return Err(InternalError {
                        state: $state,
                        error,
                        span,
                    });
                }
                Accept::ErrorUnexpected => {
                    accepts_partial!($index, $state, $start, $v, $input);
                    let start_index = start_index!($index, $partial, $state);
                    return Err(InternalError {
                        state: $state,
                        error: ErrorKind::UnexpectedInput,
                        span: span_from($input, start_index),
                    });
                }
            }
        }
    };
}

macro_rules! accepts_partial {
    (
        $index: ident,
        $state: ident,
        $start: ident,
        $v: ident,
        $input: ident
    ) => {
        #[allow(unused_assignments)]
        {
            match $state {
                State::RequireMajor => {
                    if let Ok(num) = $input[$start..$index].parse::<u64>() {
                        $v.set_major(num)
                    }
                }
                State::ParseMajor => match $input[$start..$index].parse::<u64>() {
                    Ok(num) => $v.set_major(num),
                    _ => {
                        return Err(InternalError {
                            state: $state,
                            error: ErrorKind::NumberOverflow,
                            span: Span::new($start, $index),
                        });
                    }
                },
                State::ParseMinor => {
                    let segment = &$input[$start..$index];
                    match segment.parse::<u64>() {
                        Ok(num) => $v.set_minor(num),
                        _ => $v.add_pre_release(segment),
                    }
                }
                State::ParsePatch => {
                    let segment = &$input[$start..$index];
                    match segment.parse::<u64>() {
                        Ok(num) => $v.set_patch(num),
                        _ => $v.add_pre_release(segment),
                    }
                }
                State::ParseAdd => {
                    let segment = &$input[$start..$index];
                    match segment.parse::<u64>() {
                        Ok(num) => $v.add_additional(num),
                        _ => $v.add_pre_release(segment),
                    }
                }
                State::ParsePre => {
                    let segment = &$input[$start..$index];
                    if is_release_identifier(segment) {
                        $v.add_build(segment);
                    } else {
                        $v.add_pre_release(segment);
                    }
                }
                State::ParseBuild => {
                    $v.add_build(&$input[$start..$index]);
                }
                _ => {}
            }
        }
    };
}

macro_rules! start_index {
    (
        $index: ident,
        $partial: ident,
        $state: ident
    ) => {
        if $partial
            && matches!(
                $state,
                State::ExpectMinor
                    | State::ExpectPatch
                    | State::ExpectAdd
                    | State::ExpectPre
                    | State::ExpectBuild
            )
        {
            $index - 1
        } else {
            $index
        }
    };
}

#[inline]
fn parse_internal<'input, V>(
    input: &'input str,
    dfa: &Dfa,
    lookup: &Lookup,
) -> Result<V::Out, Error<'input>>
where
    V: VersionBuilder<'input>,
{
    let mut v = V::new();

    match try_parse_internal(input, &mut v, false, dfa, lookup) {
        Ok(_) => Ok(v.build()),
        Err(err) => Err(Error {
            input,
            span: err.span,
            error: err.error,
        }),
    }
}

#[cfg(feature = "partial")]
#[inline]
fn parse_partial_internal<'input, V>(
    input: &'input str,
    dfa: &Dfa,
    lookup: &Lookup,
) -> Result<(V::Out, &'input str), Error<'input>>
where
    V: VersionBuilder<'input>,
{
    let mut v = V::new();
    match try_parse_internal(input, &mut v, true, dfa, lookup) {
        Ok(_) => Ok((v.build(), "")),
        Err(err) => {
            let keep_error = match err.state {
                State::ExpectMajor | State::RequireMajor => matches!(
                    err.error,
                    ErrorKind::UnexpectedInput | ErrorKind::MissingMajorNumber,
                ),
                State::ParseMajor => err.error == ErrorKind::NumberOverflow,
                _ => false,
            };

            if keep_error {
                Err(Error {
                    input,
                    span: err.span,
                    error: err.error,
                })
            } else {
                Ok((v.build(), &input[err.span.start..]))
            }
        }
    }
}

#[inline]
fn try_parse_internal<'input, V>(
    input: &'input str,
    v: &mut V,
    partial: bool,
    dfa: &Dfa,
    lookup: &Lookup,
) -> Result<(), InternalError>
where
    V: VersionBuilder<'input>,
{
    let mut start = 0_usize;
    let mut state = State::ExpectMajor;

    for (index, b) in input.bytes().enumerate() {
        let (mut new_state, accepts) = transduce(lookup, dfa, state, b);
        accepts!(accepts, index, partial, state, new_state, start, v, num, input);
        state = new_state;
    }
    let (mut new_state, accepts) = transition(dfa, state, Class::EndOfInput);
    let index = input.len();
    accepts!(accepts, index, partial, state, new_state, start, v, num, input);
    Ok(())
}

// This constant maps the first 5 bits of a code unit to the one less than the length in utf-8.
// There are 32 possible values for the first 5 bits. The length in utf-8 is in [1, 4].
// Subtracting 1 gives us [0, 3], which can be encoded in 2 bits.
// The utf-8 length for a given byte can be determined by looking at the first 5 bits and all the
// lengths are packed into this constant.
//
// 1. `byte >> 3`   produces to first 5 bits: `xxxxx...` -> `000xxxxx`
// 2. `_ << 1`      multiply by 2 as the length is encoded with 2 bits.
//                  We now have a value that is in [0, 63]
// 3. `MAGIC >> _`  selects the cooresponding length "entry" by shifting the MAGIC by the value we got in 2.
// 4. `_ & 0b11`    retains only the last two bits
// 5. `_ + 1`       returns the actual length in [1, 4]
//
// in UTF-8, the length is either 1 byte for any ASCII char (leading 0)
// or by the number of leading 1:
//   1 byte  => `0xxxx|...`  (1.)=> `0000xxxx`  (2.)=> `000xxxx0`
//   2 bytes => `110xx|...`  (1.)=> `000110xx`  (2.)=> `00110xx0`
//   3 bytes => `1110x|...`  (1.)=> `0001110x`  (2.)=> `001110x0`
//   4 bytes => `11110|...`  (1.)=> `00011110`  (2.)=> `00111100`
//
// There is only value for 4 bytes length, which is `00111100`, or 60.
// For 3 bytes length, there are two possible values, `00111000` and `00111010`, or 56 and 58.
// For 2 bytes length, there are four possible values, the rest falls into the 1 byte length region.
//
// There are bytes that start with `10xxx|...`. Those are continuation bytes and not valid for a first byte.
// We do map them to a single byte length. While this is incorrect, we will slice on the values produces by
// the following method and if we got a continuation byte, we will panic.
//
//                   ~4 ~~~3 ~~~~~~~~2                     ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~1
const MAGIC: u64 = 0b11_1010_0101_0101_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;

/// Get the length of a utf8-char by looking at it's leading byte without branching.
///
/// This is not a general purpose method, as it will return incorrect results when called
/// with continuation bytes. The way this method is called, the parser guarantees that this
/// does not happen.
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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(u8)]
enum Accept {
    None,
    SaveStart,
    Major,
    Minor,
    MinorAtEnd,
    #[cfg(feature = "strict")]
    RequireMinor,
    Patch,
    PatchAtEnd,
    #[cfg(feature = "strict")]
    RequirePatch,
    Add,
    AddAtEnd,
    Pre,
    Build,
    ErrorMissing,
    ErrorUnexpected,
}

type Lookup = [Class; 256];

const fn class_lookup(include_extra_alpha: bool) -> Lookup {
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
            '*' if include_extra_alpha => Class::Alpha,
            '?' if include_extra_alpha => Class::Alpha,
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
        ($transitions:ident: $($($cls:ident)|+ @ $state:ident -> $target:ident),+,) => {
            $(
                $(
                    $transitions[dfa_index(State::$state, Class::$cls) as usize] = State::$target;
                )+
            )+
        };
    }

macro_rules! accept {
        ($accepts:ident: $($($cls:ident)|+ @ $state:ident -> $accept:ident),+,) => {
            $(
                $(
                    $accepts[dfa_index(State::$state, Class::$cls) as usize] = Accept::$accept;
                )+
            )+
        };
    }

type Dfa = ([State; STATES * CLASSES], [Accept; STATES * CLASSES]);

const fn dfa() -> Dfa {
    let mut transitions = [State::Error; STATES * CLASSES];
    dfa!(transitions:
                           Whitespace @ ExpectMajor  -> ExpectMajor,
                                    V @ ExpectMajor  -> RequireMajor,
                               Number @ ExpectMajor  -> ParseMajor,

                               Number @ RequireMajor -> ParseMajor,

              Whitespace | EndOfInput @ ParseMajor   -> EndOfInput,
                               Number @ ParseMajor   -> ParseMajor,
                                  Dot @ ParseMajor   -> ExpectMinor,
                               Hyphen @ ParseMajor   -> ExpectPre,
                                 Plus @ ParseMajor   -> ExpectBuild,

                               Number @ ExpectMinor  -> ParseMinor,
                            Alpha | V @ ExpectMinor  -> ParsePre,

              Whitespace | EndOfInput @ ParseMinor   -> EndOfInput,
                               Number @ ParseMinor   -> ParseMinor,
                            Alpha | V @ ParseMinor   -> ParsePre,
                                  Dot @ ParseMinor   -> ExpectPatch,
                               Hyphen @ ParseMinor   -> ExpectPre,
                                 Plus @ ParseMinor   -> ExpectBuild,

                               Number @ ExpectPatch  -> ParsePatch,
                            Alpha | V @ ExpectPatch  -> ParsePre,

              Whitespace | EndOfInput @ ParsePatch   -> EndOfInput,
                               Number @ ParsePatch   -> ParsePatch,
                            Alpha | V @ ParsePatch   -> ParsePre,
                                  Dot @ ParsePatch   -> ExpectAdd,
                               Hyphen @ ParsePatch   -> ExpectPre,
                                 Plus @ ParsePatch   -> ExpectBuild,

                               Number @ ExpectAdd    -> ParseAdd,
                            Alpha | V @ ExpectAdd    -> ParsePre,

              Whitespace | EndOfInput @ ParseAdd     -> EndOfInput,
                               Number @ ParseAdd     -> ParseAdd,
                            Alpha | V @ ParseAdd     -> ParsePre,
                                  Dot @ ParseAdd     -> ExpectAdd,
                               Hyphen @ ParseAdd     -> ExpectPre,
                                 Plus @ ParseAdd     -> ExpectBuild,

                   Number | Alpha | V @ ExpectPre    -> ParsePre,

              Whitespace | EndOfInput @ ParsePre     -> EndOfInput,
    Dot | Hyphen | Number | Alpha | V @ ParsePre     -> ParsePre,
                                 Plus @ ParsePre     -> ExpectBuild,

                   Number | Alpha | V @ ExpectBuild  -> ParseBuild,

              Whitespace | EndOfInput @ ParseBuild   -> EndOfInput,
    Dot | Hyphen | Number | Alpha | V @ ParseBuild   -> ParseBuild,

              Whitespace | EndOfInput @ EndOfInput   -> EndOfInput,
    );

    let mut accepts = [Accept::None; STATES * CLASSES];
    accept!(accepts:
                                                       Number @ ExpectMajor  -> SaveStart,
                                                   EndOfInput @ ExpectMajor  -> ErrorMissing,
                     Alpha | Dot | Hyphen | Plus | Unexpected @ ExpectMajor  -> ErrorUnexpected,

                                                       Number @ RequireMajor -> SaveStart,
                                                   EndOfInput @ RequireMajor -> ErrorMissing,
    Whitespace | Alpha | V | Dot | Hyphen | Plus | Unexpected @ RequireMajor -> ErrorUnexpected,

                Whitespace | EndOfInput | Dot | Hyphen | Plus @ ParseMajor   -> Major,
                                       Alpha | V | Unexpected @ ParseMajor   -> ErrorUnexpected,

                                           Number | V | Alpha @ ExpectMinor  -> SaveStart,
                                                   EndOfInput @ ExpectMinor  -> ErrorMissing,
                Whitespace | Dot | Hyphen | Plus | Unexpected @ ExpectMinor  -> ErrorUnexpected,

                             Whitespace | Dot | Hyphen | Plus @ ParseMinor   -> Minor,
                                                   EndOfInput @ ParseMinor   -> MinorAtEnd,
                                                   Unexpected @ ParseMinor   -> ErrorUnexpected,

                                           Number | V | Alpha @ ExpectPatch  -> SaveStart,
                                                   EndOfInput @ ExpectPatch  -> ErrorMissing,
                Whitespace | Dot | Hyphen | Plus | Unexpected @ ExpectPatch  -> ErrorUnexpected,

                             Whitespace | Dot | Hyphen | Plus @ ParsePatch   -> Patch,
                                                   EndOfInput @ ParsePatch   -> PatchAtEnd,
                                                   Unexpected @ ParsePatch   -> ErrorUnexpected,

                                           Number | V | Alpha @ ExpectAdd    -> SaveStart,
                                                   EndOfInput @ ExpectAdd    -> ErrorMissing,
                Whitespace | Dot | Hyphen | Plus | Unexpected @ ExpectAdd    -> ErrorUnexpected,

                             Whitespace | Dot | Hyphen | Plus @ ParseAdd     -> Add,
                                                   EndOfInput @ ParseAdd     -> AddAtEnd,
                                                   Unexpected @ ParseAdd     -> ErrorUnexpected,

                                           Number | V | Alpha @ ExpectPre    -> SaveStart,
                                                   EndOfInput @ ExpectPre    -> ErrorMissing,
                Whitespace | Dot | Hyphen | Plus | Unexpected @ ExpectPre    -> ErrorUnexpected,

                               Whitespace | EndOfInput | Plus @ ParsePre     -> Pre,
                                                   Unexpected @ ParsePre     -> ErrorUnexpected,

                                           Number | V | Alpha @ ExpectBuild  -> SaveStart,
                                                   EndOfInput @ ExpectBuild  -> ErrorMissing,
                Whitespace | Dot | Hyphen | Plus | Unexpected @ ExpectBuild  -> ErrorUnexpected,

                                      Whitespace | EndOfInput @ ParseBuild   -> Build,
                                                   Unexpected @ ParseBuild   -> ErrorUnexpected,

        Alpha | V | Number | Dot | Hyphen | Plus | Unexpected @ EndOfInput   -> ErrorUnexpected,
    );

    (transitions, accepts)
}

static LOOKUP: Lookup = class_lookup(false);
#[cfg(feature = "partial")]
static EXTRA_LOOKUP: Lookup = class_lookup(true);
static DFA: Dfa = dfa();

#[inline(always)]
const fn transduce(class_lookup: &Lookup, dfa: &Dfa, s: State, b: u8) -> (State, Accept) {
    transition(dfa, s, class_lookup[b as usize])
}

#[inline(always)]
const fn transition(dfa: &Dfa, s: State, class: Class) -> (State, Accept) {
    let index = dfa_index(s, class) as usize;
    (dfa.0[index], dfa.1[index])
}

#[inline]
fn span_from(input: &str, index: usize) -> Span {
    Span::new(index, index + utf8_len(input.as_bytes()[index]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use semver_v010 as semver010;
    use semver_v011 as semver011;
    use semver_v100 as semver;
    use test_case::test_case;

    #[cfg(feature = "semver")]
    #[cfg_attr(feature = "semver", test)]
    fn test_parse_semver() {
        let actual = parse::<Version>("   v1.2.3.4.5-Foo-bar+baz-qux  ").ok();
        let expected = semver::Version::parse("1.2.3-Foo-bar+4.5.baz-qux").ok();
        assert_eq!(actual, expected)
    }

    #[cfg(feature = "semver011")]
    #[cfg_attr(feature = "semver011", test)]
    fn test_parse_semver011() {
        let actual = parse::<semver011::Version>("   v1.2.3.4.5-Foo-bar+baz-qux  ").ok();
        let expected = semver011::Version::parse("1.2.3-Foo.bar+4.5.baz.qux").ok();
        assert_eq!(actual, expected)
    }

    #[cfg(feature = "semver010")]
    #[cfg_attr(feature = "semver010", test)]
    fn test_parse_semver010() {
        let actual = parse::<semver010::Version>("   v1.2.3.4.5-Foo-bar+baz-qux  ").ok();
        let expected = semver010::Version::parse("1.2.3-Foo.bar+4.5.baz.qux").ok();
        assert_eq!(actual, expected)
    }

    use semver::Version;

    macro_rules! vers {
        ($major:literal . $minor:literal . $patch:literal) => {
            semver::Version::new($major, $minor, $patch)
        };

        ($major:literal . $minor:literal . $patch:literal - $pre:literal ) => {{
            let mut v = <Version as VersionBuilder<'static>>::new();
            v.set_major($major);
            v.set_minor($minor);
            v.set_patch($patch);
            v.add_pre_release($pre);
            v.build()
        }};

        ($major:literal . $minor:literal . $patch:literal + $build:literal ) => {{
            let mut v = <Version as VersionBuilder<'static>>::new();
            v.set_major($major);
            v.set_minor($minor);
            v.set_patch($patch);
            v.add_build($build);
            v.build()
        }};

        ($major:literal . $minor:literal . $patch:literal - $pre:literal + $build:literal ) => {{
            let mut v = <Version as VersionBuilder<'static>>::new();
            v.set_major($major);
            v.set_minor($minor);
            v.set_patch($patch);
            v.add_pre_release($pre);
            v.add_build($build);
            v.build()
        }};
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
    #[test_case("3.1.0-M13-beta3" => Ok(vers!(3 . 1 . 0 - "M13-beta3")))]
    #[test_case("1.2.3-alpha01.drop02" => Ok(vers!(1 . 2 . 3 - "alpha01.drop02")))]
    #[test_case("1.4.1-alpha01" => Ok(vers!(1 . 4 . 1 - "alpha01")))]
    #[test_case("1.4-alpha02" => Ok(vers!(1 . 4 . 0 - "alpha02")))]
    #[test_case("1-alpha03" => Ok(vers!(1 . 0 . 0 - "alpha03")))]
    #[test_case("1.9.3.RC1" => Ok(vers!(1 . 9 . 3 - "RC1")))]
    #[test_case("1.9.RC2" => Ok(vers!(1 . 9 . 0 - "RC2")))]
    #[test_case("1.RC3" => Ok(vers!(1 . 0 . 0 - "RC3")))]
    #[test_case("1.3.3-7" => Ok(vers!(1 . 3 . 3 - "7")))]
    #[test_case("5.9.0-202009080501-r" => Ok(vers!(5 . 9 . 0 - "202009080501-r")))]
    #[test_case("1.2.3.RC.4" => Ok(vers!(1 . 2 . 3 - "RC.4")))]
    fn test_pre_release(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
    }

    #[test_case("1.2.3+build1" => Ok(vers!(1 . 2 . 3 + "build1")))]
    #[test_case("  1.2.3+build2  " => Ok(vers!(1 . 2 . 3 + "build2")))]
    #[test_case("3.1.0+build3-r021" => Ok(vers!(3 . 1 . 0 + "build3-r021")))]
    #[test_case("1.2.3+build01.drop02" => Ok(vers!(1 . 2 . 3 + "build01.drop02")))]
    #[test_case("1.4.1+build01" => Ok(vers!(1 . 4 . 1 + "build01")))]
    #[test_case("1.4+build02" => Ok(vers!(1 . 4 . 0 + "build02")))]
    #[test_case("1+build03" => Ok(vers!(1 . 0 . 0 + "build03")))]
    #[test_case("7.2.0+28-2f9fb552" => Ok(vers!(7 . 2 . 0 + "28-2f9fb552" )))]
    #[test_case("1.3.3.7" => Ok(vers!(1 . 3 . 3 + "7")))]
    #[test_case("5.9.0.202009080501-r" => Ok(vers!(5 . 9 . 0 + "202009080501.r")))]
    fn test_build(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
    }

    #[test_case("1.3.3.7" => Ok(vers!(1 . 3 . 3 + "7")))]
    #[test_case("1.3.3.0" => Ok(vers!(1 . 3 . 3 + "0")))]
    #[test_case("1.3.3.00" => Ok(vers!(1 . 3 . 3 + "0")))]
    #[test_case("1.3.3.07" => Ok(vers!(1 . 3 . 3 + "7")))]
    #[test_case("1.3.3.7.4.2" => Ok(vers!(1 . 3 . 3 + "7.4.2")))]
    #[test_case("1.3.3.7.04.02" => Ok(vers!(1 . 3 . 3 + "7.4.2")))]
    #[test_case("1.3.3.9876543210987654321098765432109876543210" => Ok(vers!(1 . 3 . 3 - "9876543210987654321098765432109876543210")))]
    #[test_case("1.3.3.9876543210987654321098765432109876543210.4.2" => Ok(vers!(1 . 3 . 3 - "9876543210987654321098765432109876543210.4.2")))]
    #[test_case("1.3.3.7.foo" => Ok(vers!(1 . 3 . 3 - "foo" + "7")))]
    #[test_case("1.3.3.7-bar" => Ok(vers!(1 . 3 . 3 - "bar" + "7")))]
    #[test_case("1.3.3.7+baz" => Ok(vers!(1 . 3 . 3 + "7.baz")))]
    fn test_additional_numbers(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
    }

    #[test_case("1.2.3-alpha1+build5" => Ok(vers!(1 . 2 . 3 - "alpha1" + "build5" )))]
    #[test_case("   1.2.3-alpha2+build6   " => Ok(vers!(1 . 2 . 3 - "alpha2" + "build6" )))]
    #[test_case("1.2.3-1.alpha1.9+build5.7.3aedf  " => Ok(vers!(1 . 2 . 3 - "1.alpha1.9" + "build5.7.3aedf" )))]
    #[test_case("0.4.0-beta.1+0851523" => Ok(vers!(0 . 4 . 0 - "beta.1" + "0851523" )))]
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
    #[test_case("1.2.3-1" => Ok(vers!(1 . 2 . 3 - "1")))]
    #[test_case("1.2.3-01" => Ok(vers!(1 . 2 . 3 - "01")))]
    #[test_case("1.2.3-0001" => Ok(vers!(1 . 2 . 3 - "0001")))]
    #[test_case("2.3.4+1" => Ok(vers!(2 . 3 . 4 + "1")))]
    #[test_case("2.3.4+01" => Ok(vers!(2 . 3 . 4 + "01")))]
    #[test_case("2.3.4+0001" => Ok(vers!(2 . 3 . 4 + "0001")))]
    fn test_leading_zeroes(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
    }

    #[test_case("v1" => Ok(vers!(1 . 0 . 0)))]
    #[test_case("  v2  " => Ok(vers!(2 . 0 . 0)))]
    #[test_case("v1.2.3" => Ok(vers!(1 . 2 . 3)))]
    #[test_case("v1.3.3-7" => Ok(vers!(1 . 3 . 3 - "7")))]
    #[test_case("V3" => Ok(vers!(3 . 0 . 0)))]
    #[test_case("  V5  " => Ok(vers!(5 . 0 . 0)))]
    #[test_case("V2.3.4" => Ok(vers!(2 . 3 . 4)))]
    #[test_case("V4.2.4-2" => Ok(vers!(4 . 2 . 4 - "2")))]
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
    #[test_case("1.2.3-alpha.v4" => Ok(vers!(1 . 2 . 3 - "alpha.v4")))]
    #[test_case("1.2.3-alpha-v5" => Ok(vers!(1 . 2 . 3 - "alpha-v5")))]
    #[test_case("1.2.3-alpha+v6" => Ok(vers!(1 . 2 . 3 - "alpha" + "v6")))]
    #[test_case("1.2.3+build.v4" => Ok(vers!(1 . 2 . 3 + "build.v4")))]
    #[test_case("1.2.3+build-v5" => Ok(vers!(1 . 2 . 3 + "build-v5")))]
    #[test_case("1.2.3-alpha.v6+build.v7" => Ok(vers!(1 . 2 . 3 - "alpha.v6" + "build.v7")))]
    fn test_v_num_in_the_middle(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
    }

    #[test_case("1.9876543210987654321098765432109876543210" => Ok(vers!(1 . 0 . 0 - "9876543210987654321098765432109876543210")))]
    #[test_case("1.9876543210987654321098765432109876543210.2" => Ok(vers!(1 . 0 . 0 - "9876543210987654321098765432109876543210.2")))]
    #[test_case("1.2.9876543210987654321098765432109876543210" => Ok(vers!(1 . 2 . 0 - "9876543210987654321098765432109876543210")))]
    #[test_case("1.2.3.9876543210987654321098765432109876543210" => Ok(vers!(1 . 2 . 3 - "9876543210987654321098765432109876543210")))]
    #[test_case("1.2.3-9876543210987654321098765432109876543211" => Ok(vers!(1 . 2 . 3 - "9876543210987654321098765432109876543211")))]
    #[test_case("1.2.3+9876543210987654321098765432109876543213" => Ok(vers!(1 . 2 . 3 + "9876543210987654321098765432109876543213")))]
    fn test_too_large_numbers(input: &str) -> Result<Version, Error<'_>> {
        parse::<Version>(input)
    }

    #[test_case("1,2" => Ok((vers!(1 . 0 . 0 ), ",2")))]
    #[test_case("2, 3" => Ok((vers!(2 . 0 . 0), ", 3")))]
    #[test_case("3 , 4" => Ok((vers!(3 . 0 . 0), ", 4")))]
    #[test_case("1.2.3-2.3.4" => Ok((vers!(1 . 2 . 3 - "2.3.4"), "")))]
    #[test_case("2.3.4 - 4.5.6" => Ok((vers!(2 . 3 . 4), "- 4.5.6")))]
    #[test_case("1.x.3 || 3.4.5" => Ok((vers!(1 . 0 . 0 - "x.3"), "|| 3.4.5")))]
    #[test_case("1.2,a" => Ok((vers!(1 . 2 . 0), ",a")))]
    #[test_case("1.2.3,b" => Ok((vers!(1 . 2 . 3), ",b")))]
    #[test_case("1.2a,c" => Ok((vers!(1 . 0 . 0 - "2a"), ",c")))]
    #[test_case("1.2.a,d" => Ok((vers!(1 . 2 . 0 - "a"), ",d")))]
    #[test_case("1.2-a,e" => Ok((vers!(1 . 2 . 0 - "a"), ",e")))]
    #[test_case("1.2.3+a,f" => Ok((vers!(1 . 2 . 3 + "a"), ",f")))]
    #[cfg(feature = "partial")]
    fn test_parse_partial(input: &str) -> Result<(Version, &str), Error<'_>> {
        parse_partial::<Version>(input)
    }

    #[test_case("1.*" => Ok(vers!(1 . 0 . 0 - "*")))]
    #[test_case("1.2.*" => Ok(vers!(1 . 2 . 0 - "*")))]
    #[test_case("1.2.3.*" => Ok(vers!(1 . 2 . 3 - "*")))]
    #[test_case("1.2.4.***" => Ok(vers!(1 . 2 . 4 - "***")))]
    #[test_case("1.2.5-a*b*c" => Ok(vers!(1 . 2 . 5 - "a*b*c")))]
    #[test_case("2.?" => Ok(vers!(2 . 0 . 0 - "?")))]
    #[test_case("2.2.?" => Ok(vers!(2 . 2 . 0 - "?")))]
    #[test_case("2.2.3.?" => Ok(vers!(2 . 2 . 3 - "?")))]
    #[test_case("2.2.4.???" => Ok(vers!(2 . 2 . 4 - "???")))]
    #[test_case("2.2.5-a?b?c" => Ok(vers!(2 . 2 . 5 - "a?b?c")))]
    #[cfg(feature = "partial")]
    fn test_parse_partial_extend_alpha(input: &str) -> Result<Version, Error<'_>> {
        parse_partial::<Version>(input).map(|(v, _)| v)
    }

    #[test_case("" => Err((ErrorKind::MissingMajorNumber, Span::new(0, 0))); "empty input")]
    #[test_case("  " => Err((ErrorKind::MissingMajorNumber, Span::new(2, 2))); "whitespace input")]
    #[test_case("." => Err((ErrorKind::UnexpectedInput, Span::new(0, 1))); "dot")]
    #[test_case("🙈" => Err((ErrorKind::UnexpectedInput, Span::new(0, 4))); "emoji")]
    #[test_case("v" => Err((ErrorKind::MissingMajorNumber, Span::new(1, 1))); "v")]
    #[test_case("val" => Err((ErrorKind::UnexpectedInput, Span::new(1, 2))); "val")]
    #[test_case("v🙈" => Err((ErrorKind::UnexpectedInput, Span::new(1, 5))); "v-emoji")]
    #[test_case("1🙈" => Err((ErrorKind::UnexpectedInput, Span::new(1, 5))); "1-emoji")]
    #[test_case("1." => Err((ErrorKind::MissingMinorNumber, Span::new(2, 2))); "eoi after major")]
    #[test_case("1. " => Err((ErrorKind::UnexpectedInput, Span::new(2, 3))); "whitespace after major")]
    #[test_case("1.2." => Err((ErrorKind::MissingPatchNumber, Span::new(4, 4))); "eoi after minor")]
    #[test_case("1.2. " => Err((ErrorKind::UnexpectedInput, Span::new(4, 5))); "whitespace after minor")]
    #[test_case("1.2.3-" => Err((ErrorKind::MissingPreRelease, Span::new(6, 6))); "eoi after hyphen")]
    #[test_case("1.2.3- " => Err((ErrorKind::UnexpectedInput, Span::new(6, 7))); "whitespace after hyphen")]
    #[test_case("1.2.3.4-" => Err((ErrorKind::MissingPreRelease, Span::new(8, 8))); "eoi after additional")]
    #[test_case("1.2.3.4- " => Err((ErrorKind::UnexpectedInput, Span::new(8, 9))); "whitespace after additional")]
    #[test_case("1.2.3+" => Err((ErrorKind::MissingBuild, Span::new(6, 6))); "eoi after plus")]
    #[test_case("1.2.3+ " => Err((ErrorKind::UnexpectedInput, Span::new(6, 7))); "whitespace after plus")]
    #[test_case("1.2.3-." => Err((ErrorKind::UnexpectedInput, Span::new(6, 7))); "pre release trailing dot")]
    #[test_case("1.2.3--" => Err((ErrorKind::UnexpectedInput, Span::new(6, 7))); "pre release trailing hyphen")]
    #[test_case("1.2.3-+" => Err((ErrorKind::UnexpectedInput, Span::new(6, 7))); "pre release trailing plus")]
    #[test_case("1.2.3-🙈" => Err((ErrorKind::UnexpectedInput, Span::new(6, 10))); "pre release trailing emoji")]
    #[test_case("1.2.3+." => Err((ErrorKind::UnexpectedInput, Span::new(6, 7))); "build trailing dot")]
    #[test_case("1.2.3+-" => Err((ErrorKind::UnexpectedInput, Span::new(6, 7))); "build trailing hyphen")]
    #[test_case("1.2.3++" => Err((ErrorKind::UnexpectedInput, Span::new(6, 7))); "build trailing plus")]
    #[test_case("1.2.3-🙈" => Err((ErrorKind::UnexpectedInput, Span::new(6, 10))); "build trailing emoji")]
    #[test_case("v.1.2.3" => Err((ErrorKind::UnexpectedInput, Span::new(1, 2))); "v followed by dot")]
    #[test_case("v-2.3.4" => Err((ErrorKind::UnexpectedInput, Span::new(1, 2))); "v followed by hyphen")]
    #[test_case("v+3.4.5" => Err((ErrorKind::UnexpectedInput, Span::new(1, 2))); "v followed by plus")]
    #[test_case("vv1.2.3" => Err((ErrorKind::UnexpectedInput, Span::new(1, 2))); "v followed by v")]
    #[test_case("v v1.2.3" => Err((ErrorKind::UnexpectedInput, Span::new(1, 2))); "v followed by whitespace")]
    #[test_case("a1.2.3" => Err((ErrorKind::UnexpectedInput, Span::new(0, 1))); "starting with a-1")]
    #[test_case("a.b.c" => Err((ErrorKind::UnexpectedInput, Span::new(0, 1))); "starting with a-dot")]
    #[test_case("1.+.0" => Err((ErrorKind::UnexpectedInput, Span::new(2, 3))); "plus as minor")]
    #[test_case("1.2.." => Err((ErrorKind::UnexpectedInput, Span::new(4, 5))); "dot as patch")]
    #[test_case("123456789012345678901234567890" => Err((ErrorKind::NumberOverflow, Span::new(0, 30))); "number overflows u64")]
    #[test_case("1 abc" => Err((ErrorKind::UnexpectedInput, Span::new(2, 3))); "a following parsed number 1")]
    #[test_case("1.2.3 abc" => Err((ErrorKind::UnexpectedInput, Span::new(6, 7))); "a following parsed number 1.2.3")]
    #[test_case("1.*" => Err((ErrorKind::UnexpectedInput, Span::new(2, 3))); "asterisk as early pre")]
    #[test_case("1.2.3-*" => Err((ErrorKind::UnexpectedInput, Span::new(6, 7))); "asterisk as explicit pre")]
    #[test_case("1.2.3-ab*" => Err((ErrorKind::UnexpectedInput, Span::new(8, 9))); "asterisk within pre")]
    #[test_case("1.?" => Err((ErrorKind::UnexpectedInput, Span::new(2, 3))); "question mark as early pre")]
    #[test_case("1.2.3-?" => Err((ErrorKind::UnexpectedInput, Span::new(6, 7))); "question mark as explicit pre")]
    #[test_case("1.2.3-ab?" => Err((ErrorKind::UnexpectedInput, Span::new(8, 9))); "question mark within pre")]
    fn test_simple_errors(input: &str) -> Result<Version, (ErrorKind, Span)> {
        parse::<Version>(input).map_err(|e| (e.error, e.span))
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
    #[test_case("123456789012345678901234567890" => r#"The value `123456789012345678901234567890` overflows the range of an u64
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

    #[test_case("" => Err((ErrorKind::MissingMajorNumber, Span::new(0, 0))); "empty input")]
    #[test_case("  " => Err((ErrorKind::MissingMajorNumber, Span::new(2, 2))); "whitespace input")]
    #[test_case("." => Err((ErrorKind::UnexpectedInput, Span::new(0, 1))); "dot")]
    #[test_case("🙈" => Err((ErrorKind::UnexpectedInput, Span::new(0, 4))); "emoji")]
    #[test_case("v" => Err((ErrorKind::MissingMajorNumber, Span::new(1, 1))); "v")]
    #[test_case("val" => Err((ErrorKind::UnexpectedInput, Span::new(1, 2))); "val")]
    #[test_case("v🙈" => Err((ErrorKind::UnexpectedInput, Span::new(1, 5))); "v-emoji")]
    #[test_case("v.1.2.3" => Err((ErrorKind::UnexpectedInput, Span::new(1, 2))); "v followed by dot")]
    #[test_case("v-2.3.4" => Err((ErrorKind::UnexpectedInput, Span::new(1, 2))); "v followed by hyphen")]
    #[test_case("v+3.4.5" => Err((ErrorKind::UnexpectedInput, Span::new(1, 2))); "v followed by plus")]
    #[test_case("vv1.2.3" => Err((ErrorKind::UnexpectedInput, Span::new(1, 2))); "v followed by v")]
    #[test_case("v v1.2.3" => Err((ErrorKind::UnexpectedInput, Span::new(1, 2))); "v followed by whitespace")]
    #[test_case("a1.2.3" => Err((ErrorKind::UnexpectedInput, Span::new(0, 1))); "starting with a-1")]
    #[test_case("a.b.c" => Err((ErrorKind::UnexpectedInput, Span::new(0, 1))); "starting with a-dot")]
    #[test_case("123456789012345678901234567890" => Err((ErrorKind::NumberOverflow, Span::new(0, 30))); "number overflows u64")]
    #[cfg(feature = "partial")]
    fn test_partial_simple_errors(input: &str) -> Result<(Version, &str), (ErrorKind, Span)> {
        parse_partial::<Version>(input).map_err(|e| (e.error, e.span))
    }

    #[test_case("1." => Ok((vers!(1 . 0 . 0), ".")); "eoi after major")]
    #[test_case("1. " => Ok((vers!(1 . 0 . 0), ". ")); "whitespace after major")]
    #[test_case("1🙈" => Ok((vers!(1 . 0 . 0), "🙈")); "1-emoji")]
    #[test_case("1.2." => Ok((vers!(1 . 2 . 0), ".")); "eoi after minor")]
    #[test_case("1.2. " => Ok((vers!(1 . 2 . 0), ". ")); "whitespace after minor")]
    #[test_case("1.2.3-" => Ok((vers!(1 . 2 . 3), "-")); "eoi after hyphen")]
    #[test_case("1.2.3- " => Ok((vers!(1 . 2 . 3), "- ")); "whitespace after hyphen")]
    #[test_case("1.2.3.4-" => Ok((vers!(1 . 2 . 3 + "4"), "-")); "eoi after additional")]
    #[test_case("1.2.3.4- " => Ok((vers!(1 . 2 . 3 + "4"), "- ")); "whitespace after additional")]
    #[test_case("1.2.3+" => Ok((vers!(1 . 2 . 3), "+")); "eoi after plus")]
    #[test_case("1.2.3+ " => Ok((vers!(1 . 2 . 3), "+ ")); "whitespace after plus")]
    #[test_case("1.2.3-." => Ok((vers!(1 . 2 . 3), "-.")); "pre release trailing dot")]
    #[test_case("1.2.3--" => Ok((vers!(1 . 2 . 3), "--")); "pre release trailing hyphen")]
    #[test_case("1.2.3-+" => Ok((vers!(1 . 2 . 3), "-+")); "pre release trailing plus")]
    #[test_case("1.2.3-🙈" => Ok((vers!(1 . 2 . 3), "-🙈")); "pre release trailing emoji")]
    #[test_case("1.2.3+." => Ok((vers!(1 . 2 . 3), "+.")); "build trailing dot")]
    #[test_case("1.2.3+-" => Ok((vers!(1 . 2 . 3), "+-")); "build trailing hyphen")]
    #[test_case("1.2.3++" => Ok((vers!(1 . 2 . 3), "++")); "build trailing plus")]
    #[test_case("1.2.3-🙈" => Ok((vers!(1 . 2 . 3), "-🙈")); "build trailing emoji")]
    #[test_case("1.+.0" => Ok((vers!(1 . 0 . 0), ".+.0")); "plus as minor")]
    #[test_case("1.2.." => Ok((vers!(1 . 2 . 0), "..")); "dot as patch")]
    #[test_case("1 abc" => Ok((vers!(1 . 0 . 0), "abc")); "a following parsed number 1")]
    #[test_case("1.2.3 abc" => Ok((vers!(1 . 2 . 3), "abc")); "a following parsed number 1.2.3")]
    #[cfg(feature = "partial")]
    fn test_partial_non_errors(input: &str) -> Result<(Version, &str), (ErrorKind, Span)> {
        parse_partial::<Version>(input).map_err(|e| (e.error, e.span))
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

    #[test_case("=1.2.3", parse::<Version>("1.2.3.Final"); "dot final")]
    #[test_case("=1.2.3", parse::<Version>("1.2.3.Release"); "dot release")]
    #[test_case("=1.2.3", parse::<Version>("1.2.3-Final"); "hyphen final")]
    #[test_case("=1.2.3", parse::<Version>("1.2.3-Release"); "hyphen release")]
    #[test_case("=1.2.3", parse::<Version>("1.2.3+Final"); "plus final")]
    #[test_case("=1.2.3", parse::<Version>("1.2.3+Release"); "plus release")]
    fn test_release_cmp(v: &str, eqv: Result<Version, Error<'_>>) {
        // semver 1.x no longer ignore the build when comparing versions
        // we check that the version compared against `=1.2.3`
        assert!(semver::VersionReq::parse(v).unwrap().matches(&eqv.unwrap()));
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

/// A strict version of the parser that follows the spec more closely. It is not 100% spec compliant, but it's closer.
#[cfg(feature = "strict")]
pub mod strict {
    use super::*;

    /// Parse a string slice into a Version, using strict semantics.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use semver_v100 as semver;
    /// use semver::Version;
    ///
    /// let version = lenient_semver_parser::strict::parse::<Version>("1.2.3");
    /// assert_eq!(version, Ok(Version::new(1, 2, 3)));
    ///
    /// // examples of a version that wpuld be accepted by the regular parser,
    /// // but not by the strict one.
    /// assert!(lenient_semver_parser::strict::parse::<Version>("1.2.M1").is_err());
    ///
    /// assert!(lenient_semver_parser::strict::parse::<Version>("1").is_err());
    ///
    /// assert!(lenient_semver_parser::strict::parse::<Version>("1.2.3.Final").is_err());
    ///
    /// assert!(lenient_semver_parser::strict::parse::<Version>("1.2.3.4.5").is_err());
    ///
    /// assert!(lenient_semver_parser::strict::parse::<Version>("v1.2.3").is_err());
    ///
    /// assert!(lenient_semver_parser::strict::parse::<Version>("1.2.9876543210987654321098765432109876543210").is_err());
    /// ```
    pub fn parse<'input, V>(input: &'input str) -> Result<V::Out, Error<'input>>
    where
        V: VersionBuilder<'input>,
    {
        parse_internal::<V>(input, &STRICT_DFA, &LOOKUP)
    }

    /// Parse a string slice into a Version without failing on unexpected input.
    ///
    /// This function tries to parse the string into a version and then stops when the input
    /// no longer parsed into a version. The remainder if the input is returned alongside the version.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use semver_v100 as semver;
    /// use semver::Version;
    ///
    /// assert_eq!(
    ///     lenient_semver_parser::strict::parse_partial::<Version>("1.2.3 and the rest").unwrap(),
    ///     (Version::new(1, 2, 3), "and the rest")
    /// );
    ///
    /// assert_eq!(
    ///     lenient_semver_parser::strict::parse_partial::<Version>("1,2").unwrap(),
    ///     (Version::new(1, 0, 0), ",2")
    /// );
    ///
    /// assert_eq!(
    ///     lenient_semver_parser::strict::parse_partial::<Version>("1 - 2").unwrap(),
    ///     (Version::new(1, 0, 0), " - 2")
    /// );
    /// ```
    #[cfg(feature = "partial")]
    pub fn parse_partial<'input, V>(
        input: &'input str,
    ) -> Result<(V::Out, &'input str), Error<'input>>
    where
        V: VersionBuilder<'input>,
    {
        parse_partial_internal::<V>(input, &STRICT_DFA, &LOOKUP)
    }

    static STRICT_DFA: Dfa = strict_dfa();

    pub(super) const fn strict_dfa() -> Dfa {
        let mut transitions = [State::Error; STATES * CLASSES];
        dfa!(transitions:

                     Whitespace @ ExpectMajor  -> ExpectMajor,
                         Number @ ExpectMajor  -> ParseMajor,

                         Number @ ParseMajor   -> ParseMajor,
                            Dot @ ParseMajor   -> ExpectMinor,

                         Number @ ExpectMinor  -> ParseMinor,

                         Number @ ParseMinor   -> ParseMinor,
                            Dot @ ParseMinor   -> ExpectPatch,

                         Number @ ExpectPatch  -> ParsePatch,

        Whitespace | EndOfInput @ ParsePatch   -> EndOfInput,
                         Number @ ParsePatch   -> ParsePatch,
                         Hyphen @ ParsePatch   -> ExpectPre,
                           Plus @ ParsePatch   -> ExpectBuild,

                         Number @ ExpectPre    -> ParsePre,
                              V @ ExpectPre    -> ParsePre,
                          Alpha @ ExpectPre    -> ParsePre,

        Whitespace | EndOfInput @ ParsePre     -> EndOfInput,
             Number | Alpha | V @ ParsePre     -> ParsePre,
                            Dot @ ParsePre     -> ExpectPre,
                           Plus @ ParsePre     -> ExpectBuild,

             Number | Alpha | V @ ExpectBuild  -> ParseBuild,

        Whitespace | EndOfInput @ ParseBuild   -> EndOfInput,
             Number | Alpha | V @ ParseBuild   -> ParseBuild,
                            Dot @ ParseBuild   -> ExpectBuild,

        Whitespace | EndOfInput @ EndOfInput   -> EndOfInput,
        );

        let mut accepts = [Accept::None; STATES * CLASSES];
        accept!(accepts:
                                                           Number @ ExpectMajor  -> SaveStart,
                                                       EndOfInput @ ExpectMajor  -> ErrorMissing,
                     Alpha | V | Dot | Hyphen | Plus | Unexpected @ ExpectMajor  -> ErrorUnexpected,

                                                              Dot @ ParseMajor   -> Major,
                                                       EndOfInput @ ParseMajor   -> ErrorMissing,
              Alpha | V | Hyphen | Plus | Whitespace | Unexpected @ ParseMajor   -> ErrorUnexpected,

                                                           Number @ ExpectMinor  -> SaveStart,
                                                       EndOfInput @ ExpectMinor  -> ErrorMissing,
        Alpha | V | Dot | Hyphen | Plus | Whitespace | Unexpected @ ExpectMinor  -> ErrorUnexpected,

                                                              Dot @ ParseMinor   -> RequireMinor,
                                                       EndOfInput @ ParseMinor   -> ErrorMissing,
              Alpha | V | Hyphen | Plus | Whitespace | Unexpected @ ParseMinor   -> ErrorUnexpected,

                                                           Number @ ExpectPatch  -> SaveStart,
                                                       EndOfInput @ ExpectPatch  -> ErrorMissing,
        Alpha | V | Dot | Hyphen | Plus | Whitespace | Unexpected @ ExpectPatch  -> ErrorUnexpected,

                          Hyphen | Plus | Whitespace | EndOfInput @ ParsePatch   -> RequirePatch,
                                     Alpha | V | Dot | Unexpected @ ParsePatch   -> ErrorUnexpected,

                                               Number | V | Alpha @ ExpectPre    -> SaveStart,
                                                       EndOfInput @ ExpectPre    -> ErrorMissing,
                    Dot | Hyphen | Plus | Whitespace | Unexpected @ ExpectPre    -> ErrorUnexpected,

                             Dot | Plus | Whitespace | EndOfInput @ ParsePre     -> Pre,
                                              Hyphen | Unexpected @ ParsePre     -> ErrorUnexpected,

                                               Number | V | Alpha @ ExpectBuild  -> SaveStart,
                                                       EndOfInput @ ExpectBuild  -> ErrorMissing,
                    Dot | Hyphen | Plus | Whitespace | Unexpected @ ExpectBuild  -> ErrorUnexpected,

                                    Dot | Whitespace | EndOfInput @ ParseBuild   -> Build,
                                       Hyphen | Plus | Unexpected @ ParseBuild   -> ErrorUnexpected,

            Alpha | V | Number | Dot | Hyphen | Plus | Unexpected @ EndOfInput   -> ErrorUnexpected,
        );

        (transitions, accepts)
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use semver_v100::Version;
        use test_case::test_case;

        #[test_case("1.2.3")]
        #[test_case("  1.2.4  ")]
        #[test_case("1.2.3-alpha1")]
        #[test_case("  1.2.3-alpha2  ")]
        #[test_case("1.2.3-alpha01.drop02")]
        #[test_case("1.4.1-alpha01")]
        #[test_case("1.3.3-7")]
        #[test_case("1.2.3+build1")]
        #[test_case("  1.2.3+build2  ")]
        #[test_case("1.2.3+build01.drop02")]
        #[test_case("1.4.1+build01")]
        #[test_case("1.2.3-alpha1+build5")]
        #[test_case("   1.2.3-alpha2+build6   ")]
        #[test_case("1.2.3-1.alpha1.9+build5.7.3aedf  ")]
        #[test_case("0.4.0-beta.1+0851523")]
        #[test_case("2.7.3+Final")]
        #[test_case("2.7.3+Release")]
        #[test_case("2.7.3+r")]
        #[test_case("2020.4.9")]
        #[test_case("2020.04.09")]
        #[test_case("2.3.4+1")]
        #[test_case("2.3.4+01")]
        #[test_case("2.3.4+0001")]
        #[test_case("1.2.3+v6")]
        #[test_case("1.2.3-alpha.v4")]
        #[test_case("1.2.3-alpha+v6")]
        #[test_case("1.2.3+build.v4")]
        #[test_case("1.2.3-alpha.v6+build.v7")]
        #[test_case("1.2.3-9876543210987654321098765432109876543211")]
        #[test_case("1.2.3+9876543210987654321098765432109876543213")]
        fn test_positive(input: &str) {
            assert!(parse::<Version>(input).is_ok())
        }

        #[test_case("  "; "spaces")]
        #[test_case("  v2  ")]
        #[test_case("  V5  ")]
        #[test_case("."; "dot")]
        #[test_case(""; "empty")]
        #[test_case("🙈"; "emoji")]
        #[test_case("00001")]
        #[test_case("01")]
        #[test_case("1 abc")]
        #[test_case("1-alpha03")]
        #[test_case("1-v3")]
        #[test_case("1. "; "1 dot space")]
        #[test_case("1."; "1 dot")]
        #[test_case("1.+.0")]
        #[test_case("1.2-v4")]
        #[test_case("1.2. "; "1 2 dot space")]
        #[test_case("1.2.."; "1 2 dot dot space")]
        #[test_case("1.2." ; "1 2 dot")]
        #[test_case("1.2.3 abc")]
        #[test_case("1.2.3- "; "1 2 3 hyphen space")]
        #[test_case("1.2.3--"; "1 2 3 hyphen hyphen")]
        #[test_case("1.2.3-."; "1 2 3 hyphen dot")]
        #[test_case("1.2.3-"; "1 2 3 hyphen")]
        #[test_case("1.2.3-+"; "1 2 3 hyphen plus")]
        #[test_case("1.2.3-🙈")]
        #[test_case("1.2.3-alpha-v5")]
        #[test_case("1.2.3.4- "; "1 2 3 4 hyphen space")]
        #[test_case("1.2.3.4-"; "1 2 3 4 hyphen")]
        #[test_case("1.2.3.9876543210987654321098765432109876543210")]
        #[test_case("1.2.3.RC.4")]
        #[test_case("1.2.3.v4")]
        #[test_case("1.2.3+ "; "1 2 3 plus space")]
        #[test_case("1.2.3+-"; "1 2 3 plus hyphen")]
        #[test_case("1.2.3+."; "1 2 3 plus dot")]
        #[test_case("1.2.3+" ; "1 2 3 plus")]
        #[test_case("1.2.3++"; "1 2 3 plus plus")]
        #[test_case("1.2.3+build-v5")]
        #[test_case("1.2.9876543210987654321098765432109876543210")]
        #[test_case("1.2.v3")]
        #[test_case("1.2")]
        #[test_case("1.2+v5")]
        #[test_case("1.3.3.0")]
        #[test_case("1.3.3.00")]
        #[test_case("1.3.3.07")]
        #[test_case("1.3.3.7-bar")]
        #[test_case("1.3.3.7.04.02")]
        #[test_case("1.3.3.7.4.2")]
        #[test_case("1.3.3.7.foo")]
        #[test_case("1.3.3.7")]
        #[test_case("1.3.3.7+baz")]
        #[test_case("1.3.3.9876543210987654321098765432109876543210.4.2")]
        #[test_case("1.3.3.9876543210987654321098765432109876543210")]
        #[test_case("1.4-alpha02")]
        #[test_case("1.4+build02")]
        #[test_case("1.9.3.RC1")]
        #[test_case("1.9.RC2")]
        #[test_case("1.9876543210987654321098765432109876543210.2")]
        #[test_case("1.9876543210987654321098765432109876543210")]
        #[test_case("1.RC3")]
        #[test_case("1.v2")]
        #[test_case("1")]
        #[test_case("1+build03")]
        #[test_case("1+v4")]
        #[test_case("1🙈"; "1 emoji")]
        #[test_case("123456789012345678901234567890")]
        #[test_case("2-Final")]
        #[test_case("3-r")]
        #[test_case("4-Release")]
        #[test_case("2.7-Final")]
        #[test_case("2.8-r")]
        #[test_case("2.9-Release")]
        #[test_case("2.7.3.Final")]
        #[test_case("2.7.4.r")]
        #[test_case("2.7.5.Release")]
        #[test_case("2.8.Final")]
        #[test_case("2.9.r")]
        #[test_case("2.6.Release")]
        #[test_case("2.5+Final")]
        #[test_case("2.4+r")]
        #[test_case("2.3+Release")]
        #[test_case("3.Final")]
        #[test_case("2.r")]
        #[test_case("3.Release")]
        #[test_case("4+Final")]
        #[test_case("5+r")]
        #[test_case("2+Release")]
        #[test_case("2020.04")]
        #[test_case("2020.4")]
        #[test_case("3.1.0-M13-beta3")]
        #[test_case("3.1.0+build3-r021")]
        #[test_case("5.9.0-202009080501-r")]
        #[test_case("7.2.0+28-2f9fb552")]
        #[test_case("a.b.c")]
        #[test_case("a1.2.3")]
        #[test_case("v v1.2.3")]
        #[test_case("v-2.3.4")]
        #[test_case("v.1.2.3")]
        #[test_case("v")]
        #[test_case("v+3.4.5")]
        #[test_case("v🙈"; "v emoji")]
        #[test_case("v1.2.3")]
        #[test_case("v1.3.3-7")]
        #[test_case("v1")]
        #[test_case("V2.3.4")]
        #[test_case("V3")]
        #[test_case("V4.2.4-2")]
        #[test_case("val")]
        #[test_case("vv1.2.3")]
        fn test_negative(input: &str) {
            assert!(parse::<Version>(input).is_err());
        }
    }
}

/// for benchmarks
#[cfg(all(feature = "generator", feature = "strict"))]
pub mod generator {
    #[cfg(test)]
    use std::collections::HashMap;

    use super::*;

    /// for benchmarks
    pub fn generate_20000(seed: u32) -> String {
        let classes = [
            Class::Number,
            Class::Alpha,
            Class::Dot,
            Class::Hyphen,
            Class::Plus,
        ];
        let dfa = strict::strict_dfa();

        let mut seed = if seed == 0 { 0xBAD_5EED } else { seed };
        let mut state = State::ExpectMajor;
        let mut candidates = [Class::Whitespace; 6];

        let mut result = Vec::with_capacity(20_000);
        let size = 20_000_usize;
        loop {
            let mut cls = 0;
            let mut num_candidates = 0;
            while cls < classes.len() {
                let possible_state = transition(&dfa, state, classes[cls]).0;
                if possible_state != State::Error {
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
            result.push(ch);

            if result.len() >= size && transition(&dfa, state, Class::EndOfInput).0 != State::Error
            {
                break;
            }
        }

        String::from_utf8(result).unwrap()
    }

    const fn char_for(seed: u32, class: Class) -> (u32, u8) {
        match class {
            Class::Number => {
                let (seed, number) = roll(seed, 10);
                (seed, b'0' + number as u8)
            }
            Class::Alpha => {
                let (seed, use_upper) = roll(seed, 2);
                // don't generate a v as v0.2 chokes on that
                let (seed, mut number) = roll(seed, 25);
                // if `v` was selected (21), shift result by 1
                if number >= 21 {
                    number += 1;
                }
                let start = if use_upper == 0 { b'a' } else { b'A' };
                (seed, start + number as u8)
            }
            Class::Dot => (seed, b'.'),
            Class::Hyphen => (seed, b'-'),
            Class::Plus => (seed, b'+'),
            Class::Whitespace | Class::EndOfInput | Class::Unexpected | Class::V => (seed, b' '),
        }
    }

    const fn roll(seed: u32, upper: usize) -> (u32, usize) {
        let x = seed;
        let x = x ^ x.wrapping_shl(13);
        let x = x ^ x.wrapping_shr(17);
        let x = x ^ x.wrapping_shl(5);
        (x, x as usize % upper)
    }

    #[cfg(test)]
    fn dot() -> String {
        struct Node {
            name: String,
            accepts: bool,
        }
        struct Edge {
            from: State,
            to: State,
            matches: String,
            accepts: bool,
        }

        let mut nodes = [
            State::ExpectMajor,
            State::ParseMajor,
            State::ExpectMinor,
            State::ParseMinor,
            State::ExpectPatch,
            State::ParsePatch,
            State::ExpectAdd,
            State::ParseAdd,
            State::ExpectPre,
            State::ParsePre,
            State::ExpectBuild,
            State::ParseBuild,
            State::RequireMajor,
            // State::EndOfInput,
            // State::Error,
        ]
        .iter()
        .map(|s| {
            (
                *s,
                Node {
                    name: format!("{}", s),
                    accepts: false,
                },
            )
        })
        .collect::<HashMap<State, Node>>();

        let classes = [
            Class::Number,
            Class::Alpha,
            Class::Dot,
            Class::Hyphen,
            Class::Plus,
            Class::V,
            Class::Whitespace,
            Class::EndOfInput,
            Class::Unexpected,
        ];

        let edges = nodes
            .iter_mut()
            .map(|(&s, node)| {
                let mut targets = HashMap::new();
                for &c in &classes {
                    let (target, accept) = transition(&DFA, s, c);
                    if target != State::Error {
                        let accepts = accept != Accept::None && accept != Accept::SaveStart;
                        targets
                            .entry((target, accepts))
                            .or_insert_with(Vec::new)
                            .push(c);
                    }
                }
                let ends = targets
                    .remove(&(State::EndOfInput, true))
                    .or(targets.remove(&(State::EndOfInput, false)));

                if ends.is_some() {
                    node.accepts = true;
                }

                (s, targets)
            })
            .collect::<HashMap<State, HashMap<(State, bool), Vec<Class>>>>();

        let edges = edges
            .into_iter()
            .flat_map(|(from, targets)| {
                let targets = targets
                    .into_iter()
                    .map(|((to, accepts), classes)| {
                        let has_alpha = classes.contains(&Class::Alpha);
                        let matches = classes
                            .into_iter()
                            .filter(|c| !has_alpha || *c != Class::V)
                            .map(|c| c.to_string())
                            .collect::<String>();
                        Edge {
                            from,
                            to,
                            matches,
                            accepts,
                        }
                    })
                    .collect::<Vec<Edge>>();
                targets
            })
            .collect::<Vec<Edge>>();

        let mut statements = nodes
            .into_iter()
            .map(|(state, node)| {
                let shape_color = if node.accepts {
                    " shape=doublecircle color=blue3"
                } else {
                    ""
                };
                format!(r#"{}[label="{}"{}]"#, state, node.name, shape_color)
            })
            .collect::<Vec<_>>();

        statements.extend(edges.into_iter().map(
            |Edge {
                 from,
                 to,
                 matches,
                 accepts,
             }| {
                let color = if accepts {
                    " color=green3 fontcolor=green4 penwidth=1.7"
                } else {
                    ""
                };
                format!(r#"{} -> {}[label="{}"{}]"#, from, to, matches, color)
            },
        ));

        statements.insert(
            0,
            String::from(r#"edge [fontname="JetBrains Mono,Fira Code,Monospace"]"#),
        );
        statements.insert(0, String::from(r#"node [margin=0.02 shape=circle]"#));
        statements.insert(0, String::from(r#"graph [rankdir=LR]"#));

        let statements = statements.join(";\n    ");
        format!("digraph dfa {{\n    {};\n}}", statements)
    }

    #[test]
    fn print_dot() {
        println!("{}", dot());
    }
}
