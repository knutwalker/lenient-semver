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

//! Lenient parser for Semantic Version numbers.
//!
//! ## Motivation
//!
//! This crate aims to provide an alternative parser for [semver `Version`s](https://crates.io/crates/semver).
//!
//! Instead of adhering to the semver specification, this parser is more lenient in what it allows.
//! The differenc include:
//!
//! - Minor and Path are optional an default to 0 (e.g. "1" parses at "1.0.0")
//! - Pre-release identifier may be separated by `.` as well (e.g. "1.2.3.rc1" parses at "1.2.3-rc1")
//! - Some pre-release identifiers are parsed as build identifier (e.g. "1.2.3.Final" parses at "1.2.3+Final")
//!

use semver::{Identifier, Version};
use std::fmt::Display;

/// Parse a string slice into a Version
pub fn parse_version(input: &str) -> Result<Version, Error<'_>> {
    match parse_into_version(lex(input)) {
        Ok(result) => Ok(result),
        Err(ErrorSpan { error, span }) => {
            let error = Error { input, span, error };
            Err(error)
        }
    }
}

/// Possible errors that happen during parsing
/// and the location of the token where the error occurred.
#[derive(Debug, PartialEq, Eq)]
pub struct Error<'input> {
    input: &'input str,
    span: Span,
    error: ErrorType,
}

impl Display for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.error {
            ErrorType::Missing(segment) => {
                write!(f, "Could not parse the {} identifier: No input", segment)?;
            }
            ErrorType::NotANumber(part) => {
                write!(
                    f,
                    "Could not parse the {} identifier: `{}` is not a number",
                    part,
                    self.span.show(self.input)
                )?;
            }
            ErrorType::Unexpected => {
                write!(f, "Unexpected `{}`", self.span.show(self.input))?;
            }
        };
        if f.alternate() {
            writeln!(f)?;
            writeln!(f, "|    {}", self.input)?;
            write!(
                f,
                "|    {0:~<start$}{1:^<width$}",
                "",
                "",
                start = self.span.start,
                width = self.span.end - self.span.start
            )?;
            writeln!(f)?
        }
        Ok(())
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

#[derive(Debug, PartialEq, Eq)]
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
        if let Some(old) = self.stash.replace(token) {
            panic!("double stash, old value: {:?}", old)
        }
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

fn parse_into_version<'input, I>(tokens: I) -> Result<Version, ErrorSpan>
where
    I: IntoIterator<Item = TokenSpan<'input>>,
{
    let tokens = tokens.into_iter();
    let mut tokens = Tokens::new(tokens);
    let mut version = Version::new(0, 0, 0);
    let mut state = State::Part(Part::Major);

    loop {
        match state {
            State::Part(Part::Major) => match tokens.next() {
                // unexpected end
                None => return Err(ErrorSpan::missing_part(Part::Major, tokens.span)),
                // skip initial whitespace
                Some(Token::Whitespace) => {}
                Some(token) => {
                    version.major = parse_number(token, Part::Major, tokens.span)?;
                    state = match tokens.next() {
                        None => return Ok(version),
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
                    version.build.push(Identifier::AlphaNumeric(v.into()));
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
                    let num = parse_number(token, part, tokens.span)?;
                    match part {
                        Part::Major => unreachable!(),
                        Part::Minor => version.minor = num,
                        Part::Patch => version.patch = num,
                    }
                    state = match tokens.next() {
                        None => return Ok(version),
                        Some(Token::Dot) => match part {
                            Part::Major => unreachable!(),
                            Part::Minor => State::Part(Part::Patch),
                            Part::Patch => State::PreRelease,
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
                        version.build.push(Identifier::AlphaNumeric(v.into()));
                        return finish_tokens(tokens, version);
                    }
                    // regular pre-release part
                    Some(Token::Alpha(v)) => {
                        version.pre.push(Identifier::AlphaNumeric(v.into()));
                    }
                    // regular pre-release part
                    Some(Token::Number(v)) => {
                        version.pre.push(Identifier::Numeric(v));
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
                state = match tokens.next() {
                    None => return Ok(version),
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
                            version.build.push(Identifier::AlphaNumeric(v.into()));
                        }
                        // regular build part
                        Some(Token::Number(v)) => {
                            version.build.push(Identifier::Numeric(v));
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
                        None => return Ok(version),
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

fn parse_number<'input>(token: Token<'input>, part: Part, span: Span) -> Result<u64, ErrorSpan> {
    parse_number_inner(token, part).map_err(|e| ErrorSpan::new(e, span))
}

fn parse_number_inner<'input>(token: Token<'input>, part: Part) -> Result<u64, ErrorType> {
    match token {
        Token::Number(n) => Ok(n),
        _ => Err(ErrorType::NotANumber(part)),
    }
}

fn finish_tokens<'input, I, T>(mut tokens: Tokens<'input, I>, value: T) -> Result<T, ErrorSpan>
where
    I: Iterator<Item = TokenSpan<'input>>,
{
    while let Some(token) = tokens.next() {
        match token {
            Token::Whitespace => {}
            _ => return Err(ErrorSpan::unexpected(tokens.span)),
        }
    }
    Ok(value)
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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Span {
    start: usize,
    end: usize,
}

impl Span {
    fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    fn show<'input>(&self, input: &'input str) -> &'input str {
        &input[self.start..self.end]
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
    /// `.`
    Dot,
    /// `+`
    Plus,
    /// `-`
    Hyphen,
    /// Error cases
    UnexpectedChar(char, usize),
}

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
                Ok(number) => Token::Number(number),
                Err(_) => Token::Alpha(number),
            };
            return Some(TokenSpan::new(start, end, token));
        }
        if c.is_alphanumeric() {
            let mut end = self.input.len();
            while let Some((j, c)) = self.chars.next() {
                if !c.is_alphanumeric() {
                    end = j;
                    self.peeked = Some((j, c));
                    break;
                }
            }
            let token = Token::Alpha(&self.input[start..end]);
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
    use semver::Identifier;
    use test_case::test_case;

    trait IntoIdentifier {
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

        ($major:literal . $minor:literal . $patch:literal pre $( $pre:literal )-+ ; build $( $build:literal )-+ ) => {
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
        parse_version(input)
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
    #[test_case("1.3.3.7" => Ok(vers!(1 . 3 . 3 - 7)))]
    #[test_case("5.9.0.202009080501-r" => Ok(vers!(5 . 9 . 0 - 202009080501 - "r")))] // This should really be a + build
    fn test_pre_release(input: &str) -> Result<Version, Error<'_>> {
        parse_version(input)
    }

    #[test_case("1.2.3+build1" => Ok(vers!(1 . 2 . 3 + "build1")))]
    #[test_case("  1.2.3+build2  " => Ok(vers!(1 . 2 . 3 + "build2")))]
    #[test_case("3.1.0+build3-r021" => Ok(vers!(3 . 1 . 0 + "build3" - "r021")))]
    #[test_case("1.2.3+build01.drop02" => Ok(vers!(1 . 2 . 3 + "build01" - "drop02")))]
    #[test_case("1.4.1+build01" => Ok(vers!(1 . 4 . 1 + "build01")))]
    #[test_case("1.4+build02" => Ok(vers!(1 . 4 . 0 + "build02")))]
    #[test_case("1+build03" => Ok(vers!(1 . 0 . 0 + "build03")))]
    #[test_case("7.2.0+28-2f9fb552" => Ok(vers!(7 . 2 . 0 + 28 -  "2f9fb552" )))]
    fn test_build(input: &str) -> Result<Version, Error<'_>> {
        parse_version(input)
    }

    #[test_case("1.2.3-alpha1+build5" => Ok(vers!(1 . 2 . 3 pre "alpha1" ; build "build5" )))]
    #[test_case("   1.2.3-alpha2+build6   " => Ok(vers!(1 . 2 . 3 pre "alpha2" ; build "build6" )))]
    #[test_case("1.2.3-1.alpha1.9+build5.7.3aedf  " => Ok(vers!(1 . 2 . 3 pre 1 - "alpha1" - 9 ; build "build5" - 7 - "3aedf" )))]
    #[test_case("0.4.0-beta.1+0851523" => Ok(vers!(0 . 4 . 0 pre "beta" - 1 ; build "0851523" )))]
    fn test_combined(input: &str) -> Result<Version, Error<'_>> {
        parse_version(input)
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
    fn test_with_release_identifier(input: &str) -> Result<Version, Error<'_>> {
        parse_version(input)
    }

    #[test_case("2020.4.9" => Ok(vers!(2020 . 4 . 9)))]
    #[test_case("2020.04.09" => Ok(vers!(2020 . 4 . 9)))]
    #[test_case("2020.4" => Ok(vers!(2020 . 4 . 0)))]
    #[test_case("2020.04" => Ok(vers!(2020 . 4 . 0)))]
    fn test_date_versions(input: &str) -> Result<Version, Error<'_>> {
        parse_version(input)
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
    #[test_case("a.b.c" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Major), Span::new(0, 1))))]
    #[test_case("1.+.0" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Minor), Span::new(2, 3))))]
    #[test_case("1.2.." => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Patch), Span::new(4, 5))))]
    #[test_case("123456789012345678901234567890" => Err(ErrorSpan::new(ErrorType::NotANumber(Part::Major), Span::new(0, 30))))]
    #[test_case("1 abc" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(2, 5))))]
    #[test_case("1.2.3 abc" => Err(ErrorSpan::new(ErrorType::Unexpected, Span::new(6, 9))))]
    fn test_simple_errors(input: &str) -> Result<Version, ErrorSpan> {
        parse_into_version(lex(input))
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
        format!("{:#}", parse_version(input).unwrap_err())
    }

    #[test]
    fn test_lexer() {
        let tokens = lex("  1.2.3-1.alpha1.9+build5.7.3aedf  ")
            .map(|s| s.token)
            .collect::<Vec<_>>();
        assert_eq!(
            tokens,
            vec![
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
            ]
        );
    }
    #[test]
    fn test_lexer_numbers() {
        let tokens = lex("1.0.00.08.09").map(|s| s.token).collect::<Vec<_>>();
        assert_eq!(
            tokens,
            vec![
                Token::Number(1),
                Token::Dot,
                Token::Number(0),
                Token::Dot,
                Token::Number(0),
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
            parse_into_version(tokens.into_iter().map(|t| TokenSpan {
                token: t,
                span: Span::new(1, 2)
            })),
            Ok(Version {
                major: 1,
                minor: 2,
                patch: 3,
                pre: vec![
                    Identifier::Numeric(1),
                    Identifier::AlphaNumeric(String::from("alpha1")),
                    Identifier::Numeric(9),
                ],
                build: vec![
                    Identifier::AlphaNumeric(String::from("build5")),
                    Identifier::Numeric(7),
                    Identifier::AlphaNumeric(String::from("3aedf")),
                ],
            })
        );
    }

    #[test]
    fn parse_version_number() {
        assert_eq!(
            parse_number(Token::Number(42), Part::Major, Span::new(1, 2)),
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
        parse_number_inner(token, part)
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

    #[test_case("1.2.3" => parse_version("1.2.3.Final"); "dot final")]
    #[test_case("1.2.3" => parse_version("1.2.3.Release"); "dot release")]
    #[test_case("1.2.3" => parse_version("1.2.3-Final"); "hyphen final")]
    #[test_case("1.2.3" => parse_version("1.2.3-Release"); "hyphen release")]
    #[test_case("1.2.3" => parse_version("1.2.3+Final"); "plus final")]
    #[test_case("1.2.3" => parse_version("1.2.3+Release"); "plus release")]
    fn test_release_cmp(v: &str) -> Result<Version, Error<'_>> {
        parse_version(v)
    }
}
