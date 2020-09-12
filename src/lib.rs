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

pub(crate) fn parse_version(input: &str) -> Result<Version, Error<'_>> {
    match parse_into_version(lex(input)) {
        Ok(result) => Ok(result),
        Err(ErrorSpan { error, span }) => {
            let error = Error { input, span, error };
            Err(error)
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Error<'input> {
    input: &'input str,
    span: Span,
    error: ErrorType<'input>,
}

impl Display for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.error {
            ErrorType::Missing(segment) => {
                write!(f, "Could not parse the {} identifier: No input", segment)?;
            }
            ErrorType::NotANumber(part, _) => {
                write!(
                    f,
                    "Could not parse the {} identifier: `{}` is not a number",
                    part,
                    self.span.show(self.input)
                )?;
            }
            ErrorType::Unexpected(_) => {
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
struct ErrorSpan<'input> {
    error: ErrorType<'input>,
    span: Span,
}

impl<'input> ErrorSpan<'input> {
    fn new(error: ErrorType<'input>, span: Span) -> Self {
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

    fn unexpected(token: Token<'input>, span: Span) -> Self {
        Self {
            error: ErrorType::Unexpected(token),
            span,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum ErrorType<'input> {
    Missing(Segment),
    NotANumber(Part, Token<'input>),
    Unexpected(Token<'input>),
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

fn parse_into_version<'input, I>(tokens: I) -> Result<Version, ErrorSpan<'input>>
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
                    Some(token) => {
                        return Err(ErrorSpan::unexpected(token, tokens.span));
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
                        Some(token) => {
                            return Err(ErrorSpan::unexpected(token, tokens.span));
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

fn parse_number<'input>(
    token: Token<'input>,
    part: Part,
    span: Span,
) -> Result<u64, ErrorSpan<'input>> {
    parse_number_inner(token, part).map_err(|e| ErrorSpan::new(e, span))
}

fn parse_number_inner<'input>(token: Token<'input>, part: Part) -> Result<u64, ErrorType<'input>> {
    match token {
        Token::Number(n) => Ok(n),
        token => Err(ErrorType::NotANumber(part, token)),
    }
}

fn finish_tokens<'input, I, T>(
    mut tokens: Tokens<'input, I>,
    value: T,
) -> Result<T, ErrorSpan<'input>>
where
    I: Iterator<Item = TokenSpan<'input>>,
{
    while let Some(token) = tokens.next() {
        match token {
            Token::Whitespace => {}
            token => return Err(ErrorSpan::unexpected(token, tokens.span)),
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

    #[test]
    fn test_parse() {
        assert_eq!(parse_version("1"), Ok(Version::new(1, 0, 0)));
        assert_eq!(parse_version("1.2"), Ok(Version::new(1, 2, 0)));
        assert_eq!(parse_version("1.2.3"), Ok(Version::new(1, 2, 3)));
        assert_eq!(parse_version("  1.2.3  "), Ok(Version::new(1, 2, 3)));

        assert_eq!(
            parse_version("1.2.3-alpha1"),
            Ok(Version {
                major: 1,
                minor: 2,
                patch: 3,
                pre: vec![Identifier::AlphaNumeric(String::from("alpha1"))],
                build: Vec::new(),
            })
        );
        assert_eq!(
            parse_version("  1.2.3-alpha1  "),
            Ok(Version {
                major: 1,
                minor: 2,
                patch: 3,
                pre: vec![Identifier::AlphaNumeric(String::from("alpha1"))],
                build: Vec::new(),
            })
        );
        assert_eq!(
            parse_version("1.2.3+build5"),
            Ok(Version {
                major: 1,
                minor: 2,
                patch: 3,
                pre: Vec::new(),
                build: vec![Identifier::AlphaNumeric(String::from("build5"))],
            })
        );
        assert_eq!(
            parse_version("  1.2.3+build5  "),
            Ok(Version {
                major: 1,
                minor: 2,
                patch: 3,
                pre: Vec::new(),
                build: vec![Identifier::AlphaNumeric(String::from("build5"))],
            })
        );
        assert_eq!(
            parse_version("1.2.3-alpha1+build5"),
            Ok(Version {
                major: 1,
                minor: 2,
                patch: 3,
                pre: vec![Identifier::AlphaNumeric(String::from("alpha1"))],
                build: vec![Identifier::AlphaNumeric(String::from("build5"))],
            })
        );
        assert_eq!(
            parse_version("  1.2.3-alpha1+build5  "),
            Ok(Version {
                major: 1,
                minor: 2,
                patch: 3,
                pre: vec![Identifier::AlphaNumeric(String::from("alpha1"))],
                build: vec![Identifier::AlphaNumeric(String::from("build5"))],
            })
        );
        assert_eq!(
            parse_version("1.2.3-1.alpha1.9+build5.7.3aedf  "),
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
        assert_eq!(
            parse_version("0.4.0-beta.1+0851523"),
            Ok(Version {
                major: 0,
                minor: 4,
                patch: 0,
                pre: vec![
                    Identifier::AlphaNumeric(String::from("beta")),
                    Identifier::Numeric(1),
                ],
                build: vec![Identifier::AlphaNumeric(String::from("0851523"))],
            })
        );

        assert_eq!(
            parse_version("1.4.0-alpha01"),
            Ok(Version {
                major: 1,
                minor: 4,
                patch: 0,
                pre: vec![Identifier::AlphaNumeric(String::from("alpha01"))],
                build: Vec::new(),
            })
        );

        assert_eq!(
            parse_version("1.5.1-drop02"),
            Ok(Version {
                major: 1,
                minor: 5,
                patch: 1,
                pre: vec![Identifier::AlphaNumeric(String::from("drop02"))],
                build: Vec::new(),
            })
        );
        assert_eq!(
            parse_version("1.5-drop02"),
            Ok(Version {
                major: 1,
                minor: 5,
                patch: 0,
                pre: vec![Identifier::AlphaNumeric(String::from("drop02"))],
                build: Vec::new(),
            })
        );

        assert_eq!(
            parse_version("2.6.8-rc1"),
            Ok(Version {
                major: 2,
                minor: 6,
                patch: 8,
                pre: vec![Identifier::AlphaNumeric(String::from("rc1"))],
                build: Vec::new(),
            })
        );

        assert_eq!(
            parse_version("3.1.0-M13-beta3"),
            Ok(Version {
                major: 3,
                minor: 1,
                patch: 0,
                pre: vec![
                    Identifier::AlphaNumeric(String::from("M13")),
                    Identifier::AlphaNumeric(String::from("beta3")),
                ],
                build: Vec::new(),
            })
        );

        assert_eq!(
            parse_version("1.9.RC2"),
            Ok(Version {
                major: 1,
                minor: 9,
                patch: 0,
                pre: vec![Identifier::AlphaNumeric(String::from("RC2")),],
                build: Vec::new(),
            })
        );

        assert_eq!(
            parse_version("1.7.M05"),
            Ok(Version {
                major: 1,
                minor: 7,
                patch: 0,
                pre: vec![Identifier::AlphaNumeric(String::from("M05")),],
                build: Vec::new(),
            })
        );

        assert_eq!(
            parse_version("2.Final"),
            Ok(Version {
                major: 2,
                minor: 0,
                patch: 0,
                pre: Vec::new(),
                build: vec![Identifier::AlphaNumeric(String::from("Final"))],
            })
        );
        assert_eq!(
            parse_version("2.7.Final"),
            Ok(Version {
                major: 2,
                minor: 7,
                patch: 0,
                pre: Vec::new(),
                build: vec![Identifier::AlphaNumeric(String::from("Final"))],
            })
        );
        assert_eq!(
            parse_version("2.7.3.Final"),
            Ok(Version {
                major: 2,
                minor: 7,
                patch: 3,
                pre: Vec::new(),
                build: vec![Identifier::AlphaNumeric(String::from("Final"))],
            })
        );
        assert_eq!(
            parse_version("2.Release"),
            Ok(Version {
                major: 2,
                minor: 0,
                patch: 0,
                pre: Vec::new(),
                build: vec![Identifier::AlphaNumeric(String::from("Release"))],
            })
        );
        assert_eq!(
            parse_version("2.7.Release"),
            Ok(Version {
                major: 2,
                minor: 7,
                patch: 0,
                pre: Vec::new(),
                build: vec![Identifier::AlphaNumeric(String::from("Release"))],
            })
        );
        assert_eq!(
            parse_version("2.7.3.Release"),
            Ok(Version {
                major: 2,
                minor: 7,
                patch: 3,
                pre: Vec::new(),
                build: vec![Identifier::AlphaNumeric(String::from("Release"))],
            })
        );

        assert_eq!(
            parse_version("7.2.0+28-2f9fb552"),
            Ok(Version {
                major: 7,
                minor: 2,
                patch: 0,
                pre: Vec::new(),
                build: vec![
                    Identifier::Numeric(28),
                    Identifier::AlphaNumeric(String::from("2f9fb552"))
                ],
            })
        );

        assert_eq!(
            parse_version("5.9.0.202009080501-r"),
            Ok(Version {
                major: 5,
                minor: 9,
                patch: 0,
                build: Vec::new(),
                pre: vec![
                    Identifier::Numeric(202009080501),
                    Identifier::AlphaNumeric(String::from("r"))
                ],
                // pre: Vec::new(),
                // build: vec![
                //     Identifier::Numeric(202009080501),
                //     Identifier::AlphaNumeric(String::from("r"))
                // ],
            })
        );

        assert_eq!(parse_version("2020.4.9"), Ok(Version::new(2020, 4, 9)));
        assert_eq!(parse_version("2020.04.09"), Ok(Version::new(2020, 4, 9)));
        assert_eq!(parse_version("2020.04"), Ok(Version::new(2020, 4, 0)));

        assert_eq!(parse_version("2020.04"), Ok(Version::new(2020, 4, 0)));
    }

    #[test]
    fn parse_error() {
        fn parse_version(input: &str) -> Result<Version, ErrorSpan> {
            parse_into_version(lex(input))
        }

        use ErrorType::*;

        assert_eq!(
            parse_version(""),
            Err(ErrorSpan::new(
                Missing(Segment::Part(Part::Major)),
                Span::new(0, 0)
            ))
        );
        assert_eq!(
            parse_version("  "),
            Err(ErrorSpan::new(
                Missing(Segment::Part(Part::Major)),
                Span::new(0, 2)
            ))
        );
        assert_eq!(
            parse_version("1.2.3-"),
            Err(ErrorSpan::new(
                Missing(Segment::PreRelease),
                Span::new(5, 6)
            ))
        );
        assert_eq!(
            parse_version("1.2.3+"),
            Err(ErrorSpan::new(Missing(Segment::Build), Span::new(5, 6)))
        );
        assert_eq!(
            parse_version("a.b.c"),
            Err(ErrorSpan::new(
                NotANumber(Part::Major, Token::Alpha("a")),
                Span::new(0, 1)
            ))
        );
        assert_eq!(
            parse_version("1.+.0"),
            Err(ErrorSpan::new(
                NotANumber(Part::Minor, Token::Plus),
                Span::new(2, 3)
            ))
        );
        assert_eq!(
            parse_version("1.2.."),
            Err(ErrorSpan::new(
                NotANumber(Part::Patch, Token::Dot),
                Span::new(4, 5)
            ))
        );
        assert_eq!(
            parse_version("123456789012345678901234567890"),
            Err(ErrorSpan::new(
                NotANumber(Part::Major, Token::Alpha("123456789012345678901234567890")),
                Span::new(0, 30)
            ))
        );
        assert_eq!(
            parse_version("1.2.3 abc"),
            Err(ErrorSpan::new(
                Unexpected(Token::Alpha("abc")),
                Span::new(6, 9)
            ))
        );
    }

    #[test]
    fn parse_error_string() {
        fn parsed_version(input: &str) -> String {
            format!("{:#}", parse_version(input).unwrap_err())
        }

        assert_eq!(
            parsed_version(""),
            String::from(
                r#"Could not parse the major identifier: No input
|    
|    
"#
            )
        );
        assert_eq!(
            parsed_version("  "),
            String::from(
                r#"Could not parse the major identifier: No input
|      
|    ^^
"#
            )
        );
        assert_eq!(
            parsed_version("1.2.3-"),
            String::from(
                r#"Could not parse the pre-release identifier: No input
|    1.2.3-
|    ~~~~~^
"#
            )
        );
        assert_eq!(
            parsed_version("1.2.3+"),
            String::from(
                r#"Could not parse the build identifier: No input
|    1.2.3+
|    ~~~~~^
"#
            )
        );
        assert_eq!(
            parsed_version("a.b.c"),
            String::from(
                r#"Could not parse the major identifier: `a` is not a number
|    a.b.c
|    ^
"#
            )
        );
        assert_eq!(
            parsed_version("1.+.0"),
            String::from(
                r#"Could not parse the minor identifier: `+` is not a number
|    1.+.0
|    ~~^
"#
            )
        );
        assert_eq!(
            parsed_version("1.2.."),
            String::from(
                r#"Could not parse the patch identifier: `.` is not a number
|    1.2..
|    ~~~~^
"#
            )
        );
        assert_eq!(
            parsed_version("123456789012345678901234567890"),
            String::from(
                r#"Could not parse the major identifier: `123456789012345678901234567890` is not a number
|    123456789012345678901234567890
|    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
"#
            )
        );
        assert_eq!(
            parsed_version("1.2.3 abc"),
            String::from(
                r#"Unexpected `abc`
|    1.2.3 abc
|    ~~~~~~^^^
"#
            )
        );
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
    fn test_parse_version_number() {
        assert_eq!(
            parse_number(Token::Number(42), Part::Major, Span::new(1, 2)),
            Ok(42)
        );
        assert_eq!(
            parse_number_inner(Token::Dot, Part::Patch),
            Err(ErrorType::NotANumber(Part::Patch, Token::Dot))
        );
        assert_eq!(
            parse_number_inner(Token::Plus, Part::Patch),
            Err(ErrorType::NotANumber(Part::Patch, Token::Plus))
        );
        assert_eq!(
            parse_number_inner(Token::Hyphen, Part::Patch),
            Err(ErrorType::NotANumber(Part::Patch, Token::Hyphen))
        );
        assert_eq!(
            parse_number_inner(Token::Whitespace, Part::Patch),
            Err(ErrorType::NotANumber(Part::Patch, Token::Whitespace))
        );
        assert_eq!(
            parse_number_inner(Token::Alpha("foo"), Part::Patch),
            Err(ErrorType::NotANumber(Part::Patch, Token::Alpha("foo")))
        );
        assert_eq!(
            parse_number_inner(Token::UnexpectedChar('🙈', 42), Part::Patch),
            Err(ErrorType::NotANumber(
                Part::Patch,
                Token::UnexpectedChar('🙈', 42)
            ))
        );
    }

    #[test]
    fn test_is_release_identifier() {
        for valid in [
            "Final", "FINAL", "final", "FiNaL", "fInAL", "Release", "RELEASE", "release",
            "ReLeAsE", "rElEAse",
        ]
        .as_ref()
        {
            assert!(is_release_identifier(valid));
        }
    }
}
