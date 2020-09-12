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

use std::{fmt::Display, num::ParseIntError};

use semver::{Identifier, Version};

pub(crate) fn parse_version(input: &str) -> Result<Version, Error> {
    parse_tokens(lex(input))
}

// TODO: struct with pos

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Error {
    NonNumeric(Part, String),
    Missing(Segment),
    // TODO: add slice
    // parse_error("Extra junk after valid version:  abc")
    ExtraJunk,
    Other(String),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Part {
    Major,
    Minor,
    Patch,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Segment {
    Part(Part),
    PreRelease,
    Build,
}

#[derive(Debug, Copy, Clone)]
enum State {
    Part(Part),
    PreRelease,
    Build,
}

fn parse_tokens<'input, I>(tokens: I) -> Result<Version, Error>
where
    I: IntoIterator<Item = Token<'input>>,
{
    let tokens = tokens.into_iter();
    let mut tokens = tokens.skip_while(|t| matches!(t, Token::Whitespace(_)));

    let mut version = Version::new(0, 0, 0);
    version.major = expect_version_number(&mut tokens, Part::Major)?;

    let mut state = match tokens.next() {
        Some(Token::Dot) => State::Part(Part::Minor),
        Some(Token::Hyphen) => State::PreRelease,
        Some(Token::Plus) => State::Build,
        Some(token) => return finish_tokens(token.chain(tokens), version),
        None => return Ok(version),
    };

    let mut pre_release: Option<Token<'input>> = None;

    loop {
        match state {
            State::Part(part) => {
                match tokens.next() {
                    // things like 1.Final, early stop with a single build identifier
                    Some(Token::Alpha(v)) if is_release_identifier(v) => {
                        version.build.push(Identifier::AlphaNumeric(v.into()));
                        return finish_tokens(tokens, version);
                    }
                    // any alpha token skips right into pre-release parsing
                    Some(Token::Alpha(v)) => {
                        pre_release = Some(Token::Alpha(v));
                        state = State::PreRelease;
                    }
                    // unexpected end
                    Some(Token::Whitespace(_)) | None => {
                        return Err(Error::Missing(Segment::Part(part)));
                    }
                    // any other token is tried as a number
                    Some(token) => {
                        let num = parse_version_number(token, part)?;
                        match part {
                            Part::Major => unreachable!(),
                            Part::Minor => version.minor = num,
                            Part::Patch => version.patch = num,
                        }
                        state = match tokens.next() {
                            Some(Token::Dot) => match part {
                                Part::Major => unreachable!(),
                                Part::Minor => State::Part(Part::Patch),
                                Part::Patch => State::PreRelease,
                            },
                            Some(Token::Hyphen) => State::PreRelease,
                            Some(Token::Plus) => State::Build,
                            Some(token) => return finish_tokens(token.chain(tokens), version),
                            None => return Ok(version),
                        };
                    }
                }
            }
            State::PreRelease => {
                let token = pre_release.take().or_else(|| tokens.next());
                match token {
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
                    Some(Token::Whitespace(_)) | None => {
                        return Err(Error::Missing(Segment::PreRelease));
                    }
                    // any other token is invalid
                    Some(token) => {
                        return Err(invalid_token(token));
                    }
                }
                state = match tokens.next() {
                    Some(Token::Dot) | Some(Token::Hyphen) => State::PreRelease,
                    Some(Token::Plus) => State::Build,
                    Some(token) => return finish_tokens(token.chain(tokens), version),
                    None => return Ok(version),
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
                        Some(Token::Whitespace(_)) | None => {
                            return Err(Error::Missing(Segment::Build));
                        }
                        // any other token is invalid
                        Some(token) => {
                            return Err(invalid_token(token));
                        }
                    }
                    match tokens.next() {
                        Some(Token::Dot) | Some(Token::Hyphen) => {
                            // try next build token
                        }
                        Some(token) => return finish_tokens(token.chain(tokens), version),
                        None => return Ok(version),
                    };
                }
            }
        }
    }
}

fn expect_version_number<'input, I>(tokens: &mut I, part: Part) -> Result<u64, Error>
where
    I: Iterator<Item = Token<'input>>,
{
    let token = tokens
        .next()
        .ok_or_else(|| Error::Missing(Segment::Part(part)))?;
    parse_version_number(token, part)
}

fn parse_version_number<'input>(token: Token<'input>, part: Part) -> Result<u64, Error> {
    match token {
        Token::Number(n) => Ok(n),
        Token::InvalidNumber(input, error) => Err(Error::NonNumeric(
            part,
            format!("`{}` cannot be parsed into a number: {}", input, error),
        )),
        Token::Alpha(_)
        | Token::Whitespace(_)
        | Token::Dot
        | Token::Plus
        | Token::Hyphen
        | Token::UnexpectedChar(_, _) => Err(Error::NonNumeric(
            part,
            format!("`{}` is not a number", token),
        )),
    }
}

fn finish_tokens<'input, I, T>(tokens: I, value: T) -> Result<T, Error>
where
    I: Iterator<Item = Token<'input>>,
{
    for token in tokens {
        match token {
            Token::Whitespace(_) => {}
            _ => return Err(invalid_token(token)),
        }
    }
    Ok(value)
}

fn invalid_token<'input>(token: Token<'input>) -> Error {
    match token {
        Token::UnexpectedChar(c, pos) => {
            Error::Other(format!("Unexpected character `{}` at position {}", c, pos))
        }
        Token::InvalidNumber(input, error) => {
            Error::Other(format!("Unexpected number `{}`: {}", input, error))
        }
        _ => Error::ExtraJunk,
    }
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
enum Token<'input> {
    /// Any unicode whitespace
    Whitespace(&'input str),
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
    InvalidNumber(&'input str, ParseIntError),
    UnexpectedChar(char, usize),
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Token<'input>;

    fn next(&mut self) -> Option<Self::Item> {
        let (i, c) = self.peeked.take()?;
        if c.is_whitespace() {
            let mut end = self.input.len();
            while let Some((j, c)) = self.chars.next() {
                if !c.is_whitespace() {
                    end = j;
                    self.peeked = Some((j, c));
                    break;
                }
            }
            return Some(Token::Whitespace(&self.input[i..end]));
        }
        if c.is_ascii_digit() {
            let mut end = self.input.len();
            let mut is_alpha = false;
            while let Some((j, c)) = self.chars.next() {
                if c.is_ascii_digit() {
                    continue;
                }
                if c.is_alphanumeric() {
                    is_alpha = true;
                    continue;
                }
                end = j;
                self.peeked = Some((j, c));
                break;
            }
            let number = &self.input[i..end];
            if is_alpha {
                return Some(Token::Alpha(number));
            }
            let token = match number.parse::<u64>() {
                Ok(number) => Token::Number(number),
                Err(e) => Token::InvalidNumber(number, e),
            };
            return Some(token);
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
            return Some(Token::Alpha(&self.input[i..end]));
        }
        let token = match c {
            '.' => Token::Dot,
            '-' => Token::Hyphen,
            '+' => Token::Plus,
            _ => Token::UnexpectedChar(c, i),
        };

        self.peeked = self.chars.next();
        Some(token)
    }
}

impl<'input> Display for Token<'input> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Whitespace(s) => s.fmt(f),
            Token::Number(n) => n.fmt(f),
            Token::Alpha(s) => s.fmt(f),
            Token::Dot => f.write_str("."),
            Token::Plus => f.write_str("+"),
            Token::Hyphen => f.write_str("-"),
            Token::InvalidNumber(s, _) => s.fmt(f),
            Token::UnexpectedChar(c, _) => f.write_fmt(format_args!("{}", c)),
        }
    }
}

impl<'input> IntoIterator for Token<'input> {
    type Item = Self;

    type IntoIter = std::iter::Once<Self>;

    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(self)
    }
}

impl<'input> Token<'input> {
    fn chain<I>(self, other: I) -> std::iter::Chain<std::iter::Once<Self>, I>
    where
        I: Iterator<Item = Self>,
    {
        self.into_iter().chain(other)
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
        use Error::*;

        assert_eq!(parse_version(""), Err(Missing(Segment::Part(Part::Major))));
        assert_eq!(
            parse_version("  "),
            Err(Missing(Segment::Part(Part::Major)))
        );
        assert_eq!(parse_version("1.2.3-"), Err(Missing(Segment::PreRelease)));
        assert_eq!(parse_version("1.2.3+"), Err(Missing(Segment::Build)));
        assert_eq!(
            parse_version("a.b.c"),
            Err(NonNumeric(Part::Major, String::from("`a` is not a number")))
        );
        assert_eq!(
            parse_version("1.+.0"),
            Err(NonNumeric(Part::Minor, String::from("`+` is not a number")))
        );
        assert_eq!(
            parse_version("1.2.."),
            Err(NonNumeric(Part::Patch, String::from("`.` is not a number")))
        );
        assert_eq!(
            parse_version("123456789012345678901234567890"),
            Err(NonNumeric(Part::Major, String::from("`123456789012345678901234567890` cannot be parsed into a number: number too large to fit in target type")))
        );
        assert_eq!(parse_version("1.2.3 abc"), Err(ExtraJunk));
    }

    #[test]
    fn test_lexer() {
        let tokens = lex("  1.2.3-1.alpha1.9+build5.7.3aedf  ").collect::<Vec<_>>();
        assert_eq!(
            tokens,
            vec![
                Token::Whitespace("  "),
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
                Token::Whitespace("  "),
            ]
        );
    }
    #[test]
    fn test_lexer_numbers() {
        let tokens = lex("1.0.00.08.09").collect::<Vec<_>>();
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
        let err = input.parse::<u64>().unwrap_err();
        let tokens = lex(input).collect::<Vec<_>>();
        assert_eq!(tokens, vec![Token::InvalidNumber(input, err)]);
    }

    #[test]
    fn test_lexer_invalid_token() {
        let input = "!#∰~[🙈]";
        let tokens = lex(input).collect::<Vec<_>>();
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
        let tokens = lex(input).collect::<Vec<_>>();
        assert_eq!(tokens, vec![Token::Whitespace(input)]);
    }

    #[test]
    fn test_parse_tokens() {
        let tokens = vec![
            Token::Whitespace("  "),
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
            Token::Whitespace("  "),
        ];

        assert_eq!(
            parse_tokens(tokens),
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
        assert_eq!(parse_version_number(Token::Number(42), Part::Major), Ok(42));
        assert_eq!(
            parse_version_number(
                Token::InvalidNumber(" ", " ".parse::<u64>().unwrap_err()),
                Part::Minor
            ),
            Err(Error::NonNumeric(
                Part::Minor,
                String::from("` ` cannot be parsed into a number: invalid digit found in string")
            ))
        );
        assert_eq!(
            parse_version_number(Token::Dot, Part::Patch),
            Err(Error::NonNumeric(
                Part::Patch,
                String::from("`.` is not a number")
            ))
        );
        assert_eq!(
            parse_version_number(Token::Plus, Part::Patch),
            Err(Error::NonNumeric(
                Part::Patch,
                String::from("`+` is not a number")
            ))
        );
        assert_eq!(
            parse_version_number(Token::Hyphen, Part::Patch),
            Err(Error::NonNumeric(
                Part::Patch,
                String::from("`-` is not a number")
            ))
        );
        assert_eq!(
            parse_version_number(Token::Whitespace("  "), Part::Patch),
            Err(Error::NonNumeric(
                Part::Patch,
                String::from("`  ` is not a number")
            ))
        );
        assert_eq!(
            parse_version_number(Token::Alpha("foo"), Part::Patch),
            Err(Error::NonNumeric(
                Part::Patch,
                String::from("`foo` is not a number")
            ))
        );
        assert_eq!(
            parse_version_number(Token::UnexpectedChar('🙈', 42), Part::Patch),
            Err(Error::NonNumeric(
                Part::Patch,
                String::from("`🙈` is not a number")
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
