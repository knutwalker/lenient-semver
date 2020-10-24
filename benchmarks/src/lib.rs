use lenient_semver_02::{parse as parse_02, VersionLite as VersionLite02};
use lenient_semver_parser::parse;
use lenient_version::Version as VersionLite;
use regex::Regex;
use semver::{Identifier, Version};
use semver10::Version as Version10;
use semver_rs::{Options, Version as VersionRs};

const INPUT_S: &str = "1.0.0";
const INPUT_XL: &str = "  1.2.3-1.alpha1.9+build5.7.3aedf.01337  ";
pub const INPUTS: [&str; 2] = [INPUT_S, INPUT_XL];

pub fn mega_input() -> String {
    let data = lenient_semver_parser::generator::generate_20000(42);
    let data = Vec::from(data);
    String::from_utf8(data).unwrap()
}

#[inline(always)]
pub fn lenient_semver(input: &str) -> Version {
    parse::<Version>(input).unwrap()
}

#[inline(always)]
pub fn lenient_version(input: &str) -> VersionLite {
    parse::<VersionLite>(input).unwrap()
}

#[inline(always)]
pub fn lenient_semver10(input: &str) -> Version10 {
    parse::<Version10>(input).unwrap()
}

#[inline(always)]
pub fn lenient_02_semver(input: &str) -> Version10 {
    parse_02::<Version10>(input).unwrap()
}

#[inline(always)]
pub fn lenient_02_lite(input: &str) -> VersionLite02 {
    parse_02::<VersionLite02>(input).unwrap()
}

#[inline(always)]
pub fn semver(input: &str) -> Version {
    Version::parse(input).unwrap()
}

#[inline(always)]
pub fn semver10(input: &str) -> Version10 {
    Version10::parse(input).unwrap()
}

#[inline(always)]
pub fn semver_rs(input: &str) -> VersionRs {
    VersionRs::new(input).parse().unwrap()
}

#[inline(always)]
pub fn semver_rs_loose(input: &str) -> VersionRs {
    VersionRs::new(input)
        .with_options(Options::builder().loose(true).build())
        .parse()
        .unwrap()
}

#[inline(always)]
pub fn regex(re: &Regex, input: &str) -> Version {
    regex_parser(re, input).unwrap()
}

pub fn parsing_regex() -> Regex {
    Regex::new(r"^\s*(?P<major>0|[1-9]\d*)\.(?P<minor>0|[1-9]\d*)\.(?P<patch>0|[1-9]\d*)(?:-(?P<prerelease>(?:0|[1-9]\d*|\d*[a-zA-Z-][0-9a-zA-Z-]*)(?:\.(?:0|[1-9]\d*|\d*[a-zA-Z-][0-9a-zA-Z-]*))*))?(?:\+(?P<buildmetadata>[0-9a-zA-Z-]+(?:\.[0-9a-zA-Z-]+)*))?\s*$").unwrap()
}

pub fn regex_parser(re: &Regex, input: &str) -> Option<Version> {
    let caps = re.captures(input)?;

    let mut version = Version::new(
        caps.name("major")?.as_str().parse().unwrap(),
        caps.name("minor")?.as_str().parse().unwrap(),
        caps.name("patch")?.as_str().parse().unwrap(),
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

    Some(version)
}

#[cfg(test)]
mod tests {
    use super::*;
    use lenient_semver_02::IdentifierLite as IdentifierLite02;
    use semver10::Identifier as Identifier10;
    use test_case::test_case;

    fn expected_s_11() -> Version {
        Version::new(1, 0, 0)
    }

    fn expected_s_10() -> Version10 {
        Version10::new(1, 0, 0)
    }

    fn expected_s_lite() -> VersionLite<'static> {
        VersionLite::new(1, 0, 0)
    }

    fn expected_s_lite_02() -> VersionLite02<'static> {
        let mut v = VersionLite02::default();
        v.major = 1;
        v
    }

    fn expected_s_rs() -> VersionRs {
        VersionRs::from_parts(1, 0, 0, None)
    }

    fn expected_xl_11() -> Version {
        Version {
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
                Identifier::AlphaNumeric(String::from("01337")),
            ],
        }
    }

    fn expected_xl_10() -> Version10 {
        Version10 {
            major: 1,
            minor: 2,
            patch: 3,
            pre: vec![
                Identifier10::Numeric(1),
                Identifier10::AlphaNumeric(String::from("alpha1")),
                Identifier10::Numeric(9),
            ],
            build: vec![
                Identifier10::AlphaNumeric(String::from("build5")),
                Identifier10::Numeric(7),
                Identifier10::AlphaNumeric(String::from("3aedf")),
                Identifier10::AlphaNumeric(String::from("01337")),
            ],
        }
    }

    fn expected_xl_lite() -> VersionLite<'static> {
        VersionLite {
            major: 1,
            minor: 2,
            patch: 3,
            additional: Vec::new(),
            pre: vec!["1", "alpha1", "9"],
            build: vec!["build5", "7", "3aedf", "01337"],
        }
    }

    fn expected_xl_lite_02() -> VersionLite02<'static> {
        VersionLite02 {
            major: 1,
            minor: 2,
            patch: 3,
            pre: vec![
                IdentifierLite02::Numeric(1),
                IdentifierLite02::AlphaNumeric("alpha1"),
                IdentifierLite02::Numeric(9),
            ],
            build: vec![
                IdentifierLite02::AlphaNumeric("build5"),
                IdentifierLite02::Numeric(7),
                IdentifierLite02::AlphaNumeric("3aedf"),
                IdentifierLite02::AlphaNumeric("01337"),
            ],
        }
    }

    fn expected_xl_rs() -> VersionRs {
        VersionRs::from_parts(1, 2, 3, Some(String::from("1.alpha1.9")))
    }

    #[test_case(INPUT_S => expected_s_11())]
    #[test_case(INPUT_XL => expected_xl_11())]
    fn test_lenient_semver(input: &str) -> Version {
        lenient_semver(input)
    }

    #[test_case(INPUT_S => expected_s_lite())]
    #[test_case(INPUT_XL => expected_xl_lite())]
    fn test_lenient_lite(input: &str) -> VersionLite {
        lenient_version(input)
    }

    #[test_case(INPUT_S => expected_s_10())]
    #[test_case(INPUT_XL => expected_xl_10())]
    fn test_lenient_semver10(input: &str) -> Version10 {
        lenient_semver10(input)
    }

    #[test_case(INPUT_S => expected_s_lite_02())]
    #[test_case(INPUT_XL => expected_xl_lite_02())]
    fn test_lenient_02_lite(input: &str) -> VersionLite02 {
        lenient_02_lite(input)
    }

    #[test_case(INPUT_S => expected_s_10())]
    #[test_case(INPUT_XL => expected_xl_10())]
    fn test_lenient_02_semver10(input: &str) -> Version10 {
        lenient_02_semver(input)
    }

    #[test_case(INPUT_S => expected_s_11())]
    #[test_case(INPUT_XL => expected_xl_11())]
    fn test_semver(input: &str) -> Version {
        semver(input)
    }

    #[test_case(INPUT_S => expected_s_10())]
    #[test_case(INPUT_XL => expected_xl_10())]
    fn test_semver10(input: &str) -> Version10 {
        semver10(input)
    }

    #[test_case(INPUT_S => expected_s_rs())]
    #[test_case(INPUT_XL => expected_xl_rs())]
    fn test_semver_rs(input: &str) -> VersionRs {
        semver_rs(input)
    }

    #[test_case(INPUT_S => expected_s_rs())]
    #[test_case(INPUT_XL => expected_xl_rs())]
    fn test_semver_rs_loose(input: &str) -> VersionRs {
        semver_rs_loose(input)
    }

    #[test_case(INPUT_S => expected_s_11())]
    #[test_case(INPUT_XL => expected_xl_11())]
    fn test_regex(input: &str) -> Version {
        let re = parsing_regex();
        regex(&re, input)
    }
}
