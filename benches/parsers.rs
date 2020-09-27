use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

use lenient_semver::{parse, VersionLite};
use regex::Regex;
use semver::{Identifier, Version};
use semver_rs::Version as VersionRs;

const INPUT_S: &str = "1.0.0";
const INPUT_XL: &str = "  1.2.3-1.alpha1.9+build5.7.3aedf.01337  ";

fn regex_parser(re: &Regex, input: &str) -> Option<Version> {
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

fn bench_parsers(c: &mut Criterion) {
    let mut group = c.benchmark_group("Parser");

    for &input in [INPUT_S, INPUT_XL].iter() {
        let lenient_semver = BenchmarkId::new("lenient_parser_semver", input);
        group.bench_with_input(lenient_semver, input, |b, input| {
            b.iter(|| parse::<Version>(black_box(input)).unwrap())
        });
        let lenient_lite = BenchmarkId::new("lenient_parser_lite", input);
        group.bench_with_input(lenient_lite, input, |b, input| {
            b.iter(|| parse::<VersionLite<'_>>(black_box(input)).unwrap())
        });
        let semver = BenchmarkId::new("semver_parser", input);
        group.bench_with_input(semver, input, |b, input| {
            b.iter(|| Version::parse(black_box(input)).unwrap())
        });
        let semver_rs = BenchmarkId::new("semver_rs_parser", input);
        group.bench_with_input(semver_rs, input, |b, input| {
            b.iter(|| Version::parse(black_box(input)).unwrap())
        });

        let regex = BenchmarkId::new("regex_parser", input);
        let re = Regex::new(r"^\s*(?P<major>0|[1-9]\d*)\.(?P<minor>0|[1-9]\d*)\.(?P<patch>0|[1-9]\d*)(?:-(?P<prerelease>(?:0|[1-9]\d*|\d*[a-zA-Z-][0-9a-zA-Z-]*)(?:\.(?:0|[1-9]\d*|\d*[a-zA-Z-][0-9a-zA-Z-]*))*))?(?:\+(?P<buildmetadata>[0-9a-zA-Z-]+(?:\.[0-9a-zA-Z-]+)*))?\s*$").unwrap();
        group.bench_with_input(regex, &(input, re), |b, (input, re)| {
            b.iter(|| regex_parser(re, black_box(input)).unwrap())
        });
    }

    group.finish();
}

criterion_group!(benches, bench_parsers);
criterion_main!(benches);
