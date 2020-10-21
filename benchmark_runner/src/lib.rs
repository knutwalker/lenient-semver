use criterion::{black_box, BenchmarkId, Criterion};
use std::time::Duration;

macro_rules! run_group {
    ($crit:ident, $group:literal, $($name:literal -> $fun:expr),+,) => {{
        let mut group = $crit.benchmark_group($group);
        for &input in ::benchmarks::INPUTS.iter() {
            $(
                let id = BenchmarkId::new($name, input.trim());
                group.bench_with_input(id, input, |b, input| {
                    b.iter(|| $fun(::criterion::black_box(input)))
                });
            )+
        }
        group.finish();
    }};
}

fn parser_benchmarks(c: &mut Criterion) {
    run_group!(c, "semver11",
        "semver" -> ::benchmarks::semver,
        "lenient" -> ::benchmarks::lenient_semver,
        "lite" -> ::benchmarks::lenient_version,
    );

    run_group!(c, "semver10",
        "semver" -> ::benchmarks::semver10,
        "lenient" -> ::benchmarks::lenient_semver10,
        "lenient_0.2" -> ::benchmarks::lenient_02_semver,
        "lite" -> ::benchmarks::lenient_version,
        "lite_0.2" -> ::benchmarks::lenient_02_lite,
    );

    let mut group = c.benchmark_group("regex");
    for &input in ::benchmarks::INPUTS.iter() {
        let id = BenchmarkId::new("semver_rs", input.trim());
        group.bench_with_input(id, input, |b, input| {
            b.iter(|| ::benchmarks::semver_rs(black_box(input)))
        });

        let id = BenchmarkId::new("semver_rs_loose", input.trim());
        group.bench_with_input(id, input, |b, input| {
            b.iter(|| ::benchmarks::semver_rs_loose(black_box(input)))
        });

        let id = BenchmarkId::new("regex", input.trim());
        let re = ::benchmarks::parsing_regex();
        group.bench_with_input(id, &(input, re), |b, (input, re)| {
            b.iter(|| ::benchmarks::regex(re, black_box(input)))
        });
    }
    group.finish();
}

fn crate_benchmarks(c: &mut Criterion) {
    run_group!(c, "crate",
        "lite" -> ::benchmarks::lenient_version,
    );
}

fn criterion(crate_only: bool) -> Criterion {
    let mut criterion = Criterion::default().with_plots();
    if crate_only {
        criterion = criterion
            .sample_size(1_000)
            .confidence_level(0.98)
            .warm_up_time(Duration::from_secs(10))
            .measurement_time(Duration::from_secs(20))
    };
    criterion.configure_from_args()
}

pub fn main() {
    let crate_only = std::env::args().any(|a| &*a == "crate");
    let mut criterion = criterion(crate_only);
    if crate_only {
        crate_benchmarks(&mut criterion)
    } else {
        parser_benchmarks(&mut criterion);
    }
    criterion.final_summary();
}
