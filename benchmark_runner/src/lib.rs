use criterion::{black_box, BenchmarkId, Criterion};

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

pub fn parser_benchmarks(c: &mut Criterion) {
    run_group!(c, "semver11",
        "semver" -> ::benchmarks::semver,
        "lenient" -> ::benchmarks::lenient_semver,
        "lite" -> ::benchmarks::lenient_version,
        "liteu8" -> ::benchmarks::lenient_version_u8,
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
