use criterion::{criterion_group, criterion_main};

criterion_group!(benches, benchmark_runner::parser_benchmarks);
criterion_main!(benches);
