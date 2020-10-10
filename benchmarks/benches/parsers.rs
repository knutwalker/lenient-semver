use criterion::{criterion_group, criterion_main};

criterion_group!(benches, benchmarks::parser_benchmarks);
criterion_main!(benches);
