use criterion::{BenchmarkId, Criterion /*,Throughput*/, criterion_group, criterion_main};
use mule_map::MuleMap;
use rand::distr::Distribution;
use rand::distr::Uniform;
use rand::rng;
use rand::seq::SliceRandom;
use std::collections::HashMap;
use std::num::NonZero;
use std::time::Duration;

const ITERATIONS: usize = 10_000;

fn entry_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("entry_insert");

    let mut rng = rng();
    const SIZE: u32 = u8::MAX as u32;

    let distr_small = Uniform::new_inclusive(0, u8::MAX as u32).unwrap();
    let distr_large = Uniform::new_inclusive(u8::MAX as u32 + 1, u16::MAX as u32).unwrap();
    let fractions_of_small = [0.5, 0.6, 0.7, 0.8, 0.9, 1.0];

    // NOTE: If throughput is enabled, then the line chart is disabled
    // group.throughput(Throughput::Elements(ITERATIONS as u64));
    group.warm_up_time(Duration::from_millis(1));
    group.measurement_time(Duration::from_millis(500));

    for fraction_of_small in fractions_of_small.iter() {
        let mut keys: Vec<u32> = (0..(ITERATIONS as f64 * fraction_of_small) as usize)
            .map(|_| distr_small.sample(&mut rng))
            .collect();

        keys.extend((keys.len()..ITERATIONS).map(|_| distr_large.sample(&mut rng)));
        keys.shuffle(&mut rng);

        // HashMap
        let mut hash_map: HashMap<u32, usize, fnv_rs::FnvBuildHasher> = Default::default();

        group.bench_with_input(
            BenchmarkId::new("HashMap", fraction_of_small),
            fraction_of_small,
            |b, _fraction_of_small| {
                b.iter(|| {
                    for &key in keys.iter() {
                        hash_map
                            .entry(key as u32)
                            .and_modify(|val| *val += 1)
                            .or_insert(1);
                    }
                });
            },
        );

        // MuleMap bump
        let mut mule_map_bump = MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
        group.bench_with_input(
            BenchmarkId::new("MuleMap::bump", fraction_of_small),
            fraction_of_small,
            |b, _fraction_of_small| {
                b.iter(|| {
                    for &key in keys.iter() {
                        mule_map_bump.bump_int(key);
                    }
                });
            },
        );

        // MuleMap NonZero bump
        let mut mule_nonzero_bump = MuleMap::<u32, NonZero<usize>, fnv_rs::FnvBuildHasher>::new();

        group.bench_with_input(
            BenchmarkId::new("MuleMap NonZero bump", fraction_of_small),
            fraction_of_small,
            |b, _fraction_of_small| {
                b.iter(|| {
                    for &key in keys.iter() {
                        mule_nonzero_bump.bump_non_zero(key);
                    }
                });
            },
        );

        // HandRolled
        let mut hash_map_hand_rolled: HashMap<u32, usize, fnv_rs::FnvBuildHasher> =
            Default::default();
        let mut table_hand_rolled: Vec<usize> = vec![0; u8::MAX as usize + 1];

        group.bench_with_input(
            BenchmarkId::new("HandRolled", fraction_of_small),
            fraction_of_small,
            |b, _fraction_of_small| {
                b.iter(|| {
                    for &key in keys.iter() {
                        if key <= SIZE {
                            table_hand_rolled[key as usize] += 1;
                        } else {
                            hash_map_hand_rolled
                                .entry(key)
                                .and_modify(|counter| *counter += 1)
                                .or_insert(1);
                        }
                    }
                });
            },
        );
    }

    group.finish();
}

criterion_group!(benches, entry_insert);
criterion_main!(benches);
