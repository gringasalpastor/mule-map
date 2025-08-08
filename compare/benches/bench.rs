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
    const SIZE: u32 = u8::MAX as u32;
    let mut group = c.benchmark_group("Count Frequency");

    let mut rng = rng();

    let distr_small = Uniform::new_inclusive(0, u32::from(u8::MAX)).unwrap();
    let distr_large = Uniform::new_inclusive(u32::from(u8::MAX) + 1, u32::from(u16::MAX)).unwrap();
    let fractions_of_small: [f64; 11] = [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0];

    // NOTE: If throughput is enabled, then the line chart is disabled
    // group.throughput(Throughput::Elements(ITERATIONS as u64));
    group.warm_up_time(Duration::from_millis(1000));
    group.measurement_time(Duration::from_millis(10000));

    for fraction_of_small in &fractions_of_small {
        #[allow(clippy::cast_possible_truncation)]
        #[allow(clippy::cast_sign_loss)]
        let label = format!("{:?}", (fraction_of_small * 100.0).floor() as u32);

        #[allow(clippy::cast_possible_truncation)]
        #[allow(clippy::cast_sign_loss)]
        #[allow(clippy::cast_precision_loss)]
        let mut keys: Vec<u32> = (0..(ITERATIONS as f64 * fraction_of_small) as usize)
            .map(|_| distr_small.sample(&mut rng))
            .collect();

        keys.extend((keys.len()..ITERATIONS).map(|_| distr_large.sample(&mut rng)));
        keys.shuffle(&mut rng);

        // HashMap
        let mut hash_map: HashMap<u32, usize, fnv_rs::FnvBuildHasher> = HashMap::default();

        group.bench_with_input(
            BenchmarkId::new("HashMap", &label),
            fraction_of_small,
            |b, _fraction_of_small| {
                b.iter(|| {
                    for &key in &keys {
                        hash_map.entry(key).and_modify(|val| *val += 1).or_insert(1);
                    }
                });
            },
        );

        // MuleMap bump
        let mut mule_map_bump = MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
        group.bench_with_input(
            BenchmarkId::new("MuleMap", &label),
            fraction_of_small,
            |b, _fraction_of_small| {
                b.iter(|| {
                    for &key in &keys {
                        mule_map_bump.bump_int(key);
                    }
                });
            },
        );

        // MuleMap NonZero bump
        let mut mule_nonzero_bump = MuleMap::<u32, NonZero<usize>, fnv_rs::FnvBuildHasher>::new();

        group.bench_with_input(
            BenchmarkId::new("MuleMap (NonZero)", &label),
            fraction_of_small,
            |b, _fraction_of_small| {
                b.iter(|| {
                    for &key in &keys {
                        mule_nonzero_bump.bump_non_zero(key);
                    }
                });
            },
        );

        // HandRolled
        let mut hash_map_hand_rolled: HashMap<u32, usize, fnv_rs::FnvBuildHasher> =
            HashMap::default();
        let mut table_hand_rolled: Vec<usize> = vec![0; u8::MAX as usize + 1];

        group.bench_with_input(
            BenchmarkId::new("HandRolled", &label),
            fraction_of_small,
            |b, _fraction_of_small| {
                b.iter(|| {
                    for &key in &keys {
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
