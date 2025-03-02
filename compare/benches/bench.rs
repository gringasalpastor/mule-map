use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion /*,Throughput*/};
use mule_map::MuleMap;
use rand::distr::Distribution;
use rand::distr::Uniform;
use rand::rng;
use rand::seq::SliceRandom;
use std::collections::HashMap;
use std::time::Duration;

const ITERATIONS: usize = 10_000;

fn entry_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("entry_insert");

    let mut rng = rng();

    let distr_small = Uniform::new_inclusive(0, u8::MAX as u32).unwrap();
    let distr_large = Uniform::new_inclusive(u8::MAX as u32 + 1, u16::MAX as u32).unwrap();
    // let fractions_of_small = [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0];
    let fractions_of_small = [0.5, 0.6, 0.7, 0.8, 0.9, 1.0];
    // let fractions_of_small = [1.0];

    // group.throughput(Throughput::Elements(ITERATIONS as u64));
    group.warm_up_time(Duration::from_millis(1));
    group.measurement_time(Duration::from_millis(500));

    for fraction_of_small in fractions_of_small.iter() {
        let mut keys: Vec<u32> = (0..(ITERATIONS as f64 * fraction_of_small) as usize)
            .map(|_| distr_small.sample(&mut rng))
            .collect();

        keys.extend((keys.len()..ITERATIONS).map(|_| distr_large.sample(&mut rng)));
        keys.shuffle(&mut rng);
        let mut _mule_map =
            MuleMap::<u32, usize, fnv_rs::FnvBuildHasher, { mule_map::ZERO_SENTINEL }>::new();
        let mut mule_map_bump =
            MuleMap::<u32, usize, fnv_rs::FnvBuildHasher, { mule_map::ZERO_SENTINEL }>::new();

        // group.bench_with_input(
        //     BenchmarkId::new("MuleMap", fraction_of_small),
        //     fraction_of_small,
        //     |b, _fraction_of_small| {
        //         b.iter(|| {
        //             for &key in keys.iter() {
        //                 mule_map.modify_or_insert(key, |val| *val += 1, 1);
        //                 // mule_map.entry(key).and_modify(|val| *val += 1).or_insert(1);
        //             }
        //         });
        //     },
        // );

        group.bench_with_input(
            BenchmarkId::new("MuleMap::bump", fraction_of_small),
            fraction_of_small,
            |b, _fraction_of_small| {
                b.iter(|| {
                    for &key in keys.iter() {
                        mule_map_bump.bump(key);
                    }
                });
            },
        );
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

        // use std::num::NonZero;

        // let mut hash_map_hand_rolled_non_zero: HashMap<u32, usize, fnv_rs::FnvBuildHasher> =
        //     Default::default();
        // let mut table_hand_rolled_non_zero: Vec<Option<NonZero<usize>>> =
        //     vec![None; u8::MAX as usize + 1];

        // const SIZE: u32 = u8::MAX as u32;

        // group.bench_with_input(
        //     BenchmarkId::new("HandRolledNonZero", fraction_of_small),
        //     fraction_of_small,
        //     |b, _fraction_of_small| {
        //         b.iter(|| {
        //             for &key in keys.iter() {
        //                 if key <= SIZE {
        //                     unsafe {
        //                         table_hand_rolled_non_zero[key as usize] =
        //                             Some(NonZero::<usize>::new_unchecked(
        //                                 table_hand_rolled_non_zero[key as usize]
        //                                     .map(|x| x.get())
        //                                     .unwrap_or(0)
        //                                     + 1,
        //                             ));

        //                         // *std::mem::transmute::<&mut Option<NonZero<usize>>, &mut usize>(
        //                         //     &mut table_hand_rolled_non_zero[key as usize],
        //                         // ) += 1;
        //                     }
        //                 } else {
        //                     hash_map_hand_rolled_non_zero
        //                         .entry(key)
        //                         .and_modify(|counter| *counter += 1)
        //                         .or_insert(1);
        //                 }
        //             }
        //         });
        //     },
        // );

        //     let mut hash_map_hand_rolled: HashMap<u32, usize, fnv_rs::FnvBuildHasher> =
        //         Default::default();
        //     let mut table_hand_rolled: Vec<usize> = vec![0; u8::MAX as usize + 1];

        //     group.bench_with_input(
        //         BenchmarkId::new("HandRolled", fraction_of_small),
        //         fraction_of_small,
        //         |b, _fraction_of_small| {
        //             b.iter(|| {
        //                 for &key in keys.iter() {
        //                     if key <= SIZE {
        //                         table_hand_rolled[key as usize] += 1;
        //                     } else {
        //                         hash_map_hand_rolled
        //                             .entry(key)
        //                             .and_modify(|counter| *counter += 1)
        //                             .or_insert(1);
        //                     }
        //                 }
        //             });
        //         },
        //     );
    }

    group.finish();
}

criterion_group!(benches, entry_insert);

criterion_main!(benches);
