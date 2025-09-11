#![cfg(test)]

use std::cell::Ref;

use satellite_bitcoin::generic::fixed_list_unchecked::FixedRefList;

use crate::error::StateShardError;
use crate::select::*;
use crate::StateShard; // bring trait methods like total_btc into scope

use super::common::{create_shard, leak_loaders_from_vec, MockShardZc};

fn build_shards<const N: usize>(balances: &[u64]) -> FixedRefList<Ref<'static, MockShardZc>, N> {
    let shards: Vec<MockShardZc> = balances.iter().copied().map(create_shard).collect();
    let loaders = leak_loaders_from_vec(shards);

    let mut refs: FixedRefList<Ref<'static, MockShardZc>, N> = FixedRefList::new();
    for loader in loaders {
        refs.push(loader.load().expect("zero-copy borrow")).unwrap();
    }
    refs
}

#[test]
fn select_with_happy_path_and_errors() {
    const MAX_TOTAL: usize = 5;
    const MAX_SELECTED: usize = 3;

    let shards = build_shards::<MAX_TOTAL>(&[10, 20, 30, 40, 50]);

    // Happy path: unique indexes in-bounds within selection capacity
    let selected = select_with::<_, _, MAX_TOTAL, MAX_SELECTED>(&shards, [0, 2, 4]).unwrap();
    assert_eq!(selected.as_slice(), &[0, 2, 4]);

    // Error: duplicate index
    let err = select_with::<_, _, MAX_TOTAL, MAX_SELECTED>(&shards, [1, 1]).unwrap_err();
    assert_eq!(err, StateShardError::DuplicateShardSelection);

    // Error: out of bounds
    let err = select_with::<_, _, MAX_TOTAL, MAX_SELECTED>(&shards, [0, 5]).unwrap_err();
    assert_eq!(err, StateShardError::OutOfBounds);

    // Note: `IntoShardIndices` for arrays uses `FixedList::from_slice`, which panics
    // when exceeding capacity rather than returning an error. We avoid asserting
    // on that here to keep this test panic-free.
}

#[test]
fn select_min_by_empty_and_basic() {
    const MAX_TOTAL: usize = 4;

    // Empty list
    let empty: FixedRefList<Ref<'static, MockShardZc>, MAX_TOTAL> = FixedRefList::new();
    let res = select_min_by::<_, _, MAX_TOTAL>(&empty, |s| s.total_btc().to_sat() as u128).unwrap();
    assert_eq!(res, None);

    // Non-empty
    let shards = build_shards::<MAX_TOTAL>(&[50, 10, 20, 10]);
    // With tie on minimum value (10), first index should be chosen (stable by scan order)
    let res =
        select_min_by::<_, _, MAX_TOTAL>(&shards, |s| s.total_btc().to_sat() as u128).unwrap();
    assert_eq!(res, Some(1));
}

#[test]
fn select_max_by_empty_and_basic() {
    const MAX_TOTAL: usize = 4;

    // Empty list
    let empty: FixedRefList<Ref<'static, MockShardZc>, MAX_TOTAL> = FixedRefList::new();
    let res = select_max_by::<_, _, MAX_TOTAL>(&empty, |s| s.total_btc().to_sat()).unwrap();
    assert_eq!(res, None);

    // Non-empty
    let shards = build_shards::<MAX_TOTAL>(&[5, 20, 20, 7]);
    // With tie on maximum value (20), first index should be chosen
    let res = select_max_by::<_, _, MAX_TOTAL>(&shards, |s| s.total_btc().to_sat()).unwrap();
    assert_eq!(res, Some(1));
}

#[test]
fn select_multiple_by_predicate_and_errors() {
    const MAX_TOTAL: usize = 6;
    const MAX_SELECTED_OK: usize = 3;

    let shards = build_shards::<MAX_TOTAL>(&[0, 5, 10, 0, 15, 0]);
    // Should select indices with non-zero BTC, capped by MAX_SELECTED_OK
    let selected = select_multiple_by::<_, _, MAX_TOTAL, MAX_SELECTED_OK>(&shards, |s| {
        s.total_btc().to_sat() > 0
    })
    .unwrap();
    assert_eq!(selected.as_slice(), &[1, 2, 4]);

    // Narrow predicate to ensure fewer matches
    const MAX_SELECTED_SMALL: usize = 2;
    let selected = select_multiple_by::<_, _, MAX_TOTAL, MAX_SELECTED_SMALL>(&shards, |s| {
        s.total_btc().to_sat() >= 10
    })
    .unwrap();
    assert_eq!(selected.as_slice(), &[2, 4]);
}

#[test]
fn select_multiple_sorted_accumulate_until_predicate() {
    const MAX_TOTAL: usize = 5;
    const MAX_SELECTED: usize = 3;
    // Balances: [5, 40, 10, 25, 15]
    // Sorted descending by key: indexes [1 (40), 3 (25), 4 (15), 2 (10), 0 (5)]
    // Accumulate until >= 50 -> [1, 3] should be enough (40 + 25 = 65)
    let shards = build_shards::<MAX_TOTAL>(&[5, 40, 10, 25, 15]);

    let selected = select_multiple_sorted::<_, _, _, MAX_TOTAL, MAX_SELECTED>(
        &shards,
        |s| s.total_btc().to_sat(),
        |sum| sum >= 50,
    )
    .unwrap();

    assert_eq!(selected.as_slice(), &[1, 3]);
}

#[test]
fn select_multiple_sorted_fallback_select_all_when_predicate_never_true() {
    const MAX_TOTAL: usize = 4;
    const MAX_SELECTED: usize = 4;
    let shards = build_shards::<MAX_TOTAL>(&[1, 1, 1, 1]);

    // Predicate impossible: sum > 10; expect all selected in descending order logic path →
    // function returns select_with(shards, indices) where indices is the sorted indices
    let selected = select_multiple_sorted::<_, _, _, MAX_TOTAL, MAX_SELECTED>(
        &shards,
        |s| s.total_btc().to_sat(),
        |sum| sum > 10,
    )
    .unwrap();

    // The implementation sorts descending by key, but then returns `select_with` over that order.
    // For all equal keys, the stable order is by original index due to `sort_by_key` not being stable when using key only.
    // We only assert that all indices are present and length matches.
    let mut v = selected.as_slice().to_vec();
    v.sort_unstable();
    assert_eq!(v, vec![0, 1, 2, 3]);
}
