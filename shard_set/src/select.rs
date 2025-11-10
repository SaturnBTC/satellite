//! # Shard Selection Functions
//!
//! This module provides standalone functions for selecting shards from a `ShardList`
//! based on various criteria. These functions are designed to work with pre-loaded
//! shard references and return either single indices or lists of indices.
//!
//! ## Usage Example
//!
//! ```rust,ignore
//! # use satellite_lang::prelude::*;
//! # use satellite_lang::ZeroCopy;
//! # use crate::load::load_shards;
//! # use crate::select::*;
//! #
//! # #[derive(Clone, Copy)]
//! # struct MyShard { balance: u64 }
//! # unsafe impl ZeroCopy for MyShard {}
//! # impl Owner for MyShard {
//! #     const OWNER: satellite_lang::solana_program::pubkey::Pubkey =
//! #         satellite_lang::solana_program::pubkey::Pubkey::new_from_array([0u8; 32]);
//! # }
//! # let loaders: &[AccountLoader<MyShard>] = &[];
//!
//! // Load shards into a ShardList
//! let shards = load_shards::<MyShard, 10>(loaders)?;
//!
//! // Select single shard with minimum balance
//! let min_shard: Option<usize> = select_min_by(&shards, |shard| shard.balance)?;
//!
//! // Select single shard with maximum balance  
//! let max_shard: Option<usize> = select_max_by(&shards, |shard| shard.balance)?;
//!
//! // Select multiple shards by predicate
//! let high_balance_shards: FixedList<usize, 5> = select_multiple_by(
//!     &shards,
//!     |shard| shard.balance > 1000
//! )?;
//!
//! // Select specific shards by index
//! let selected_shards: FixedList<usize, 3> = select_with(&shards, [0, 2, 4])?;
//!
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

use core::cell::Ref;
use core::cmp::Reverse;
use satellite_bitcoin::generic::fixed_list::FixedList;
use satellite_bitcoin::generic::fixed_list_unchecked::FixedRefList;
use satellite_lang::prelude::Owner;
use satellite_lang::ZeroCopy;

use super::error::StateShardError;
use super::shard_indices::IntoShardIndices;

/// Select shards by index from a ShardList of shard references.
///
/// # Errors
/// * [`StateShardError::TooManyShardsSelected`]
///   if the number of indices in `spec` exceeds `MAX_SELECTED_SHARDS`.
/// * [`StateShardError::DuplicateShardSelection`]
///   if `spec` contains the same index more than once.
/// * [`StateShardError::OutOfBounds`]
///   if any index is >= the number of shards.
pub fn select_with<T, S, const MAX_TOTAL_SHARDS: usize, const MAX_SELECTED_SHARDS: usize>(
    shards: &FixedRefList<Ref<S>, MAX_TOTAL_SHARDS>,
    spec: T,
) -> super::error::Result<FixedList<usize, MAX_SELECTED_SHARDS>>
where
    T: IntoShardIndices<MAX_SELECTED_SHARDS>,
    S: ZeroCopy + Owner,
{
    let indexes = spec
        .into_indices()
        .map_err(|_| StateShardError::TooManyShardsSelected)?;

    let mut selected = FixedList::new();

    for &idx in indexes.as_slice() {
        if idx >= shards.len() {
            return Err(StateShardError::OutOfBounds.into());
        }

        // Avoid selecting the same shard more than once
        if selected.iter().any(|&existing| existing == idx) {
            return Err(StateShardError::DuplicateShardSelection.into());
        }

        selected
            .push(idx)
            .map_err(|_| StateShardError::TooManyShardsSelected)?;
    }

    Ok(selected)
}

/// Select the shard that minimises the value returned by `key_fn`.
/// Returns the index of the selected shard, or None if no shards are available.
///
/// # Errors
/// Returns an error if no shards are available to select from.
pub fn select_min_by<F, S, const MAX_TOTAL_SHARDS: usize>(
    shards: &FixedRefList<Ref<S>, MAX_TOTAL_SHARDS>,
    key_fn: F,
) -> super::error::Result<Option<usize>>
where
    F: Fn(&S) -> u128,
    S: ZeroCopy + Owner,
{
    if shards.is_empty() {
        return Ok(None);
    }

    let mut best_idx: Option<usize> = None;
    let mut best_key: u128 = u128::MAX;

    for (idx, shard_ref) in shards.iter().enumerate() {
        let key = key_fn(&*shard_ref);
        if key < best_key {
            best_key = key;
            best_idx = Some(idx);
        }
    }

    Ok(best_idx)
}

/// Select the shard that maximises the value returned by `key_fn`.
/// Returns the index of the selected shard, or None if no shards are available.
///
/// # Errors
/// Returns an error if no shards are available to select from.
pub fn select_max_by<F, S, const MAX_TOTAL_SHARDS: usize>(
    shards: &FixedRefList<Ref<S>, MAX_TOTAL_SHARDS>,
    key_fn: F,
) -> super::error::Result<Option<usize>>
where
    F: Fn(&S) -> u64,
    S: ZeroCopy + Owner,
{
    if shards.is_empty() {
        return Ok(None);
    }

    let mut best_idx: Option<usize> = None;
    let mut best_key: u64 = 0;

    for (idx, shard_ref) in shards.iter().enumerate() {
        let key = key_fn(&*shard_ref);
        if key > best_key {
            best_key = key;
            best_idx = Some(idx);
        }
    }

    Ok(best_idx)
}

/// Select all shards that satisfy the provided `predicate`.
///
/// # Errors
/// Propagates the same conditions as [`select_with`].
pub fn select_multiple_by<P, S, const MAX_TOTAL_SHARDS: usize, const MAX_SELECTED_SHARDS: usize>(
    shards: &FixedRefList<Ref<S>, MAX_TOTAL_SHARDS>,
    predicate: P,
) -> super::error::Result<FixedList<usize, MAX_SELECTED_SHARDS>>
where
    P: Fn(&S) -> bool,
    S: ZeroCopy + Owner,
{
    let mut indices = Vec::new();
    for (idx, shard_ref) in shards.iter().enumerate() {
        if predicate(&*shard_ref) {
            indices.push(idx);
        }
    }
    select_with(shards, indices)
}

/// Select a minimal set of shards – ordered by `key_fn` (descending) –
/// such that the accumulated `predicate` evaluates to `true`.
///
/// # Errors
/// Propagates the same conditions as [`select_with`].
pub fn select_multiple_sorted<
    K,
    P,
    S,
    const MAX_TOTAL_SHARDS: usize,
    const MAX_SELECTED_SHARDS: usize,
>(
    shards: &FixedRefList<Ref<S>, MAX_TOTAL_SHARDS>,
    key_fn: K,
    predicate: P,
) -> super::error::Result<FixedList<usize, MAX_SELECTED_SHARDS>>
where
    K: Fn(&S) -> u64,
    P: Fn(u64) -> bool,
    S: ZeroCopy + Owner,
{
    // 1. Gather all shard indices and sort them **descending** by `key_fn`.
    let mut indices: Vec<usize> = (0..shards.len()).collect();
    indices.sort_by_key(|&i| {
        let key = key_fn(&*shards.get(i).unwrap());
        // Reverse to get descending order.
        Reverse(key)
    });

    // 2. Incrementally add shards until the predicate is satisfied.
    let mut selected = Vec::new();
    let mut accumulated: u64 = 0;
    for &idx in &indices {
        accumulated += key_fn(&*shards.get(idx).unwrap());
        selected.push(idx);
        if predicate(accumulated) {
            return select_with(shards, selected);
        }
    }

    // Fallback – select everything (may still error if `MAX_SELECTED_SHARDS` exceeded).
    select_with(shards, indices)
}
