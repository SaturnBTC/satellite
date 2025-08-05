use core::marker::PhantomData;
use core::mem::MaybeUninit;

use satellite_bitcoin::generic::fixed_list::FixedList;
use satellite_lang::prelude::AccountLoader;
use satellite_lang::prelude::Owner;
use satellite_lang::ZeroCopy;

use super::error::StateShardError;
use super::shard_handle::ShardHandle;
use super::shard_indices::IntoShardIndices;
use arch_program::program_error::ProgramError;
use core::cell::{Ref, RefMut};
use core::cmp::Reverse;

/// Marker type representing the **initial** state where shards are loaded but not yet accessible.
pub struct Created;

/// Marker type representing the **inspection** state with immutable access to all shards.
pub struct Loaded;

/// Marker type representing the **selection** state with a chosen subset of shards.
pub struct Selected;

/// A type-safe wrapper around a slice of [`AccountLoader`]s representing the
/// shards that belong to the currently executing instruction.
///
/// # Workflow States
///
/// This follows a clear 4-step workflow enforced by the type system:
///
/// * [`Created`] – Initial state after `from()`, only allows `load_all()`
/// * [`Loaded`] – After `load_all()`, provides immutable access to ALL shards
///   and exposes selection methods (`select_with`, `select_min_by`, etc.)
/// * [`Selected`] – After selection, allows `mutate_selected()` for
///   mutable access to chosen shards only
///
/// The required workflow is:
/// ```ignore
/// ShardSet::from(loaders)               // Step 1: Create
///     .load_all()?                      // Step 2: Load & inspect all shards  
///     .select_min_by(|s| s.balance)?    // Step 3: Select based on shard data
///     .mutate_selected()?               // Step 4: Get mutable access to selected
/// ```
///
/// # Generic Parameters
///
/// * `'info` – lifetime that ties each `AccountLoader` to the surrounding context.
/// * `S` – zero-copy shard type that must implement [`ZeroCopy`] + [`Owner`].
/// * `MAX_TOTAL_SHARDS` – upper bound enforced at **compile time** on the total
///   number of shards that can be loaded.
/// * `MAX_SELECTED_SHARDS` – upper bound enforced at **compile time** on how
///   many shards can participate in a single operation.
/// * `State` – either [`Created`], [`Loaded`], or [`Selected`].
pub struct ShardSet<
    'info,
    S,
    const MAX_TOTAL_SHARDS: usize,
    const MAX_SELECTED_SHARDS: usize,
    State = Created,
> where
    S: ZeroCopy + Owner,
{
    /// All shard loaders supplied by the caller.
    loaders: &'info [AccountLoader<'info, S>],

    /// Immutable references to all shards (only valid in Loaded and Selected states).
    shard_refs: [MaybeUninit<Ref<'info, S>>; MAX_TOTAL_SHARDS],

    /// Number of loaded shard refs (for tracking how many are actually loaded).
    loaded_count: usize,

    /// Indexes of selected shards (only valid in Selected state).
    selected: FixedList<usize, MAX_SELECTED_SHARDS>,

    /// Typestate marker.
    _state: PhantomData<State>,
}

impl<'info, S, const MAX_TOTAL_SHARDS: usize, const MAX_SELECTED_SHARDS: usize, State> Drop
    for ShardSet<'info, S, MAX_TOTAL_SHARDS, MAX_SELECTED_SHARDS, State>
where
    S: ZeroCopy + Owner,
{
    fn drop(&mut self) {
        // Drop the initialized Ref objects
        for i in 0..self.loaded_count {
            unsafe {
                self.shard_refs[i].assume_init_drop();
            }
        }
    }
}

// -------------------------------- Created State --------------------------------
impl<'info, S, const MAX_TOTAL_SHARDS: usize, const MAX_SELECTED_SHARDS: usize>
    ShardSet<'info, S, MAX_TOTAL_SHARDS, MAX_SELECTED_SHARDS, Created>
where
    S: ZeroCopy + Owner,
{
    /// Creates a new `ShardSet` wrapping the provided loaders.
    ///
    /// **Next step**: Call `.load_all()` to inspect all shards.
    #[inline]
    pub fn from(loaders: &'info [AccountLoader<'info, S>]) -> Self {
        Self {
            loaders,
            shard_refs: core::array::from_fn(|_| MaybeUninit::uninit()),
            loaded_count: 0,
            selected: FixedList::new(),
            _state: PhantomData,
        }
    }

    /// Number of shards (loaders) available.
    #[inline]
    pub fn len(&self) -> usize {
        self.loaders.len()
    }

    /// `true` if no shards are present.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.loaders.is_empty()
    }

    /// Load and provide immutable access to ALL shards for inspection.
    /// This enables selection operations based on actual shard data.
    ///
    /// **Next step**: Call a `select_*()` method to choose specific shards.
    pub fn load_all(
        mut self,
    ) -> Result<ShardSet<'info, S, MAX_TOTAL_SHARDS, MAX_SELECTED_SHARDS, Loaded>, ProgramError>
    {
        if self.loaders.len() > MAX_TOTAL_SHARDS {
            return Err(ProgramError::InvalidArgument);
        }

        // Try to borrow all shards immutably
        for (i, loader) in self.loaders.iter().enumerate() {
            self.shard_refs[i].write(loader.load()?);
        }
        self.loaded_count = self.loaders.len();

        // Move fields out of self before forgetting it to prevent double-drop
        let loaders = self.loaders;
        let shard_refs = unsafe { core::ptr::read(&self.shard_refs) };
        let loaded_count = self.loaded_count;
        let selected = unsafe { core::ptr::read(&self.selected) };
        
        // Prevent destructor from running on self since we moved the fields
        core::mem::forget(self);

        Ok(ShardSet {
            loaders,
            shard_refs,
            loaded_count,
            selected,
            _state: PhantomData,
        })
    }
}

// -------------------------------- Loaded State --------------------------------
impl<'info, S, const MAX_TOTAL_SHARDS: usize, const MAX_SELECTED_SHARDS: usize>
    ShardSet<'info, S, MAX_TOTAL_SHARDS, MAX_SELECTED_SHARDS, Loaded>
where
    S: ZeroCopy + Owner,
{
    /// Access the immutable references to all shards for inspection.
    #[inline]
    pub fn shards(&self) -> impl Iterator<Item = &Ref<'info, S>> {
        self.shard_refs
            .iter()
            .take(self.loaded_count)
            .map(|maybe_uninit| unsafe { maybe_uninit.assume_init_ref() })
    }

    /// Get a slice of all loaded shard references.
    #[inline]
    pub fn shards_slice(&self) -> &[Ref<'info, S>] {
        unsafe {
            std::slice::from_raw_parts(
                self.shard_refs.as_ptr() as *const Ref<'info, S>,
                self.loaded_count,
            )
        }
    }

    /// Number of shards available.
    #[inline]
    pub fn len(&self) -> usize {
        self.loaded_count
    }

    /// `true` if no shards are present.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.loaded_count == 0
    }

    /// Apply a function to each shard and collect results.
    pub fn for_each<R>(&self, mut f: impl FnMut(&S) -> R) -> Vec<R> {
        self.shards().map(|shard_ref| f(&**shard_ref)).collect()
    }

    /// Select shards by index and transition to the selection state.
    ///
    /// **Next step**: Call `.mutate_selected()` to get mutable access.
    ///
    /// # Errors
    /// * [`StateShardError::TooManyShardsSelected`]
    ///   if the number of indices in `spec` exceeds `MAX_SELECTED_SHARDS`.
    /// * [`StateShardError::DuplicateShardSelection`]
    ///   if `spec` contains the same index more than once.
    /// * [`StateShardError::OutOfBounds`]
    ///   if any index is >= the number of shards.
    pub fn select_with<T>(
        mut self,
        spec: T,
    ) -> super::error::Result<ShardSet<'info, S, MAX_TOTAL_SHARDS, MAX_SELECTED_SHARDS, Selected>>
    where
        T: IntoShardIndices<MAX_SELECTED_SHARDS>,
    {
        let indexes = spec
            .into_indices()
            .map_err(|_| StateShardError::TooManyShardsSelected)?;

        for &idx in indexes.as_slice() {
            if idx >= self.loaders.len() {
                return Err(StateShardError::OutOfBounds.into());
            }

            // Avoid selecting the same shard more than once
            if self.selected.iter().any(|&existing| existing == idx) {
                return Err(StateShardError::DuplicateShardSelection.into());
            }

            self.selected
                .push(idx)
                .map_err(|_| StateShardError::TooManyShardsSelected)?;
        }

        // Move fields out of self before forgetting it to prevent double-drop
        let loaders = self.loaders;
        let shard_refs = unsafe { core::ptr::read(&self.shard_refs) };
        let loaded_count = self.loaded_count;
        let selected = unsafe { core::ptr::read(&self.selected) };
        
        // Prevent destructor from running on self since we moved the fields
        core::mem::forget(self);

        Ok(ShardSet {
            loaders,
            shard_refs,
            loaded_count,
            selected,
            _state: PhantomData,
        })
    }

    /// Select the shard that minimises the value returned by `key_fn`.
    ///
    /// **Next step**: Call `.mutate_selected()` to get mutable access.
    ///
    /// # Errors
    /// Propagates the same conditions as [`Self::select_with`].
    pub fn select_min_by<F>(
        self,
        key_fn: F,
    ) -> super::error::Result<ShardSet<'info, S, MAX_TOTAL_SHARDS, MAX_SELECTED_SHARDS, Selected>>
    where
        F: Fn(&S) -> u64,
    {
        let mut best_idx: Option<usize> = None;
        let mut best_key: u64 = u64::MAX;

        for (idx, shard_ref) in self.shard_refs.iter().enumerate().take(self.loaded_count) {
            let key = key_fn(unsafe { shard_ref.assume_init_ref() });
            if key < best_key {
                best_key = key;
                best_idx = Some(idx);
            }
        }

        match best_idx {
            Some(i) => self.select_with([i]),
            None => self.select_with([]),
        }
    }

    /// Select the shard that maximises the value returned by `key_fn`.
    ///
    /// **Next step**: Call `.mutate_selected()` to get mutable access.
    ///
    /// # Errors
    /// Propagates the same conditions as [`Self::select_with`].
    pub fn select_max_by<F>(
        self,
        key_fn: F,
    ) -> super::error::Result<ShardSet<'info, S, MAX_TOTAL_SHARDS, MAX_SELECTED_SHARDS, Selected>>
    where
        F: Fn(&S) -> u64,
    {
        let mut best_idx: Option<usize> = None;
        let mut best_key: u64 = 0;

        for (idx, shard_ref) in self.shard_refs.iter().enumerate().take(self.loaded_count) {
            let key = key_fn(unsafe { shard_ref.assume_init_ref() });
            if key > best_key {
                best_key = key;
                best_idx = Some(idx);
            }
        }

        match best_idx {
            Some(i) => self.select_with([i]),
            None => self.select_with([]),
        }
    }

    /// Select all shards that satisfy the provided `predicate`.
    ///
    /// **Next step**: Call `.mutate_selected()` to get mutable access.
    ///
    /// # Errors
    /// Propagates the same conditions as [`Self::select_with`].
    pub fn select_multiple_by<P>(
        self,
        predicate: P,
    ) -> super::error::Result<ShardSet<'info, S, MAX_TOTAL_SHARDS, MAX_SELECTED_SHARDS, Selected>>
    where
        P: Fn(&S) -> bool,
    {
        let mut indices = Vec::new();
        for (idx, shard_ref) in self.shard_refs.iter().enumerate().take(self.loaded_count) {
            if predicate(unsafe { shard_ref.assume_init_ref() }) {
                indices.push(idx);
            }
        }
        self.select_with(indices)
    }

    /// Select a minimal set of shards – ordered by `key_fn` (descending) –
    /// such that the accumulated `predicate` evaluates to `true`.
    ///
    /// **Next step**: Call `.mutate_selected()` to get mutable access.
    ///
    /// # Errors
    /// Propagates the same conditions as [`Self::select_with`].
    pub fn select_multiple_sorted<K, P>(
        self,
        key_fn: K,
        predicate: P,
    ) -> super::error::Result<ShardSet<'info, S, MAX_TOTAL_SHARDS, MAX_SELECTED_SHARDS, Selected>>
    where
        K: Fn(&S) -> u64,
        P: Fn(u64) -> bool,
    {
        // 1. Gather all shard indices and sort them **descending** by `key_fn`.
        let mut indices: Vec<usize> = (0..self.len()).collect();
        indices.sort_by_key(|&i| {
            let key = key_fn(unsafe { self.shard_refs[i].assume_init_ref() });
            // Reverse to get descending order.
            Reverse(key)
        });

        // 2. Incrementally add shards until the predicate is satisfied.
        let mut selected = Vec::new();
        let mut accumulated: u64 = 0;
        for &idx in &indices {
            accumulated += key_fn(unsafe { self.shard_refs[idx].assume_init_ref() });
            selected.push(idx);
            if predicate(accumulated) {
                return self.select_with(selected);
            }
        }

        // Fallback – select everything (may still error if `MAX_SELECTED_SHARDS` exceeded).
        self.select_with(indices)
    }
}

// -------------------------------- Selected State --------------------------------
impl<'info, S, const MAX_TOTAL_SHARDS: usize, const MAX_SELECTED_SHARDS: usize>
    ShardSet<'info, S, MAX_TOTAL_SHARDS, MAX_SELECTED_SHARDS, Selected>
where
    S: ZeroCopy + Owner,
{
    /// Returns the indexes that were selected.
    #[inline]
    pub fn selected_indices(&self) -> &[usize] {
        self.selected.as_slice()
    }

    /// Number of selected shards.
    #[inline]
    pub fn len(&self) -> usize {
        self.selected.len()
    }

    /// `true` if no shards are selected.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.selected.is_empty()
    }

    /// Returns a [`ShardHandle`] for the shard at **global** `idx`.
    #[inline]
    pub fn handle_by_index(&self, idx: usize) -> ShardHandle<'info, S> {
        debug_assert!(idx < self.loaders.len());
        ShardHandle::new(&self.loaders[idx])
    }

    /// Get mutable access to ALL selected shards in a single call.
    ///
    /// **Final step**: Apply mutations to the selected shards.
    pub fn mutate_selected(
        self,
    ) -> Result<ShardSetMutator<'info, S, MAX_SELECTED_SHARDS>, ProgramError> {
        // 1. Prepare empty array of `Option<RefMut>`.
        let mut arr: [Option<RefMut<'info, S>>; MAX_SELECTED_SHARDS] =
            core::array::from_fn(|_| None);

        // 2. Fill in the first `len` slots with RefMut handles.
        for (slot, &idx) in self.selected_indices().iter().enumerate() {
            arr[slot] = Some(self.loaders[idx].load_mut()?);
        }

        Ok(ShardSetMutator {
            shards: arr.map(|opt| opt.unwrap()),
        })
    }

    /// Executes `f` for every **selected** shard, borrowing each one exactly
    /// for the duration of the closure call.
    pub fn for_each<R>(&self, mut f: impl FnMut(&S) -> R) -> Result<Vec<R>, ProgramError> {
        let mut results = Vec::with_capacity(self.selected.len());
        for &idx in self.selected.iter() {
            let handle = ShardHandle::new(&self.loaders[idx]);
            let out = handle.with_ref(|shard| f(shard))?;
            results.push(out);
        }
        Ok(results)
    }

    /// Executes `f` for every **selected** shard mutably.
    pub fn for_each_mut<R>(&self, mut f: impl FnMut(&mut S) -> R) -> Result<Vec<R>, ProgramError> {
        let mut results = Vec::with_capacity(self.selected.len());
        for &idx in self.selected.iter() {
            let handle = ShardHandle::new(&self.loaders[idx]);
            let out = handle.with_mut(|shard| f(shard))?;
            results.push(out);
        }
        Ok(results)
    }
}

/// Mutator that holds mutable references to selected shards.
///
/// **Final step**: Apply mutations to the selected shards
pub struct ShardSetMutator<'info, S, const N: usize>
where
    S: ZeroCopy + Owner,
{
    shards: [RefMut<'info, S>; N],
}

impl<'info, S, const N: usize> ShardSetMutator<'info, S, N>
where
    S: ZeroCopy + Owner,
{
    /// Apply `f` mutably to every shard and collect the results.
    #[inline]
    pub fn for_each_mut<R>(&mut self, mut f: impl FnMut(&mut S) -> R) -> [Option<R>; N] {
        let mut out: [Option<R>; N] = core::array::from_fn(|_| None);
        for i in 0..self.shards.len() {
            let shard = &mut self.shards[i];
            out[i] = Some(f(shard));
        }
        out
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.shards.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.shards.len() == 0
    }

    /// Access the underlying shard references for testing purposes.
    #[inline]
    pub fn shards(&self) -> &[RefMut<'info, S>] {
        &self.shards
    }

    /// Access the underlying mutable shard references for functions that need mutable access.
    #[inline]
    pub fn shards_mut(&mut self) -> &mut [RefMut<'info, S>] {
        &mut self.shards
    }

    /// Redistribute the remaining satoshi value that belongs to the selected shards
    /// back into new outputs, updating the provided `TransactionBuilder` in the
    /// process.
    ///
    /// This is a thin wrapper around
    /// `crate::split::redistribute_remaining_btc_to_shards`. See that function
    /// for detailed documentation of the parameters and error semantics.
    pub fn redistribute_remaining_btc_to_shards<
        const MAX_USER_UTXOS: usize,
        const MAX_SHARDS_PER_PROGRAM: usize,
        RS,
        U,
    >(
        &mut self,
        tx_builder: &mut satellite_bitcoin::TransactionBuilder<
            MAX_USER_UTXOS,
            MAX_SHARDS_PER_PROGRAM,
            RS,
        >,
        removed_from_shards: u64,
        program_script_pubkey: bitcoin::ScriptBuf,
        fee_rate: &satellite_bitcoin::fee_rate::FeeRate,
    ) -> Result<Vec<u128>, satellite_bitcoin::MathError>
    where
        RS: satellite_bitcoin::generic::fixed_set::FixedCapacitySet<
                Item = arch_program::rune::RuneAmount,
            > + Default,
        U: satellite_bitcoin::utxo_info::UtxoInfoTrait<RS>,
        S: super::StateShard<U, RS> + ZeroCopy + Owner,
    {
        super::split::redistribute_remaining_btc_to_shards(
            tx_builder,
            &self.shards,
            removed_from_shards,
            program_script_pubkey,
            fee_rate,
        )
    }

    /// Compute the number of satoshis that are still unsettled in the selected
    /// shards, i.e. need to be returned after accounting for fees and any
    /// amounts that were already removed by the caller.
    pub fn compute_unsettled_btc_in_shards<
        const MAX_USER_UTXOS: usize,
        const MAX_SHARDS_PER_PROGRAM: usize,
        RS,
        U,
    >(
        &self,
        tx_builder: &satellite_bitcoin::TransactionBuilder<
            MAX_USER_UTXOS,
            MAX_SHARDS_PER_PROGRAM,
            RS,
        >,
        removed_from_shards: u64,
        fee_rate: &satellite_bitcoin::fee_rate::FeeRate,
    ) -> Result<u64, satellite_bitcoin::MathError>
    where
        RS: satellite_bitcoin::generic::fixed_set::FixedCapacitySet<
                Item = arch_program::rune::RuneAmount,
            > + Default,
        U: satellite_bitcoin::utxo_info::UtxoInfoTrait<RS>,
        S: super::StateShard<U, RS> + ZeroCopy + Owner,
    {
        super::split::compute_unsettled_btc_in_shards(
            tx_builder,
            &self.shards,
            removed_from_shards,
            fee_rate,
        )
    }

    /// Update all shards after a transaction has been constructed, signed and
    /// broadcast. Internally forwards to
    /// `crate::update::update_shards_after_transaction`.
    pub fn update_shards_after_transaction<
        const MAX_USER_UTXOS: usize,
        const MAX_SHARDS_PER_PROGRAM: usize,
        RS,
        U,
    >(
        &mut self,
        tx_builder: &mut satellite_bitcoin::TransactionBuilder<
            MAX_USER_UTXOS,
            MAX_SHARDS_PER_PROGRAM,
            RS,
        >,
        program_script_pubkey: &bitcoin::ScriptBuf,
        fee_rate: &satellite_bitcoin::fee_rate::FeeRate,
    ) -> super::error::Result<()>
    where
        RS: satellite_bitcoin::generic::fixed_set::FixedCapacitySet<
                Item = arch_program::rune::RuneAmount,
            > + Default,
        U: satellite_bitcoin::utxo_info::UtxoInfoTrait<RS>,
        S: super::StateShard<U, RS> + ZeroCopy + Owner,
    {
        super::update::update_shards_after_transaction(
            tx_builder,
            &mut self.shards,
            program_script_pubkey,
            fee_rate,
        )
    }

    // === Rune-specific helpers (compiled only with `runes` feature) =============
    #[cfg_attr(docsrs, doc(cfg(feature = "runes")))]
    #[cfg(feature = "runes")]
    /// Compute the yet-to-be-settled Rune amounts held by the selected shards.
    pub fn compute_unsettled_rune_in_shards<RS, U>(
        &self,
        removed_from_shards: RS,
    ) -> Result<RS, super::error::StateShardError>
    where
        RS: satellite_bitcoin::generic::fixed_set::FixedCapacitySet<
                Item = arch_program::rune::RuneAmount,
            > + Default,
        U: satellite_bitcoin::utxo_info::UtxoInfoTrait<RS>,
        S: super::StateShard<U, RS> + ZeroCopy + Owner,
    {
        super::split::compute_unsettled_rune_in_shards(&self.shards, removed_from_shards)
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "runes")))]
    #[cfg(feature = "runes")]
    /// Redistribute the remaining Rune amounts back to the shards, generating
    /// the appropriate runestone edicts in the provided `TransactionBuilder`.
    pub fn redistribute_remaining_rune_to_shards<
        const MAX_USER_UTXOS: usize,
        const MAX_SHARDS_PER_PROGRAM: usize,
        RS,
        U,
    >(
        &mut self,
        tx_builder: &mut satellite_bitcoin::TransactionBuilder<
            MAX_USER_UTXOS,
            MAX_SHARDS_PER_PROGRAM,
            RS,
        >,
        removed_from_shards: RS,
        program_script_pubkey: bitcoin::ScriptBuf,
    ) -> Result<Vec<RS>, super::error::StateShardError>
    where
        RS: satellite_bitcoin::generic::fixed_set::FixedCapacitySet<
                Item = arch_program::rune::RuneAmount,
            > + Default,
        U: satellite_bitcoin::utxo_info::UtxoInfoTrait<RS>,
        S: super::StateShard<U, RS> + ZeroCopy + Owner,
    {
        super::split::redistribute_remaining_rune_to_shards(
            tx_builder,
            &self.shards,
            removed_from_shards,
            program_script_pubkey,
        )
    }
}

// -------------------------------- Legacy Aliases --------------------------------
// For backward compatibility during transition

/// Legacy alias for [`ShardSet`].
#[deprecated(since = "0.2.0", note = "Use `ShardSet` instead")]
pub type ShardSetBuilder<'info, S, const MAX_SELECTED_SHARDS: usize, State = Created> =
    ShardSet<'info, S, MAX_SELECTED_SHARDS, MAX_SELECTED_SHARDS, State>;

/// Legacy alias for [`Created`].
#[deprecated(since = "0.2.0", note = "Use `Created` instead")]
pub type Unselected = Created;

/// Legacy alias for [`ShardSetMutator`].
#[deprecated(since = "0.2.0", note = "Use `ShardSetMutator` instead")]
pub type ShardBatchMut<'info, S, const N: usize> = ShardSetMutator<'info, S, N>;

// Forward compatibility - maintain the old ShardSetInspector and ShardSetSelection names as type aliases
/// Type alias for the loaded state of [`ShardSet`].
pub type ShardSetInspector<'info, S, const MAX_SELECTED_SHARDS: usize> =
    ShardSet<'info, S, MAX_SELECTED_SHARDS, MAX_SELECTED_SHARDS, Loaded>;

/// Type alias for the selected state of [`ShardSet`].
pub type ShardSetSelection<'info, S, const MAX_SELECTED_SHARDS: usize> =
    ShardSet<'info, S, MAX_SELECTED_SHARDS, MAX_SELECTED_SHARDS, Selected>;
