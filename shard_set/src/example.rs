use crate::ShardSetBuilder;
use satellite_lang::prelude::{AccountLoader, Owner};
use satellite_lang::ZeroCopy;

/// Example shard type for demonstration
#[derive(Default, Clone, Copy)]
#[repr(C)]
pub struct ExampleShard {
    pub balance: u64,
    pub priority: u8,
    pub user_id: u32,
}

unsafe impl ZeroCopy for ExampleShard {}

impl Owner for ExampleShard {
    const OWNER: satellite_lang::solana_program::pubkey::Pubkey =
        satellite_lang::solana_program::pubkey::Pubkey::new_from_array([0u8; 32]);
}

/// Demonstrates the new clear 4-step workflow:
/// 1. **ShardSetBuilder::from()** - Create initial builder
/// 2. **.load_all()** - Load & inspect ALL shards  
/// 3. **.select_*()** - Choose shards based on actual shard data
/// 4. **.mutate_selected()** - Get mutable access to selected shards only
pub fn example_workflow<'info>(
    loaders: &'info [AccountLoader<'info, ExampleShard>],
) -> Result<(), Box<dyn std::error::Error>> {
    // Step 1: Create builder - only basic operations available
    let builder = ShardSetBuilder::<ExampleShard, 8, 4>::from(loaders);

    println!("Total shards available: {}", builder.len());

    // Step 2: Load and inspect ALL shards - enables selection operations
    let inspector = builder.load_all()?;

    // Now we can inspect all shards to make informed selection decisions
    let total_balance: u64 = inspector.for_each(|shard| shard.balance)
        .iter()
        .filter_map(|opt| opt.as_ref())
        .sum();
    println!("Total balance across all shards: {}", total_balance);

    // Step 3: Select shards based on actual data - various selection strategies available

    // Example 3a: Select the shard with minimum balance
    let selection = inspector.select_min_by(|shard| shard.balance)?;

    // Example 3b: Alternative selection strategies (commented out):
    // let selection = inspector.select_multiple_by(|shard| shard.priority > 5)?;
    // let selection = inspector.select_multiple_sorted(
    //     |shard| shard.balance,
    //     |accumulated| accumulated > 1000
    // )?;

    println!("Selected {} shards", selection.len());

    // Step 4: Get mutable access to ONLY the selected shards
    let mut mutator = selection.mutate_selected()?;

    // Apply mutations to all selected shards
    mutator.for_each_mut(|shard| {
        shard.balance += 100; // Add 100 to each selected shard
        shard.priority = 0; // Reset priority
        shard
    });

    println!("Updated {} shards", mutator.len());

    // The mutator guard automatically commits changes when dropped
    Ok(())
}

/// Example showing different selection strategies with clear naming
pub fn selection_examples<'info>(
    loaders: &'info [AccountLoader<'info, ExampleShard>],
) -> Result<(), Box<dyn std::error::Error>> {
    // Strategy 1: Select by specific indices
    let selection = ShardSetBuilder::<ExampleShard, 8, 4>::from(loaders)
        .load_all()? // Step 2: Load all
        .select_with([0, 2])?; // Step 3: Select indices 0 and 2

    // Strategy 2: Select the richest shard
    let selection = ShardSetBuilder::<ExampleShard, 8, 4>::from(loaders)
        .load_all()? // Step 2: Load all
        .select_max_by(|shard| shard.balance)?; // Step 3: Select max balance

    // Strategy 3: Select all high-priority shards
    let selection = ShardSetBuilder::<ExampleShard, 8, 4>::from(loaders)
        .load_all()? // Step 2: Load all
        .select_multiple_by(|shard| shard.priority >= 8)?; // Step 3: Select by predicate

    // Strategy 4: Select shards until condition is met (greedy)
    let selection = ShardSetBuilder::<ExampleShard, 8, 4>::from(loaders)
        .load_all()? // Step 2: Load all
        .select_multiple_sorted(
            // Step 3: Greedy selection
            |shard| shard.balance, // Sort by balance (descending)
            |total| total >= 5000, // Stop when total >= 5000
        )?;

    // Step 4: Apply mutations
    let mut mutator = selection.mutate_selected()?;

    // Process all selected shards
    mutator.for_each_mut(|shard| {
        // Your mutation logic here
        shard.balance /= 2;
        shard
    });

    Ok(())
}

/// Example showing the type safety - this demonstrates what won't compile
/// and what the correct workflow looks like
pub fn type_safety_example<'info>(loaders: &'info [AccountLoader<'info, ExampleShard>]) {
    // Step 1: Create builder
    let builder = ShardSetBuilder::<ExampleShard, 8, 4>::from(loaders);

    // ❌ This won't compile - select_min_by is not available on Created state
    // let selection = builder.select_min_by(|shard| shard.balance);

    // ✅ Step 2: Load all shards first
    let inspector = builder.load_all().unwrap();

    // ❌ This won't compile - mutate_selected is not available on Inspector
    // let mutator = inspector.mutate_selected();

    // ✅ Step 3: Select shards based on inspection
    let selection = inspector.select_min_by(|shard| shard.balance).unwrap();

    // ✅ Step 4: Now mutation is available
    let mutator = selection.mutate_selected().unwrap();

    println!("Successfully created mutator with {} shards", mutator.len());
}

/// Clear workflow with descriptive variable names
pub fn clear_workflow_example<'info>(
    loaders: &'info [AccountLoader<'info, ExampleShard>],
) -> Result<(), Box<dyn std::error::Error>> {
    // Each step has a clear purpose and descriptive type name
    let builder = ShardSetBuilder::<ExampleShard, 8, 4>::from(loaders);
    let inspector = builder.load_all()?;
    let selection = inspector.select_max_by(|shard| shard.balance)?;
    let mut mutator = selection.mutate_selected()?;

    // Apply business logic
    mutator.for_each_mut(|shard| {
        shard.balance *= 2; // Double the balance
        shard.priority = 10; // Set high priority
        shard
    });

    Ok(())
}
