use borsh::{BorshDeserialize, BorshSerialize};

use crate::{instruction::Instruction, pubkey::Pubkey};

pub const COMPUTE_BUDGET_PROGRAM_ID: Pubkey = Pubkey(*b"ComputeBudget1111111111111111111");

pub fn check_id(id: &Pubkey) -> bool {
    id == &COMPUTE_BUDGET_PROGRAM_ID
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize, BorshSerialize, BorshDeserialize)]
pub enum ComputeBudgetInstruction {
    /// Request a specific transaction-wide program heap region size in bytes.
    /// The value requested must be a multiple of 1024. This new heap region
    /// size applies to each program executed in the transaction, including all
    /// calls to CPIs.
    RequestHeapFrame(u32),
    /// Set a specific compute unit limit that the transaction is allowed to consume.
    SetComputeUnitLimit(u32),
}

impl ComputeBudgetInstruction {
    /// Create a `ComputeBudgetInstruction::RequestHeapFrame` `Instruction`
    pub fn request_heap_frame(bytes: u32) -> Instruction {
        Instruction::new_with_bincode(
            COMPUTE_BUDGET_PROGRAM_ID,
            Self::RequestHeapFrame(bytes),
            vec![],
        )
    }

    /// Create a `ComputeBudgetInstruction::SetComputeUnitLimit` `Instruction`
    pub fn set_compute_unit_limit(units: u32) -> Instruction {
        Instruction::new_with_bincode(
            COMPUTE_BUDGET_PROGRAM_ID,
            Self::SetComputeUnitLimit(units),
            vec![],
        )
    }
}
