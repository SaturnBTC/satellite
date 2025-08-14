//! Only tests whether `satellite-apl` builds with `metadata` feature enabled.

use satellite_lang::prelude::*;

declare_id!("054a752fa3ef8be54b17ca4e6a0ca5595bf8a64d43b5df4cee58af7800000000");

#[program]
pub mod metadata {}
