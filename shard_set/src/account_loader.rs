use std::cell::{Ref, RefMut};

use arch_program::program_error::ProgramError;

pub trait AccountLoaderLike<'info, T> {
    fn load(&self) -> Result<Ref<T>, ProgramError>;
    fn load_mut(&self) -> Result<RefMut<T>, ProgramError>;
}
