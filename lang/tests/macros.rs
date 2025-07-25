use core::str::FromStr;

use satellite_lang::arch_program::pubkey::Pubkey;

mod id {
    satellite_lang::declare_id!("Fg6PaFpoGXkYsidMpWTK6W2BeZ7FEfcYkg476zPFsLnS");
}

#[test]
fn test_declare_id() {
    let good = Pubkey::from_str("Fg6PaFpoGXkYsidMpWTK6W2BeZ7FEfcYkg476zPFsLnS").unwrap();
    let bad = Pubkey::from_str("A7yUYJNEVYRLE4QWsnc9rE9JRsm7DfqEmLscQVwkffAk").unwrap();
    assert_eq!(good, id::ID);
    assert_eq!(good, id::id());
    assert!(id::check_id(&good));
    assert!(!id::check_id(&bad));
}

mod pk {
    pub(super) const PUBKEY: satellite_lang::arch_program::pubkey::Pubkey =
        satellite_lang::pubkey!("A7yUYJNEVYRLE4QWsnc9rE9JRsm7DfqEmLscQVwkffAk");
}

#[test]
fn test_pubkey() {
    let want = Pubkey::from_str("A7yUYJNEVYRLE4QWsnc9rE9JRsm7DfqEmLscQVwkffAk");
    assert_eq!(want.unwrap(), pk::PUBKEY);
}
