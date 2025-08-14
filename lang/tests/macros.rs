use core::str::FromStr;

use satellite_lang::arch_program::pubkey::Pubkey;

mod id {
    satellite_lang::declare_id!("da075cb2ff5ec6817613de530b692a8735477769da47430cbd8154335c4a8327");
}

#[test]
fn test_declare_id() {
    let good = Pubkey::from_str("da075cb2ff5ec6817613de530b692a8735477769da47430cbd8154335c4a8327").unwrap();
    let bad = Pubkey::from_str("878286028318ef2d8d21a207310b3e3bc5cf2510ddd832ab9031fece1da42c6d").unwrap();
    assert_eq!(good, id::ID);
    assert_eq!(good, id::id());
    assert!(id::check_id(&good));
    assert!(!id::check_id(&bad));
}

mod pk {
    pub(super) const PUBKEY: satellite_lang::arch_program::pubkey::Pubkey =
        satellite_lang::pubkey!("878286028318ef2d8d21a207310b3e3bc5cf2510ddd832ab9031fece1da42c6d");
}

#[test]
fn test_pubkey() {
    let want = Pubkey::from_str("878286028318ef2d8d21a207310b3e3bc5cf2510ddd832ab9031fece1da42c6d");
    assert_eq!(want.unwrap(), pk::PUBKEY);
}
