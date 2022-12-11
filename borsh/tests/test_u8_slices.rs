use borsh::{BorshBorrowedDeserialize, BorshSerialize};

macro_rules! test_u8_slice {
    ($v: expr) => {
        let v: &[u8] = $v;
        let buf = v.try_to_vec().unwrap();
        let actual_v: &[u8] =
            BorshBorrowedDeserialize::try_from_slice(&buf).expect("failed to deserialize");
        assert_eq!(actual_v, $v);
    };
}

#[test]
fn test_u8_slices() {
    test_u8_slice!(&[]);
    test_u8_slice!(&[95]);
    test_u8_slice!(&[11; 10]);
    test_u8_slice!(&[145; 100]);
    test_u8_slice!(&[120; 1000]);
    test_u8_slice!(&[0; 10000]);
}
