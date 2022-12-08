use borsh::BorshDeserialize;

macro_rules! test_str {
    ($test_name: ident, $str: expr) => {
        #[test]
        fn $test_name() {
            let s = $str;
            let buf = s.as_bytes();
            let actual_s = <&str>::try_from_slice(&buf).expect("failed to deserialize a str slice");
            assert_eq!(actual_s, $str);
        }
    };
}

test_str!(test_empty_string, "");
test_str!(test_a, "a");
test_str!(test_hello_world, "hello world");
test_str!(test_x_1024, &("x".repeat(1024)));
test_str!(test_x_4096, &("x".repeat(4096)));
test_str!(test_x_65535, &("x".repeat(65535)));
test_str!(test_hello_1000, &("hello world!".repeat(1000)));
test_str!(test_non_ascii, "💩");
