#[macro_export]
macro_rules! assert_error {
    ( $value:expr, $p:pat ) => {
        let has_error = match $value {
            Err($p) => true,
            _ => false,
        };
        assert!(
            has_error,
            "{} must have an error {}",
            stringify!($value),
            stringify!($p)
        );
    };
}

#[allow(dead_code)]
pub static EPS: f32 = 0.0001;

#[macro_export]
macro_rules! assert_eq_eps {
    ( $expected:expr, $actual:expr) => {
        if let Ok(Value::Float(v)) = $actual {
            assert!(
                (v - $expected).abs() <= $crate::common::EPS,
                "|{} - {}| <= {}",
                v,
                $expected,
                $crate::common::EPS
            );
        } else {
            assert!(false, "{:?} must be a float value", $actual);
        }
    };
}
