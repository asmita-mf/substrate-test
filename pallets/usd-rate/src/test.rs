use super::*;
use crate::{Error, mock::*};
use frame_support::{assert_ok, assert_noop};

// #[test]
// fn submit_signed_usd_rate_value_works(){
//     _new_test_ext().execute_with(|| {
//         assert_ok!(
//             super::UsdRate::submit_signed_usd_rate_value(1, U256::from(50000000), custom_types::UsdRateTokenType::Eth),
//         );
//     })
// }