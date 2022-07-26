
use codec::{Decode, Encode};
use sp_std::{ prelude::*, str, slice::Iter, fmt};
use sp_runtime::{
	RuntimeDebug,
};
use primitive_types::U256;
use serde::{Deserialize, Serialize};
use frame_support::pallet_prelude::MaxEncodedLen;

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, scale_info::TypeInfo)]
pub struct PricePayload<Public, BlockNumber> {
	pub block_number: BlockNumber,
	pub price: u32,
	pub public: Public,
}

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, scale_info::TypeInfo)]
pub struct Payload<Public> {
	pub number: u64,
	pub public: Public,
}

#[derive( Encode, Decode, Clone, RuntimeDebug, PartialEq, Eq, Deserialize, Serialize, Default, scale_info::TypeInfo, MaxEncodedLen)]
pub struct UsdRate {
	pub eth: U256,
	pub eos: U256,
	pub vtbc_current_price: U256,
	pub vtbc_start_price: U256,
	pub vtbc_last_apr_rate: U256,
}

#[derive( Encode, Decode, Clone, Copy, PartialEq, Eq, RuntimeDebug, scale_info::TypeInfo, MaxEncodedLen)]
pub enum UsdRateTokenType {
	Eos,
	Eth,
	Vtbc,
	None
}

impl UsdRateTokenType {
    pub fn _iterator() -> Iter<'static, UsdRateTokenType> {
        static _TOKENTYPES: [UsdRateTokenType; 3] = [UsdRateTokenType::Eos, UsdRateTokenType::Eth, UsdRateTokenType::Vtbc];
        _TOKENTYPES.iter()
    }
}

impl fmt::Display for UsdRateTokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Default for UsdRateTokenType {
    fn default() -> Self { UsdRateTokenType::None }
}