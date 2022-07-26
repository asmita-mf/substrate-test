
//! Autogenerated weights for `pallet_usd_rate`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-07-21, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: None, DB CACHE: 1024

// Executed Command:
// ./target/release/node-template
// benchmark
// pallet
// --pallet
// pallet_usd_rate
// --extrinsic
// *
// --steps=50
// --repeat=20
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=pallets/usd-rate/src/weights1.rs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::Weight};
use sp_std::marker::PhantomData;

pub trait WeightInfo {
	fn submit_signed_usd_rate_value() -> Weight;
}

/// Weight functions for `pallet_usd_rate`.
pub struct WeightInfoStruct<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for WeightInfoStruct<T> {
	// Storage: UsdRate UsdRate (r:1 w:1)
	fn submit_signed_usd_rate_value() -> Weight {
		(25_043_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
}
