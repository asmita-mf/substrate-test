
use super::*;

use frame_system::RawOrigin;

use frame_benchmarking::{benchmarks, whitelisted_caller};

fn assert_event<T: Config>(generic_event: <T as Config>::Event) {
	frame_system::Pallet::<T>::assert_has_event(generic_event.into());
}

benchmarks! {
    submit_signed_usd_rate_value {
        let caller: T::AccountId = whitelisted_caller();
        log::info!("default {:?}", U256::default());
    // }:_(RawOrigin::Signed(caller.clone()), U256::from(5000000000000000000_i128), custom_types::UsdRateTokenType::Eth)
    }:_(RawOrigin::Signed(caller.clone()), U256::default(), custom_types::UsdRateTokenType::Eth)

    verify {
       let usd_rate =  custom_types::UsdRate {
            eth: U256::default(),
            eos: U256::from(0_u8),
            vtbc_current_price: U256::from(0_u8),
            vtbc_start_price: U256::from(0_u8),
            vtbc_last_apr_rate: U256::from(0_u8),
        };
        assert_event::<T>(Event::InitializedusdRateSuccess (Some(caller),custom_types::UsdRateTokenType::Eth, usd_rate ).into());
	}
}

// Compile cli code: cargo build --release --features runtime-benchmarks
//   ./target/release/vtb-node benchmark pallet --pallet pallet_usd_rate --extrinsic "*" --steps=50 --repeat=20 --execution=wasm --wasm-execution=compiled --heap-pages=4096 --output=pallets/usd-rate/src/weights1.rs 

// 


