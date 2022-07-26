#![cfg_attr(not(feature = "std"), no_std)]


#[cfg(test)]
pub mod mock;
#[cfg(test)]
mod test;

use frame_support::traits::Get;
use frame_system::{
	offchain::{
		AppCrypto, CreateSignedTransaction, SendSignedTransaction,
		SignedPayload, Signer, SigningTypes,
	},
};
use sp_runtime::{
	offchain::{
		storage::{MutateStorageError, StorageRetrievalError, StorageValueRef},
	},
};
use primitive_types::U256;
use sp_std::{prelude::*, str, convert::TryInto};
mod custom_types;
use custom_types::UsdRateTokenType;
mod rt_offchain;
pub mod crypto;
// #[path = "../../../global_constants.rs"] mod global_constants;

pub use weights::WeightInfo;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
pub mod weights;
pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	/// This pallet's configuration trait
	#[pallet::config]
	pub trait Config: CreateSignedTransaction<Call<Self>> + frame_system::Config {
		/// The identifier type for an offchain worker.
		type AuthorityId: AppCrypto<Self::Public, Self::Signature>;

		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The overarching dispatch call type.
		type Call: From<Call<Self>>;

		// Configuration parameters

		/// A grace period after we send transaction.
		///
		/// To avoid sending too many transactions, we only attempt to send one
		/// every `GRACE_PERIOD` blocks. We use Local Storage to coordinate
		/// sending between distinct runs of this offchain worker.
		#[pallet::constant]
		type GracePeriod: Get<Self::BlockNumber>;

		type WeightInfo: WeightInfo;
	}

		// Errors inform users that something went wrong.
	#[pallet::error]
	pub enum Error<T> {
		// Error returned when making signed transactions in off-chain worker
		// Error returned when no local accounts available for signing in ocw-storage
		NoLocalAcctForSigning,
		// Error returned when transaction failed due to some reason from offchain worker
		OffchainSignedTxError,
		// Error returned when If data is fetched recently
		InSameGracePeriod,
		// Error returned when fetching info from remote
		HttpFetchingError,
		// Error returned when parsing string data is failed
		StringParsingError,
		// Error returned when bytes to string conversion failed
		ByteToStringConversionError,
		// Error returned when the expected result is not a number
		ResultNotANumberError,
		// Error returned when Offchain worker does not able to acquire lock
		LockAcquiredFailed,
		// Error returned when signer can be only the Ocw key owner
		RequireOcwKeyOwner,
		// Error returned when given token is invalid
		InvalidToken
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		/// Offchain Worker entry point.
		fn offchain_worker(block_number: T::BlockNumber) {
		
			log::info!("Hello from offchain workers of usd-rate pallet!");

			for cryptos in UsdRateTokenType::_iterator() {
				match Self::fetch_and_store_cryptos_usd_rate(block_number, b"eth-usd-rate-last-send", cryptos) {
					Ok(usd_value) => {	
						let _ = Self::submit_cryptos_usd_rate_value(*cryptos ,usd_value);
					}
					Err(err) => {
						log::debug!("Warning: {:?} ", err);
					}
				}
			}
		}
	}

	/// A public part of the pallet.
	#[pallet::call]
	impl<T: Config> Pallet<T> {

		/*************************** Start extrinsic which is signed only by ocw ** ***************************/

		/// Extrinsic signed by Ocw to submit new usd rate for crypto by reading the api data
		// #[pallet::weight(<T as Config>::WeightInfo::submit_signed_usd_rate_value())]
		#[pallet::weight(T::WeightInfo::submit_signed_usd_rate_value())]

		pub fn submit_signed_usd_rate_value(origin: OriginFor<T>, rate: U256, crypto_name: UsdRateTokenType) -> DispatchResult {
			let signer = ensure_signed(origin)?;

			Self::append_usd_rate(rate, &crypto_name);
			let  usd_rate = Self::get_usd_rate();

			Self::deposit_event(Event::InitializedusdRateSuccess(Some(signer), crypto_name, usd_rate));
			Ok(())
		}

		/*************************** End of extrinsic which is signed only by ocw ** ***************************/
	}

	/// Events for the pallet.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Event generated when new rate request is accepted.
		InitializedusdRateSuccess(Option<T::AccountId>, UsdRateTokenType, custom_types::UsdRate),
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	/// Store of EthUsdRate when new rate request is accepted.
	#[pallet::storage]
	#[pallet::getter(fn get_usd_rate)]
	pub type UsdRate<T> = StorageValue<_, custom_types::UsdRate, ValueQuery>; //usd rate of eth, eos, btc

	#[pallet::storage]
	#[pallet::getter( fn get_circulation_value)]
	pub(super) type Circulation<T> = StorageMap<_, Blake2_128Concat, UsdRateTokenType, U256, ValueQuery>;

}

impl<T: SigningTypes> SignedPayload<T> for custom_types::PricePayload<T::Public, T::BlockNumber> {
	fn public(&self) -> T::Public {
		self.public.clone()
	}
}

impl<T: Config> Pallet<T> {

	/// fn append_usd_rate(rate: U256, crypto_name: &UsdRateTokenType)
	/// This function take 2 argument.
	/// based on match condition it mutate the UsdRate runtime storage 
	/// and update the usd-rate of the matched crypto
	fn append_usd_rate(rate: U256, crypto_name: &UsdRateTokenType) {
		match crypto_name {
			UsdRateTokenType::Eth => {
				UsdRate::<T>::mutate(|get_usd_rate| {
					get_usd_rate.eth = rate;
				});
			},
			UsdRateTokenType::Eos=> {
				UsdRate::<T>::mutate(|get_usd_rate| {
					get_usd_rate.eos = rate;
				});
			},
			UsdRateTokenType::Btc => {
				UsdRate::<T>::mutate(|get_usd_rate| {
					get_usd_rate.btc = rate; 
				});
			},
			_ => {log::debug!("none type");}
		}
	}

	/// fetch_and_store_cryptos_usd_rate(block_number: T::BlockNumber, 
	///	ocw_storage_key: &[u8], 
	///	crypto_type: &UsdRateTokenType) ->  Result<U256, Error<T>> 
	/// This function take 3 arguments.
	/// Check the data in local storage, if data is recently stored than it should return, 
	/// else it fetch the crypto price via making http call and store the fetched price in storage.
	fn fetch_and_store_cryptos_usd_rate(block_number: T::BlockNumber, 
		ocw_storage_key: &[u8], 
		crypto_type: &UsdRateTokenType) ->  Result<U256, Error<T>> 
	{
		/// A friendlier name for the error that is going to be returned in case we are in the grace
		/// period.
		const RECENTLY_SENT: () = ();

		let val = StorageValueRef::persistent(ocw_storage_key);

		let res = val.mutate(|last_send: Result<Option<T::BlockNumber>, StorageRetrievalError>| {
			match last_send {
				// If we already have a value in storage and the block number is recent enough
				// we avoid sending another transaction at this time.
				Ok(Some(block)) if block_number < block + T::GracePeriod::get() =>
					Err(RECENTLY_SENT),
				// In every other case we attempt to acquire the lock and send a transaction.
				_ => Ok(block_number),
			}
		});

		match res {
			// The value has been set correctly, which means we can safely send a transaction now.
			Ok(_block_number) => {
				Self::parse_crypto_price(crypto_type)
			},
			// We are in the grace period, we should not send a transaction this time.
			Err(MutateStorageError::ValueFunctionFailed(RECENTLY_SENT)) => Err(<Error<T>>::InSameGracePeriod),
			Err(MutateStorageError::ConcurrentModification(_)) => Err(<Error<T>>::LockAcquiredFailed),
		}
	}

	/// fn parse_crypto_price(crypto_type: &UsdRateTokenType) ->  Result<U256, Error<T>>
	/// This function take one argument.
	/// Based on matched crypto it fetch, parse & return the cryoto_price
	/// 
	/// [Note: If new cryptos will be introduced in the system than to fetch and add the price,
	/// needed to include the matched condition for the new cryptos. ]
	fn parse_crypto_price(crypto_type: &UsdRateTokenType) ->  Result<U256, Error<T>> {
		match crypto_type {
			UsdRateTokenType::Eth => {
				match Self::fetch_average_eth_price() {
					Some(price) => {
						if price > U256::from(0_u64) {
							Ok(price)
						}
						else {
							Err(<Error<T>>::ResultNotANumberError)
						}
					},
					None => {
						log::warn!("Unable to extract price from the response:");
						Err(<Error<T>>::ResultNotANumberError)
					},
				}
				// match Self::parse_eth_price(global_constants::_ETH_USD_RATE_API_ENDPOINT) {
				// 	Some(price) => {
				// 		if price > U256::from(0_u64) {
				// 			Ok(price)
				// 		}
				// 		else {
				// 			Err(<Error<T>>::ResultNotANumberError)
				// 		}
				// 	},
				// 	None => {
				// 		log::warn!("Unable to extract price from the response:");
				// 		Err(<Error<T>>::ResultNotANumberError)
				// 	},
				// }
			},
			UsdRateTokenType::Eos=> {
				match Self::parse_eos_price("http://freecurrencyrates.com/api/action.php?do=cvals&iso=USD&f=EOS&v=1&s=cbr") {
					Some(price) => {
						if price > U256::from(0_u64) {
							Ok(price)
						}
						else {
							Err(<Error<T>>::ResultNotANumberError)
						}
					},
					None => {
						log::warn!("Unable to extract price from the response:");
						Err(<Error<T>>::ResultNotANumberError)
					},
				}
			},
			_ => {
				Err(<Error<T>>::InvalidToken)
			}
		}
	}

	/// fn submit_cryptos_usd_rate_value(crypto_type: UsdRateTokenType, crypto_usd_rate: U256) -> Result<(), Error<T>>
	/// This function takes 2 argument
	/// It fetch the signer key from offchain storage, sign&send transaction to the runtime to submit new usd price of the cryptos.
	fn submit_cryptos_usd_rate_value(crypto_type: UsdRateTokenType, crypto_usd_rate: U256) -> Result<(), Error<T>> {
		log::info!(" Given crypto: {:?}, rate : {:?}", &crypto_type, &crypto_usd_rate);

		let signer = Signer::<T, <T as pallet::Config>::AuthorityId>::any_account();

		let result = signer.send_signed_transaction(|_acct|
			// This is the on-chain function
			Call::submit_signed_usd_rate_value { rate: crypto_usd_rate, crypto_name: crypto_type });
		// Display error if the signed tx fails.
		if let Some((acc, res)) = result {
			if res.is_err() {
				log::info!("failure: offchain_signed_tx: tx sent: {:?}", acc.id);
				return Err(<Error<T>>::OffchainSignedTxError);
			}
			log::info!("Sent success: {:?}", res);
			// Transaction is sent successfully
			return Ok(());
		}
		log::info!("No local account available");
		Err(<Error<T>>::NoLocalAcctForSigning)
	}
}
