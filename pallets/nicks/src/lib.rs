// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Nicks Pallet
//!
//! - [`Config`]
//! - [`Call`]
//!
//! ## Overview
//!
//! Nicks is an example pallet for keeping track of account names on-chain. It makes no effort to
//! create a name hierarchy, be a DNS replacement or provide reverse lookups. Furthermore, the
//! weights attached to this pallet's dispatchable functions are for demonstration purposes only and
//! have not been designed to be economically secure. Do not use this pallet as-is in production.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! * `set_name` - Set the associated name of an account; a small deposit is reserved if not already
//!   taken.
//! * `clear_name` - Remove an account's associated name; the deposit is returned.
//! * `kill_name` - Forcibly remove the associated name; the deposit is lost.

#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::traits::{Currency, OnUnbalanced, ReservableCurrency};
pub use pallet::*;
use scale_info::TypeInfo;
use sp_runtime::traits::{StaticLookup, Zero};
use sp_std::prelude::*;
use frame_support::StorageHasher;
use rustc_hex::ToHex;
use scale_info::prelude::string::String;

type AccountIdOf<T> = <T as frame_system::Config>::AccountId;
type BalanceOf<T> = <<T as Config>::Currency as Currency<AccountIdOf<T>>>::Balance;
type NegativeImbalanceOf<T> =
	<<T as Config>::Currency as Currency<AccountIdOf<T>>>::NegativeImbalance;

/// A nickname with a first and last part.
#[derive(codec::Encode, codec::Decode, Default, frame_support::RuntimeDebug, PartialEq, TypeInfo)]
pub struct Nickname {
	first: Vec<u8>,
	last: Option<Vec<u8>>,
}

/// Utility type for managing upgrades/migrations.
#[derive(codec::Encode, codec::Decode, Clone, frame_support::RuntimeDebug, PartialEq, TypeInfo)]
pub enum StorageVersionEnum {
	V1Bytes,
	V2Struct,
}

#[derive( codec::Encode, codec::Decode, Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd, scale_info::TypeInfo)]
pub enum TokenType {
	EOS,
	ETH,
	VTBC,
	VTBT
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The currency trait.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// Reservation fee.
		#[pallet::constant]
		type ReservationFee: Get<BalanceOf<Self>>;

		/// What to do with slashed funds.
		type Slashed: OnUnbalanced<NegativeImbalanceOf<Self>>;

		/// The origin which may forcibly set or remove a name. Root can always do this.
		type ForceOrigin: EnsureOrigin<Self::Origin>;

		/// The minimum length a name may be.
		#[pallet::constant]
		type MinLength: Get<u32>;

		/// The maximum length a name may be.
		#[pallet::constant]
		type MaxLength: Get<u32>;
	}

    #[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {

		// This part is for testing and debugging for the manish decoding requirement.
		fn on_initialize(n: T::BlockNumber) -> Weight {
			// Anything that needs to be done at the start of the block.
			if n == 1u32.into() {
			
                let order_id = b"0x73684b299820ea55281f4657354840d23436d7da3c7f61ab82db31f37137d8b6";
                let r = Blake2_128Concat::hash(order_id);
				frame_support::log::info!("orderid: {:?}", r.to_hex::<String>());
			}
			0
		}

		fn on_runtime_upgrade() -> frame_support::weights::Weight {
			//migration::migrate_to_v2::<T>()
			migration::migrate_to_v2_user::<T>()
		}
    }

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A name was set.
		NameSet { who: T::AccountId },
		/// A name was forcibly set.
		NameForced { target: T::AccountId },
		/// A name was changed.
		NameChanged { who: T::AccountId },
		/// A name was cleared, and the given balance returned.
		NameCleared { who: T::AccountId, deposit: BalanceOf<T> },
		/// A name was removed and the given balance slashed.
		NameKilled { target: T::AccountId, deposit: BalanceOf<T> },
	}

	/// Error for the nicks pallet.
	#[pallet::error]
	pub enum Error<T> {
		/// A name is too short.
		TooShort,
		/// A name is too long.
		TooLong,
		/// An account isn't named.
		Unnamed,
	}

	// The lookup table for names.
	//v1
	// #[pallet::storage]
	// pub(super) type NameOf<T: Config> =
	// 	StorageMap<_, Twox64Concat, T::AccountId, (BoundedVec<u8, T::MaxLength>, BalanceOf<T>)>;

	//v2
    #[pallet::storage]
	pub(super) type NameOf<T: Config> =
		StorageMap<_, Twox64Concat, T::AccountId, (Nickname, BalanceOf<T>)>;

    	#[pallet::type_value]
	pub fn StorageVersionValue<T: Config>() -> StorageVersionEnum { StorageVersionEnum::V1Bytes } //40_0000_0000_0000_0000_0000_0000_i128

	//v1
	// #[pallet::storage]
	// #[pallet::getter( fn user_assets)]
	// pub type User<T> = StorageDoubleMap<_, Blake2_128Concat, TokenType, Blake2_128Concat, <T as frame_system::Config>::AccountId, u128, ValueQuery>;

	//v2
	#[pallet::storage]
	#[pallet::getter( fn user_assets)]
	pub type User<T: Config> = StorageDoubleMap<_, Blake2_128Concat, T::AccountId, 
	Blake2_128Concat, TokenType, 
	u128, ValueQuery>;

    /// The current version of the pallet.
    #[pallet::storage]
	pub type PalletVersion<T: Config> = StorageValue<_, StorageVersionEnum, ValueQuery, StorageVersionValue<T>>;  //StorageVersionEnum { StorageVersionEnum::V1Bytes } 
	
	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
    #[pallet::without_storage_info]
	pub struct Pallet<T>(_);

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Set an account's name. The name should be a UTF-8-encoded string by convention, though
		/// we don't check it.
		///
		/// The name may not be more than `T::MaxLength` bytes, nor less than `T::MinLength` bytes.
		///
		/// If the account doesn't already have a name, then a fee of `ReservationFee` is reserved
		/// in the account.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// # <weight>
		/// - O(1).
		/// - At most one balance operation.
		/// - One storage read/write.
		/// - One event.
		/// # </weight>
		#[pallet::weight(50_000_000)]
		pub fn set_name(origin: OriginFor<T>, name: Vec<u8>, last: Option<Vec<u8>>) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			//v1
			// let bounded_name: BoundedVec<_, _> =
			// 	name.try_into().map_err(|()| Error::<T>::TooLong)?;
			// ensure!(bounded_name.len() >= T::MinLength::get() as usize, Error::<T>::TooShort);
            //v2
            let len = match last {
				None => name.len(),
				Some(ref last_name) => name.len() + last_name.len(),
			};

			ensure!(len >= T::MinLength::get() as usize, Error::<T>::TooShort);

			let deposit = if let Some((_, deposit)) = <NameOf<T>>::get(&sender) {
				Self::deposit_event(Event::<T>::NameChanged { who: sender.clone() });
				deposit
			} else {
				let deposit = T::ReservationFee::get();
				T::Currency::reserve(&sender, deposit)?;
				Self::deposit_event(Event::<T>::NameSet { who: sender.clone() });
				deposit
			};
			//v1
			// <NameOf<T>>::insert(&sender, (bounded_name, deposit));
            //v2
             <NameOf<T>>::insert(&sender, (Nickname { first: name, last }, deposit));
			Ok(())
		}

		/// Clear an account's name and return the deposit. Fails if the account was not named.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// # <weight>
		/// - O(1).
		/// - One balance operation.
		/// - One storage read/write.
		/// - One event.
		/// # </weight>
		#[pallet::weight(70_000_000)]
		pub fn clear_name(origin: OriginFor<T>) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			let deposit = <NameOf<T>>::take(&sender).ok_or(Error::<T>::Unnamed)?.1;

			let err_amount = T::Currency::unreserve(&sender, deposit);
			debug_assert!(err_amount.is_zero());

			Self::deposit_event(Event::<T>::NameCleared { who: sender, deposit });
			Ok(())
		}

		/// Remove an account's name and take charge of the deposit.
		///
		/// Fails if `target` has not been named. The deposit is dealt with through `T::Slashed`
		/// imbalance handler.
		///
		/// The dispatch origin for this call must match `T::ForceOrigin`.
		///
		/// # <weight>
		/// - O(1).
		/// - One unbalanced handler (probably a balance transfer)
		/// - One storage read/write.
		/// - One event.
		/// # </weight>
		#[pallet::weight(70_000_000)]
		pub fn kill_name(
			origin: OriginFor<T>,
			target: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;

			// Figure out who we're meant to be clearing.
			let target = T::Lookup::lookup(target)?;
			// Grab their deposit (and check that they have one).
			let deposit = <NameOf<T>>::take(&target).ok_or(Error::<T>::Unnamed)?.1;
			// Slash their deposit from them.
			T::Slashed::on_unbalanced(T::Currency::slash_reserved(&target, deposit).0);

			Self::deposit_event(Event::<T>::NameKilled { target, deposit });
			Ok(())
		}

		/// Set a third-party account's name with no deposit.
		///
		/// No length checking is done on the name.
		///
		/// The dispatch origin for this call must match `T::ForceOrigin`.
		///
		/// # <weight>
		/// - O(1).
		/// - At most one balance operation.
		/// - One storage read/write.
		/// - One event.
		/// # </weight>
		#[pallet::weight(70_000_000)]
		pub fn force_name(
			origin: OriginFor<T>,
			target: <T::Lookup as StaticLookup>::Source,
			name: Vec<u8>,
            last: Option<Vec<u8>>
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;

			// let bounded_name: BoundedVec<_, _> =
			// 	name.try_into().map_err(|()| Error::<T>::TooLong)?;
			let target = T::Lookup::lookup(target)?;
			let deposit = <NameOf<T>>::get(&target).map(|x| x.1).unwrap_or_else(Zero::zero);
			//v1
			// <NameOf<T>>::insert(&target, (bounded_name, deposit));
			//v2
            <NameOf<T>>::insert(&target, (Nickname { first: name, last }, deposit));

			Self::deposit_event(Event::<T>::NameForced { target });
			Ok(())
		}

		#[pallet::weight(70_000_000)]
		pub fn set_user(origin: OriginFor<T>, user: T::AccountId, token: TokenType, balance: u128) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			//v1
			//User::<T>::insert(token, &user, balance);
			//v2
			User::<T>::insert( &user, token, balance);

			Self::deposit_event(Event::<T>::NameForced { target: user });
			Ok(())
		}
	}
}

//v2
pub mod migration {
	use super::*;
    use frame_support::pallet_prelude::Weight;
    use frame_support::traits::Get;
	pub mod deprecated {
		use crate::*;
		use frame_support::{pallet, decl_module, decl_storage, traits::Currency};
        use super::*;
        use frame_support::storage_alias;
        use frame_support::pallet_prelude::*;

		type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

        #[storage_alias]
	    pub type NameOf<T: Config> = StorageMap<Pallet<T>, Twox64Concat, <T as frame_system::Config>::AccountId, (BoundedVec<u8, <T as pallet::Config>::MaxLength>, BalanceOf<T>)>;

		#[storage_alias]
		pub type User<T> = StorageDoubleMap<_, Blake2_128Concat, TokenType, 
		Blake2_128Concat, <T as frame_system::Config>::AccountId,
		u128, ValueQuery>;

		// decl_storage! {
		// 	trait Store for Module<T: Trait> as MyNicks {
		// 		pub NameOf: map hasher(twox_64_concat) T::AccountId => Option<(Vec<u8>, BalanceOf<T>)>;
		// 	}
		// }
		// decl_module! {
		// 	pub struct Module<T: Config> for enum Call where origin: T::Origin { }
		// }
	}

	pub fn migrate_to_v2_user<T: Config>() -> frame_support::weights::Weight {
		sp_runtime::runtime_logger::RuntimeLogger::init();

		// Storage migrations should use storage versions for safety.
		if <PalletVersion<T>>::get() == StorageVersionEnum::V1Bytes {
			// Very inefficient, mostly here for illustration purposes.
			let count = deprecated::User::<T>::iter().count();
			frame_support::log::info!(" >>> Updating MyNicks storage. Migrating {} nicknames...", count);

			// We transform the storage values from the old into the new format.
			deprecated::User::<T>::translate::<u128, _>(
				| k2: TokenType, k1: T::AccountId, user_data: u128| {
					frame_support::log::info!("     Migrated nickname for {:?}...{:?}", k1, k2);

					User::<T>::insert(k1, k2, user_data);
					frame_support::log::info!(" >>> Updating MyNicks storage. Migrating {:?} nicknames...", user_data);
					Some(user_data)
				}
			);

			// Update storage version.
			<PalletVersion<T>>::put(StorageVersionEnum::V2Struct);
			// Very inefficient, mostly here for illustration purposes.
			let count = User::<T>::iter().count();
			frame_support::log::info!(" <<< MyNicks storage updated! Migrated {} nicknames ✅", count);

			// Return the weight consumed by the migration.
			T::DbWeight::get().reads_writes(count as Weight + 1, count as Weight + 1)
		} else {
			frame_support::log::info!(" >>> Unused migration!");
			0
		}
	}

	pub fn migrate_to_v2<T: Config>() -> frame_support::weights::Weight {
		frame_support::log::info!("fn migrate_to_v2");
		sp_runtime::runtime_logger::RuntimeLogger::init();

		// Storage migrations should use storage versions for safety.
		if <PalletVersion<T>>::get() == StorageVersionEnum::V1Bytes {
			// Very inefficient, mostly here for illustration purposes.
			let count = deprecated::NameOf::<T>::iter().count();
			frame_support::log::info!(" >>> Updating MyNicks storage. Migrating {} nicknames...", count);

			// We transform the storage values from the old into the new format.
			NameOf::<T>::translate::<(Vec<u8>, BalanceOf<T>), _>(
				|k: T::AccountId, (nick, deposit): (Vec<u8>, BalanceOf<T>)| {
					frame_support::log::info!("     Migrated nickname for {:?}...", k);

					// We split the nick at ' ' (<space>).
					match nick.iter().rposition(|&x| x == b" "[0]) {
						Some(ndx) => Some((Nickname {
							first: nick[0..ndx].to_vec(),
							last: Some(nick[ndx + 1..].to_vec())
						}, deposit)),
						None => Some((Nickname { first: nick, last: None }, deposit))
					}
				}
			);

			// Update storage version.
			<PalletVersion<T>>::put(StorageVersionEnum::V2Struct);
			// Very inefficient, mostly here for illustration purposes.
			let count = NameOf::<T>::iter().count();
			frame_support::log::info!(" <<< MyNicks storage updated! Migrated {} nicknames ✅", count);

			// Return the weight consumed by the migration.
			T::DbWeight::get().reads_writes(count as Weight + 1, count as Weight + 1)
		} else {
			frame_support::log::info!(" >>> Unused migration!");
			0
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate as pallet_nicks;

	use frame_support::{
		assert_noop, assert_ok, ord_parameter_types, parameter_types,
		traits::{ConstU32, ConstU64},
	};
	use frame_system::EnsureSignedBy;
	use sp_core::H256;
	use sp_runtime::{
		testing::Header,
		traits::{BadOrigin, BlakeTwo256, IdentityLookup},
	};

	type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
	type Block = frame_system::mocking::MockBlock<Test>;

	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system,
			Balances: pallet_balances,
			Nicks: pallet_nicks,
		}
	);

	parameter_types! {
		pub BlockWeights: frame_system::limits::BlockWeights =
			frame_system::limits::BlockWeights::simple_max(1024);
	}
	impl frame_system::Config for Test {
		type BaseCallFilter = frame_support::traits::Everything;
		type BlockWeights = ();
		type BlockLength = ();
		type DbWeight = ();
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = Call;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = Event;
		type BlockHashCount = ConstU64<250>;
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
		type OnSetCode = ();
		type MaxConsumers = ConstU32<16>;
	}

	impl pallet_balances::Config for Test {
		type MaxLocks = ();
		type MaxReserves = ();
		type ReserveIdentifier = [u8; 8];
		type Balance = u64;
		type Event = Event;
		type DustRemoval = ();
		type ExistentialDeposit = ConstU64<1>;
		type AccountStore = System;
		type WeightInfo = ();
	}

	ord_parameter_types! {
		pub const One: u64 = 1;
	}
	impl Config for Test {
		type Event = Event;
		type Currency = Balances;
		type ReservationFee = ConstU64<2>;
		type Slashed = ();
		type ForceOrigin = EnsureSignedBy<One, u64>;
		type MinLength = ConstU32<3>;
		type MaxLength = ConstU32<16>;
	}

	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test> { balances: vec![(1, 10), (2, 10)] }
			.assimilate_storage(&mut t)
			.unwrap();
		t.into()
	}

	#[test]
	fn kill_name_should_work() {
		new_test_ext().execute_with(|| {
			// assert_ok!(Nicks::set_name(Origin::signed(2), b"Dave".to_vec()));
			assert_ok!(Nicks::set_name(Origin::signed(2), b"Dave".to_vec(), Some(b"Kante".to_vec())));

			assert_eq!(Balances::total_balance(&2), 10);
			assert_ok!(Nicks::kill_name(Origin::signed(1), 2));
			assert_eq!(Balances::total_balance(&2), 8);
			assert_eq!(<NameOf<Test>>::get(2), None);
		});
	}

	#[test]
	fn force_name_should_work() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				// Nicks::set_name(Origin::signed(2), b"Dr. David Brubeck, III".to_vec()),
                Nicks::set_name(Origin::signed(2), b"Dr. David Brubeck, III".to_vec(), Some(b"patle singh".to_vec())),
				Error::<Test>::TooLong,
			);

			assert_ok!(Nicks::set_name(Origin::signed(2), b"Dave".to_vec()));
			assert_eq!(Balances::reserved_balance(2), 2);
			assert_noop!(
				Nicks::force_name(Origin::signed(1), 2, b"Dr. David Brubeck, III".to_vec()),
				Error::<Test>::TooLong,
			);
			assert_ok!(Nicks::force_name(Origin::signed(1), 2, b"Dr. Brubeck, III".to_vec()));
			assert_eq!(Balances::reserved_balance(2), 2);
			let (name, amount) = <NameOf<Test>>::get(2).unwrap();
			assert_eq!(name, b"Dr. Brubeck, III".to_vec());
			assert_eq!(amount, 2);
		});
	}

	#[test]
	fn normal_operation_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Nicks::set_name(Origin::signed(1), b"Gav".to_vec()));
			assert_eq!(Balances::reserved_balance(1), 2);
			assert_eq!(Balances::free_balance(1), 8);
			assert_eq!(<NameOf<Test>>::get(1).unwrap().0, b"Gav".to_vec());

			assert_ok!(Nicks::set_name(Origin::signed(1), b"Gavin".to_vec()));
			assert_eq!(Balances::reserved_balance(1), 2);
			assert_eq!(Balances::free_balance(1), 8);
			assert_eq!(<NameOf<Test>>::get(1).unwrap().0, b"Gavin".to_vec());

			assert_ok!(Nicks::clear_name(Origin::signed(1)));
			assert_eq!(Balances::reserved_balance(1), 0);
			assert_eq!(Balances::free_balance(1), 10);
		});
	}

	#[test]
	fn error_catching_should_work() {
		new_test_ext().execute_with(|| {
			assert_noop!(Nicks::clear_name(Origin::signed(1)), Error::<Test>::Unnamed);

			assert_noop!(
				Nicks::set_name(Origin::signed(3), b"Dave".to_vec()),
				pallet_balances::Error::<Test, _>::InsufficientBalance
			);

			assert_noop!(
				Nicks::set_name(Origin::signed(1), b"Ga".to_vec()),
				Error::<Test>::TooShort
			);
			assert_noop!(
				Nicks::set_name(Origin::signed(1), b"Gavin James Wood, Esquire".to_vec()),
				Error::<Test>::TooLong
			);
			assert_ok!(Nicks::set_name(Origin::signed(1), b"Dave".to_vec()));
			assert_noop!(Nicks::kill_name(Origin::signed(2), 1), BadOrigin);
			assert_noop!(Nicks::force_name(Origin::signed(2), 1, b"Whatever".to_vec()), BadOrigin);
		});
	}
}