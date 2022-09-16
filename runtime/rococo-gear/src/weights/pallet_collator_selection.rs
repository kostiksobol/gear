// This file is part of Gear.

// Copyright (C) 2022 Gear Technologies Inc.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Autogenerated weights for pallet_collator_selection
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-09-23, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("rococo_gear-local"), DB CACHE: 1024

// Executed Command:
// ./target/release/gear-collator benchmark pallet --chain=rococo_gear-local --steps=50 --repeat=20 --pallet=pallet_collator_selection --extrinsic=* --execution=wasm --wasm-execution=compiled --heap-pages=4096 --output=./scripts/benchmarking/weights-output/pallet_collator_selection.rs --template=.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(clippy::unnecessary_cast)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_collator_selection.
pub trait WeightInfo {
    fn set_invulnerables(b: u32, ) -> Weight;
    fn set_desired_candidates() -> Weight;
    fn set_candidacy_bond() -> Weight;
    fn register_as_candidate(c: u32, ) -> Weight;
    fn leave_intent(c: u32, ) -> Weight;
    fn note_author() -> Weight;
    fn new_session(r: u32, c: u32, ) -> Weight;
}

/// Weights for pallet_collator_selection using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_collator_selection::WeightInfo for SubstrateWeight<T> {
    /// The range of component `b` is `[1, 100]`.
    fn set_invulnerables(b: u32, ) -> Weight {
        Weight::from_ref_time(15_508_000 as u64)
            // Standard Error: 3_000
            .saturating_add(Weight::from_ref_time(2_552_000 as u64).saturating_mul(b as u64))
            .saturating_add(T::DbWeight::get().reads((1 as u64).saturating_mul(b as u64)))
            .saturating_add(T::DbWeight::get().writes(1 as u64))
    }
    fn set_desired_candidates() -> Weight {
        Weight::from_ref_time(11_000_000 as u64)
            .saturating_add(T::DbWeight::get().writes(1 as u64))
    }
    fn set_candidacy_bond() -> Weight {
        Weight::from_ref_time(11_000_000 as u64)
            .saturating_add(T::DbWeight::get().writes(1 as u64))
    }
    /// The range of component `c` is `[1, 1000]`.
    fn register_as_candidate(c: u32, ) -> Weight {
        Weight::from_ref_time(32_462_000 as u64)
            // Standard Error: 0
            .saturating_add(Weight::from_ref_time(96_000 as u64).saturating_mul(c as u64))
            .saturating_add(T::DbWeight::get().reads(5 as u64))
            .saturating_add(T::DbWeight::get().writes(2 as u64))
    }
    /// The range of component `c` is `[6, 1000]`.
    fn leave_intent(c: u32, ) -> Weight {
        Weight::from_ref_time(18_851_000 as u64)
            // Standard Error: 1_000
            .saturating_add(Weight::from_ref_time(99_000 as u64).saturating_mul(c as u64))
            .saturating_add(T::DbWeight::get().reads(1 as u64))
            .saturating_add(T::DbWeight::get().writes(2 as u64))
    }
    fn note_author() -> Weight {
        Weight::from_ref_time(30_000_000 as u64)
            .saturating_add(T::DbWeight::get().reads(3 as u64))
            .saturating_add(T::DbWeight::get().writes(4 as u64))
    }
    /// The range of component `r` is `[1, 1000]`.
    /// The range of component `c` is `[1, 1000]`.
    fn new_session(r: u32, c: u32, ) -> Weight {
        Weight::from_ref_time(0 as u64)
            // Standard Error: 1_193_000
            .saturating_add(Weight::from_ref_time(6_251_000 as u64).saturating_mul(r as u64))
            // Standard Error: 1_193_000
            .saturating_add(Weight::from_ref_time(31_284_000 as u64).saturating_mul(c as u64))
            .saturating_add(T::DbWeight::get().reads((2 as u64).saturating_mul(c as u64)))
            .saturating_add(T::DbWeight::get().writes((1 as u64).saturating_mul(r as u64)))
            .saturating_add(T::DbWeight::get().writes((1 as u64).saturating_mul(c as u64)))
    }
}

// For backwards compatibility and tests
impl WeightInfo for () {
    /// The range of component `b` is `[1, 100]`.
    fn set_invulnerables(b: u32, ) -> Weight {
        Weight::from_ref_time(15_508_000 as u64)
            // Standard Error: 3_000
            .saturating_add(Weight::from_ref_time(2_552_000 as u64).saturating_mul(b as u64))
            .saturating_add(RocksDbWeight::get().reads((1 as u64).saturating_mul(b as u64)))
            .saturating_add(RocksDbWeight::get().writes(1 as u64))
    }
    fn set_desired_candidates() -> Weight {
        Weight::from_ref_time(11_000_000 as u64)
            .saturating_add(RocksDbWeight::get().writes(1 as u64))
    }
    fn set_candidacy_bond() -> Weight {
        Weight::from_ref_time(11_000_000 as u64)
            .saturating_add(RocksDbWeight::get().writes(1 as u64))
    }
    /// The range of component `c` is `[1, 1000]`.
    fn register_as_candidate(c: u32, ) -> Weight {
        Weight::from_ref_time(32_462_000 as u64)
            // Standard Error: 0
            .saturating_add(Weight::from_ref_time(96_000 as u64).saturating_mul(c as u64))
            .saturating_add(RocksDbWeight::get().reads(5 as u64))
            .saturating_add(RocksDbWeight::get().writes(2 as u64))
    }
    /// The range of component `c` is `[6, 1000]`.
    fn leave_intent(c: u32, ) -> Weight {
        Weight::from_ref_time(18_851_000 as u64)
            // Standard Error: 1_000
            .saturating_add(Weight::from_ref_time(99_000 as u64).saturating_mul(c as u64))
            .saturating_add(RocksDbWeight::get().reads(1 as u64))
            .saturating_add(RocksDbWeight::get().writes(2 as u64))
    }
    fn note_author() -> Weight {
        Weight::from_ref_time(30_000_000 as u64)
            .saturating_add(RocksDbWeight::get().reads(3 as u64))
            .saturating_add(RocksDbWeight::get().writes(4 as u64))
    }
    /// The range of component `r` is `[1, 1000]`.
    /// The range of component `c` is `[1, 1000]`.
    fn new_session(r: u32, c: u32, ) -> Weight {
        Weight::from_ref_time(0 as u64)
            // Standard Error: 1_193_000
            .saturating_add(Weight::from_ref_time(6_251_000 as u64).saturating_mul(r as u64))
            // Standard Error: 1_193_000
            .saturating_add(Weight::from_ref_time(31_284_000 as u64).saturating_mul(c as u64))
            .saturating_add(RocksDbWeight::get().reads((2 as u64).saturating_mul(c as u64)))
            .saturating_add(RocksDbWeight::get().writes((1 as u64).saturating_mul(r as u64)))
            .saturating_add(RocksDbWeight::get().writes((1 as u64).saturating_mul(c as u64)))
    }
}
