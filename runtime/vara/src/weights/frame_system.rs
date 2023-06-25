// This file is part of Gear.

// Copyright (C) 2022-2023 Gear Technologies Inc.
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

//! Autogenerated weights for frame_system
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-05-03, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! CPU: `Intel(R) Xeon(R) Platinum 8375C CPU @ 2.90GHz`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("vara-dev"), DB CACHE: 1024

// Executed Command:
// ./target/production/gear benchmark pallet --chain=vara-dev --steps=50 --repeat=20 --pallet=frame_system --extrinsic=* --execution=wasm --wasm-execution=compiled --heap-pages=4096 --output=./scripts/benchmarking/weights-output/frame_system.rs --template=.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(clippy::unnecessary_cast)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for frame_system.
pub trait WeightInfo {
    fn remark(b: u32, ) -> Weight;
    fn remark_with_event(b: u32, ) -> Weight;
    fn set_heap_pages() -> Weight;
    fn set_storage(i: u32, ) -> Weight;
    fn kill_storage(i: u32, ) -> Weight;
    fn kill_prefix(p: u32, ) -> Weight;
}

/// Weights for frame_system using the Gear node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> frame_system::WeightInfo for SubstrateWeight<T> {
    /// The range of component `b` is `[0, 1310720]`.
    fn remark(b: u32, ) -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 1_528_000 picoseconds.
        Weight::from_parts(1_152_112, 0)
            // Standard Error: 0
            .saturating_add(Weight::from_parts(516, 0).saturating_mul(b.into()))
    }
    /// The range of component `b` is `[0, 1310720]`.
    fn remark_with_event(b: u32, ) -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 6_073_000 picoseconds.
        Weight::from_parts(6_216_000, 0)
            // Standard Error: 2
            .saturating_add(Weight::from_parts(1_512, 0).saturating_mul(b.into()))
    }
    fn set_heap_pages() -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `1485`
        // Minimum execution time: 3_095_000 picoseconds.
        Weight::from_parts(3_388_000, 1485)
            .saturating_add(T::DbWeight::get().reads(1_u64))
            .saturating_add(T::DbWeight::get().writes(2_u64))
    }
    /// The range of component `i` is `[0, 1000]`.
    fn set_storage(i: u32, ) -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 1_600_000 picoseconds.
        Weight::from_parts(1_634_000, 0)
            // Standard Error: 1_053
            .saturating_add(Weight::from_parts(682_920, 0).saturating_mul(i.into()))
            .saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(i.into())))
    }
    /// The range of component `i` is `[0, 1000]`.
    fn kill_storage(i: u32, ) -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 1_594_000 picoseconds.
        Weight::from_parts(1_669_000, 0)
            // Standard Error: 742
            .saturating_add(Weight::from_parts(526_943, 0).saturating_mul(i.into()))
            .saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(i.into())))
    }
    /// The range of component `p` is `[0, 1000]`.
    fn kill_prefix(p: u32, ) -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `86 + p * (69 ±0)`
        //  Estimated: `81 + p * (70 ±0)`
        // Minimum execution time: 3_272_000 picoseconds.
        Weight::from_parts(3_343_000, 81)
            // Standard Error: 1_239
            .saturating_add(Weight::from_parts(1_105_334, 0).saturating_mul(p.into()))
            .saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(p.into())))
            .saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(p.into())))
            .saturating_add(Weight::from_parts(0, 70).saturating_mul(p.into()))
    }
}

// For backwards compatibility and tests
impl WeightInfo for () {
    /// The range of component `b` is `[0, 1310720]`.
    fn remark(b: u32, ) -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 1_528_000 picoseconds.
        Weight::from_parts(1_152_112, 0)
            // Standard Error: 0
            .saturating_add(Weight::from_parts(516, 0).saturating_mul(b.into()))
    }
    /// The range of component `b` is `[0, 1310720]`.
    fn remark_with_event(b: u32, ) -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 6_073_000 picoseconds.
        Weight::from_parts(6_216_000, 0)
            // Standard Error: 2
            .saturating_add(Weight::from_parts(1_512, 0).saturating_mul(b.into()))
    }
    fn set_heap_pages() -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `1485`
        // Minimum execution time: 3_095_000 picoseconds.
        Weight::from_parts(3_388_000, 1485)
            .saturating_add(RocksDbWeight::get().reads(1_u64))
            .saturating_add(RocksDbWeight::get().writes(2_u64))
    }
    /// The range of component `i` is `[0, 1000]`.
    fn set_storage(i: u32, ) -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 1_600_000 picoseconds.
        Weight::from_parts(1_634_000, 0)
            // Standard Error: 1_053
            .saturating_add(Weight::from_parts(682_920, 0).saturating_mul(i.into()))
            .saturating_add(RocksDbWeight::get().writes((1_u64).saturating_mul(i.into())))
    }
    /// The range of component `i` is `[0, 1000]`.
    fn kill_storage(i: u32, ) -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 1_594_000 picoseconds.
        Weight::from_parts(1_669_000, 0)
            // Standard Error: 742
            .saturating_add(Weight::from_parts(526_943, 0).saturating_mul(i.into()))
            .saturating_add(RocksDbWeight::get().writes((1_u64).saturating_mul(i.into())))
    }
    /// The range of component `p` is `[0, 1000]`.
    fn kill_prefix(p: u32, ) -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `86 + p * (69 ±0)`
        //  Estimated: `81 + p * (70 ±0)`
        // Minimum execution time: 3_272_000 picoseconds.
        Weight::from_parts(3_343_000, 81)
            // Standard Error: 1_239
            .saturating_add(Weight::from_parts(1_105_334, 0).saturating_mul(p.into()))
            .saturating_add(RocksDbWeight::get().reads((1_u64).saturating_mul(p.into())))
            .saturating_add(RocksDbWeight::get().writes((1_u64).saturating_mul(p.into())))
            .saturating_add(Weight::from_parts(0, 70).saturating_mul(p.into()))
    }
}
