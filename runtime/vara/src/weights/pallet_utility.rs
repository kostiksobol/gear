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

//! Autogenerated weights for pallet_utility
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-07-13, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! CPU: `Intel(R) Xeon(R) Platinum 8375C CPU @ 2.90GHz`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("vara-dev"), DB CACHE: 1024

// Executed Command:
// ./target/production/gear benchmark pallet --chain=vara-dev --steps=50 --repeat=20 --pallet=pallet_utility --extrinsic=* --execution=wasm --wasm-execution=compiled --heap-pages=4096 --output=./scripts/benchmarking/weights-output/pallet_utility.rs --template=.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(clippy::unnecessary_cast)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_utility.
pub trait WeightInfo {
    fn batch(c: u32, ) -> Weight;
    fn as_derivative() -> Weight;
    fn batch_all(c: u32, ) -> Weight;
    fn dispatch_as() -> Weight;
    fn force_batch(c: u32, ) -> Weight;
}

/// Weights for pallet_utility using the Gear node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_utility::WeightInfo for SubstrateWeight<T> {
    /// The range of component `c` is `[0, 1000]`.
    fn batch(c: u32, ) -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 5_343_000 picoseconds.
        Weight::from_parts(5_077_292, 0)
            // Standard Error: 4_654
            .saturating_add(Weight::from_parts(4_019_596, 0).saturating_mul(c.into()))
    }
    fn as_derivative() -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 3_844_000 picoseconds.
        Weight::from_parts(4_099_000, 0)
    }
    /// The range of component `c` is `[0, 1000]`.
    fn batch_all(c: u32, ) -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 5_245_000 picoseconds.
        Weight::from_parts(13_362_133, 0)
            // Standard Error: 4_186
            .saturating_add(Weight::from_parts(4_185_912, 0).saturating_mul(c.into()))
    }
    fn dispatch_as() -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 6_954_000 picoseconds.
        Weight::from_parts(7_186_000, 0)
    }
    /// The range of component `c` is `[0, 1000]`.
    fn force_batch(c: u32, ) -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 5_315_000 picoseconds.
        Weight::from_parts(6_135_028, 0)
            // Standard Error: 4_945
            .saturating_add(Weight::from_parts(4_023_158, 0).saturating_mul(c.into()))
    }
}

// For backwards compatibility and tests
impl WeightInfo for () {
    /// The range of component `c` is `[0, 1000]`.
    fn batch(c: u32, ) -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 5_343_000 picoseconds.
        Weight::from_parts(5_077_292, 0)
            // Standard Error: 4_654
            .saturating_add(Weight::from_parts(4_019_596, 0).saturating_mul(c.into()))
    }
    fn as_derivative() -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 3_844_000 picoseconds.
        Weight::from_parts(4_099_000, 0)
    }
    /// The range of component `c` is `[0, 1000]`.
    fn batch_all(c: u32, ) -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 5_245_000 picoseconds.
        Weight::from_parts(13_362_133, 0)
            // Standard Error: 4_186
            .saturating_add(Weight::from_parts(4_185_912, 0).saturating_mul(c.into()))
    }
    fn dispatch_as() -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 6_954_000 picoseconds.
        Weight::from_parts(7_186_000, 0)
    }
    /// The range of component `c` is `[0, 1000]`.
    fn force_batch(c: u32, ) -> Weight {
        // Proof Size summary in bytes:
        //  Measured:  `0`
        //  Estimated: `0`
        // Minimum execution time: 5_315_000 picoseconds.
        Weight::from_parts(6_135_028, 0)
            // Standard Error: 4_945
            .saturating_add(Weight::from_parts(4_023_158, 0).saturating_mul(c.into()))
    }
}
