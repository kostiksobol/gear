#[frame_support::pallet]
pub mod pallet {
    use frame_support::pallet_prelude::*;
    use sp_std::prelude::*;
    use gear_core::ids::ProgramId;

    pub(crate) const BUILTINS_STORAGE_VERSION: StorageVersion = StorageVersion::new(2);

    #[pallet::config]
    pub trait Config: frame_system::Config {
    }

    #[pallet::storage]
    #[pallet::unbounded] // Unbounded: No direct user access, maximum value length should be controlled in access api
    pub(crate) type KeyStorage<T: Config> = StorageNMap<
        _,
        (
            NMapKey<Identity, ProgramId>,
            NMapKey<Blake2_128Concat, Vec<u8>>,
        ),
        Vec<u8>,
        ValueQuery,
    >;

    #[pallet::pallet]
    #[pallet::storage_version(BUILTINS_STORAGE_VERSION)]
    pub struct Pallet<T>(_);

}
