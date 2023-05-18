use ft_io::*;
use fungible_token::WASM_BINARY;
use gclient::{EventProcessor, GearApi, Result, WSAddress};
use gstd::{vec, ActorId, Encode, Vec};

/// This constant defines the number of messages in the batch.
/// It is calculated empirically, and 25 is considered the optimal value for
/// messages in this test. If the value were larger, transactions would
/// exhaust the block limits.
const BATCH_CHUNK_SIZE: usize = 25;
const MAX_GAS_LIMIT: u64 = 250_000_000_000;

/// This test runs stress-loading for the fungible token contract.
/// Its primary purpose is to benchmark memory allocator gas consumption.
/// It does not verify whether the contract or the runtime works correctly.
///
/// See [galloc optimization doc](../../../galloc/docs/optimization.md) for
/// reference.
#[ignore = "reason: this test requires a running node, so it is ignored by default"]
#[tokio::test]
async fn stress_test() -> Result<()> {
    let api = GearApi::dev().await?;

    // Subscribing for events.
    let mut listener = api.subscribe().await?;

    // Checking that blocks still running.
    assert!(listener.blocks_running().await?);

    // Uploading program.
    let init_msg = InitConfig {
        name: "MyToken".to_string(),
        symbol: "MTK".to_string(),
        decimals: 18,
    }
    .encode();

    let (message_id, program_id, _hash) = api
        .upload_program_bytes(WASM_BINARY.to_vec(), [137u8], init_msg, MAX_GAS_LIMIT, 0)
        .await?;

    assert!(listener.message_processed(message_id).await?.succeed());

    // Getting basic users and their actor ids.
    let users = vec!["//Alice", "//Bob"];

    // Creating batch of transactions for each user.
    let mut batch: Vec<FTAction> = vec![];

    for user in users {
        let api = GearApi::init_with(WSAddress::dev(), user).await?;
        let actor_id =
            ActorId::from_slice(&api.account_id().encode()).expect("failed to create actor id");

        // Mint 1_000_000 tokens to main user
        let mint_payload = FTAction::Mint(1_000_000);
        batch.push(mint_payload);

        // Transfer 6_000 tokens to users 1-20
        for i in 1..=20u64 {
            let transfer_payload = FTAction::Transfer {
                from: actor_id,
                to: i.into(),
                amount: 6_000,
            };
            batch.push(transfer_payload);
        }

        // Check the balance of `user` and users 1-20
        let balance_payload = FTAction::BalanceOf(actor_id);
        batch.push(balance_payload);

        for i in 1..=20u64 {
            let balance_payload = FTAction::BalanceOf(i.into());
            batch.push(balance_payload);
        }

        // Users 1-20 send 1_000 tokens to users 21-40
        for i in 1..=20u64 {
            let transfer_payload = FTAction::Transfer {
                from: i.into(),
                to: (i + 20).into(),
                amount: 1_000,
            };
            batch.push(transfer_payload);
        }

        // Check the balance of users 1..20 after transfers
        for i in 1..=20u64 {
            let balance_payload = FTAction::BalanceOf(i.into());
            batch.push(balance_payload);
        }

        // Mint 10_000_000 tokens to main user
        let mint_payload = FTAction::Mint(10_000_000);
        batch.push(mint_payload);

        // Mint 5_000 tokens, transfer them to users 87-120 and check their balance
        for i in 87..=120u64 {
            let mint_payload = FTAction::Mint(5_000);
            batch.push(mint_payload);

            let transfer_payload = FTAction::Transfer {
                from: actor_id,
                to: i.into(),
                amount: 5_000,
            };
            batch.push(transfer_payload);

            let balance_payload = FTAction::BalanceOf(i.into());
            batch.push(balance_payload);
        }

        // Same as above, but for users 918-1339 and then these users send 1_000 tokens
        // to user i*2
        for i in 918..=1339u64 {
            let mint_payload = FTAction::Mint(5_000);
            batch.push(mint_payload);

            let transfer_payload = FTAction::Transfer {
                from: actor_id,
                to: i.into(),
                amount: 5_000,
            };
            batch.push(transfer_payload);

            let transfer_payload = FTAction::Transfer {
                from: i.into(),
                to: (i * 2).into(),
                amount: i as u128 / 4u128,
            };
            batch.push(transfer_payload);
        }
    }

    // Converting batch
    let batch: Vec<(_, Vec<u8>, u64, _)> = batch
        .iter()
        .map(|x| (program_id, x.encode(), MAX_GAS_LIMIT, 0))
        .collect();

    // Sending batch
    for chunk in batch.chunks_exact(BATCH_CHUNK_SIZE) {
        api.send_message_bytes_batch(chunk.to_vec()).await?;
    }

    Ok(())
}
