//! Command `claim`
use crate::{api::signer::Signer, result::Result, utils};
use structopt::StructOpt;

/// Claim value from mailbox.
#[derive(StructOpt, Debug)]
pub struct Claim {
    /// Claim value from.
    message_id: String,
}

impl Claim {
    pub async fn exec(&self, signer: Signer) -> Result<()> {
        let message_id = utils::hex_to_hash(&self.message_id)?.into();

        signer.claim_value(message_id).await?;

        Ok(())
    }
}
