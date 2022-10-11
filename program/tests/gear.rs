#![cfg(feature = "bin")]
use common::env;
use gear_program::{api::Api, result::Error};
use std::path::PathBuf;

mod cmd;
mod common;

#[tokio::test]
async fn api_timeout() {
    assert!(matches!(
        Api::new_with_timeout(None, Some(10)).await.err(),
        Some(Error::Ws(
            jsonrpsee_client_transport::ws::WsHandshakeError::Timeout(..)
        ))
    ));
}

#[test]
fn paths() {
<<<<<<< HEAD
    assert!(PathBuf::from(env::bin("gear")).exists());
=======
    assert!(PathBuf::from(env::bin("gear-node")).exists());
>>>>>>> 4ca47efe (Merge branch 'master' into vara-stage-1)
    assert!(PathBuf::from(env::bin("gprogram")).exists());
}
