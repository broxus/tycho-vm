/// Execution result.
pub type TxResult<T, E = TxError> = ::core::result::Result<T, E>;

/// Execution error.
#[derive(Debug, thiserror::Error)]
pub enum TxError {
    #[error("transaction skipped")]
    Skipped,
    #[error("fatal error")]
    Fatal(#[from] anyhow::Error),
}

impl From<tycho_types::error::Error> for TxError {
    #[inline]
    fn from(value: tycho_types::error::Error) -> Self {
        Self::Fatal(anyhow::Error::from(value))
    }
}
