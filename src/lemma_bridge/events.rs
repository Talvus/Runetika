//! Bevy Events for proof operations.

use bevy::prelude::*;
use lemma_verify::Certificate;

/// Fired when a proof graph is verified and a certificate is generated.
#[derive(Event)]
pub struct ProofVerifiedEvent {
    #[allow(dead_code)]
    pub certificate: Certificate,
}
