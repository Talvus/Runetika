//! Bevy Systems that bridge Lemma proof operations to gameplay.

use bevy::prelude::*;

use super::resources::{ProofWorkspace, ProofCertificates};
use super::events::ProofVerifiedEvent;

/// Checks if the current proof is complete and fires verification event.
pub fn check_proof_completion(
    workspace: Res<ProofWorkspace>,
    mut proof_events: EventWriter<ProofVerifiedEvent>,
    mut certificates: ResMut<ProofCertificates>,
) {
    let Ok(ws) = workspace.shared.lock() else { return };

    // Only check if there are tiles placed
    if ws.graph.tile_count() == 0 {
        return;
    }

    if !ws.graph.is_complete() {
        return;
    }
    // Re-verify each frame the graph is complete and dedupe by Merkle root.
    // The previous gate of `certificates.earned.is_empty()` made this a
    // one-shot — once the player earned their first certificate, no
    // subsequent proof would ever fire `ProofVerifiedEvent`.
    match lemma_verify::verify_graph(&ws.graph) {
        lemma_verify::VerificationResult::Valid(cert) => {
            if certificates
                .earned
                .iter()
                .any(|c| c.merkle_root == cert.merkle_root)
            {
                return; // already recorded this exact proof state
            }
            info!("Proof verified! Certificate: {}", cert.merkle_root);
            certificates.earned.push(cert.clone());
            proof_events.write(ProofVerifiedEvent { certificate: cert });
        }
        lemma_verify::VerificationResult::Invalid(errors) => {
            warn!("Proof invalid: {:?}", errors);
        }
        lemma_verify::VerificationResult::Incomplete { open_goal_count, .. } => {
            debug!("Proof has {} remaining goals", open_goal_count);
        }
    }
}
