//! Bevy Resources wrapping Lemma's proof types.

use bevy::prelude::*;
use std::sync::{Arc, Mutex};

use lemma_geometry::compose::ProofGraph;
use lemma_geometry::tile::TileLibrary;
use lemma_alien::StandardElaborator;
use lemma_verify::Certificate;

/// The active proof workspace — wraps ProofGraph and TileLibrary.
///
/// Uses Arc<Mutex<>> for shared access between Bevy systems and
/// terminal Command trait objects (which only receive &self).
#[derive(Resource)]
pub struct ProofWorkspace {
    /// Shared proof graph state accessible from terminal commands
    pub shared: Arc<Mutex<ProofWorkspaceInner>>,
}

/// Inner proof workspace state behind the shared lock.
pub struct ProofWorkspaceInner {
    /// The tile library with all available proof tiles
    pub library: TileLibrary,
    /// The current proof graph
    pub graph: ProofGraph,
    /// The ALIEN elaborator for parsing/elaborating expressions
    pub elaborator: StandardElaborator,
}

impl ProofWorkspace {
    pub fn new() -> Self {
        let library = TileLibrary::standard();
        let graph = ProofGraph::new(library.clone());
        let elaborator = StandardElaborator::new();

        ProofWorkspace {
            shared: Arc::new(Mutex::new(ProofWorkspaceInner {
                library,
                graph,
                elaborator,
            })),
        }
    }
}

/// Collection of earned proof certificates.
#[derive(Resource, Default)]
pub struct ProofCertificates {
    pub earned: Vec<Certificate>,
}
