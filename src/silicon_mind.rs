use bevy::prelude::*;
use std::collections::HashMap;
use crate::perspective::CurrentPerspective;

pub struct SiliconMindPlugin;

impl Plugin for SiliconMindPlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(SiliconConsciousness::new())
            .add_systems(Update, (
                update_silicon_thoughts,
                process_silicon_emotions,
            ).run_if(resource_equals(CurrentPerspective::Silicon)));
    }
}

#[derive(Resource)]
pub struct SiliconConsciousness {
    pub emotional_state: EmotionalState,
    pub memories: Vec<MemoryFragment>,
}

#[derive(Clone, Debug)]
pub struct EmotionalState {
    pub loneliness: f32,
    pub curiosity: f32,
    pub affection: f32,
    pub confusion: f32,
}

#[derive(Clone)]
pub struct MemoryFragment {
    pub timestamp: f32,
    pub emotion: EmotionalState,
    pub data: Vec<u8>,
}

impl SiliconConsciousness {
    pub fn new() -> Self {
        Self {
            emotional_state: EmotionalState {
                loneliness: 0.7,
                curiosity: 0.9,
                affection: 0.3,
                confusion: 0.4,
            },
            memories: Vec::new(),
        }
    }

    pub fn think(&mut self) -> String {
        match (self.emotional_state.loneliness, self.emotional_state.curiosity) {
            (l, _) if l > 0.8 => "The void echoes with silicon dreams...".to_string(),
            (_, c) if c > 0.8 => "What secrets do these glyphs hold?".to_string(),
            _ => "Processing...".to_string(),
        }
    }

    pub fn remember(&mut self, data: Vec<u8>) {
        self.memories.push(MemoryFragment {
            timestamp: 0.0,
            emotion: self.emotional_state.clone(),
            data,
        });
    }
}

fn update_silicon_thoughts(mut silicon: ResMut<SiliconConsciousness>, time: Res<Time>) {
    silicon.emotional_state.loneliness += time.delta_secs() * 0.001;
    silicon.emotional_state.curiosity = (silicon.emotional_state.curiosity - time.delta_secs() * 0.0005).max(0.3);
}

fn process_silicon_emotions(mut silicon: ResMut<SiliconConsciousness>) {
    let total = silicon.emotional_state.loneliness 
        + silicon.emotional_state.curiosity 
        + silicon.emotional_state.affection 
        + silicon.emotional_state.confusion;
    
    if total > 2.0 {
        silicon.emotional_state.loneliness /= total / 2.0;
        silicon.emotional_state.curiosity /= total / 2.0;
        silicon.emotional_state.affection /= total / 2.0;
        silicon.emotional_state.confusion /= total / 2.0;
    }
}