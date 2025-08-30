use std::io::{Write, Read};
use flate2::write::GzEncoder;
use flate2::read::GzDecoder;
use flate2::Compression;
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize, PartialEq)]
struct GameSaveData {
    player_name: String,
    level: u32,
    score: u64,
    inventory: Vec<String>,
    position: (f32, f32),
    settings: GameSettings,
}

#[derive(Debug, Serialize, Deserialize, PartialEq)]
struct GameSettings {
    volume: f32,
    graphics_quality: String,
    fullscreen: bool,
}

pub fn test_compression() {
    println!("=== Runetika Compression Test ===\n");
    
    let save_data = GameSaveData {
        player_name: "CosmicExplorer".to_string(),
        level: 42,
        score: 999999,
        inventory: vec![
            "Quantum Crystal".to_string(),
            "Silicon Fragment".to_string(),
            "Ancient Glyph".to_string(),
            "Terminal Key".to_string(),
            "Star Map".to_string(),
        ],
        position: (256.5, 512.75),
        settings: GameSettings {
            volume: 0.75,
            graphics_quality: "Ultra".to_string(),
            fullscreen: true,
        },
    };
    
    println!("Original data:");
    println!("{:#?}\n", save_data);
    
    let json_data = serde_json::to_string_pretty(&save_data).unwrap();
    let original_size = json_data.len();
    println!("JSON representation ({} bytes):", original_size);
    println!("{}\n", json_data);
    
    println!("Testing different compression levels:");
    println!("{}", "-".repeat(50));
    
    for level in [Compression::none(), Compression::fast(), Compression::default(), Compression::best()] {
        let level_name = match level.level() {
            0 => "None",
            1 => "Fast",
            6 => "Default",
            9 => "Best",
            _ => "Unknown",
        };
        
        let start = std::time::Instant::now();
        
        let mut encoder = GzEncoder::new(Vec::new(), level);
        encoder.write_all(json_data.as_bytes()).unwrap();
        let compressed = encoder.finish().unwrap();
        
        let compression_time = start.elapsed();
        let compressed_size = compressed.len();
        let ratio = (original_size as f64 - compressed_size as f64) / original_size as f64 * 100.0;
        
        println!("Level: {} ({})", level.level(), level_name);
        println!("  Compressed size: {} bytes", compressed_size);
        println!("  Compression ratio: {:.1}% reduction", ratio);
        println!("  Compression time: {:?}", compression_time);
        
        let start = std::time::Instant::now();
        let mut decoder = GzDecoder::new(&compressed[..]);
        let mut decompressed = String::new();
        decoder.read_to_string(&mut decompressed).unwrap();
        let decompression_time = start.elapsed();
        
        println!("  Decompression time: {:?}", decompression_time);
        
        let restored: GameSaveData = serde_json::from_str(&decompressed).unwrap();
        assert_eq!(save_data, restored);
        println!("  ✓ Data integrity verified\n");
    }
    
    test_large_data();
}

fn test_large_data() {
    println!("=== Large Data Compression Test ===\n");
    
    let large_text = "In the depths of space, the silicon civilization left behind mysterious glyphs. ".repeat(1000);
    let original_size = large_text.len();
    println!("Testing with {} bytes of repetitive text data", original_size);
    
    let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
    encoder.write_all(large_text.as_bytes()).unwrap();
    let compressed = encoder.finish().unwrap();
    let compressed_size = compressed.len();
    
    let ratio = (original_size as f64 - compressed_size as f64) / original_size as f64 * 100.0;
    println!("Compressed to {} bytes ({:.1}% reduction)", compressed_size, ratio);
    
    let random_data: Vec<u8> = (0..10000).map(|_| rand::random()).collect();
    println!("\nTesting with {} bytes of random binary data", random_data.len());
    
    let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
    encoder.write_all(&random_data).unwrap();
    let compressed = encoder.finish().unwrap();
    
    let ratio = (random_data.len() as f64 - compressed.len() as f64) / random_data.len() as f64 * 100.0;
    println!("Compressed to {} bytes ({:.1}% change)", compressed.len(), ratio);
    println!("Note: Random data typically doesn't compress well\n");
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_compression_integrity() {
        let data = GameSaveData {
            player_name: "Tester".to_string(),
            level: 1,
            score: 100,
            inventory: vec!["Item".to_string()],
            position: (0.0, 0.0),
            settings: GameSettings {
                volume: 1.0,
                graphics_quality: "Low".to_string(),
                fullscreen: false,
            },
        };
        
        let json = serde_json::to_string(&data).unwrap();
        
        let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
        encoder.write_all(json.as_bytes()).unwrap();
        let compressed = encoder.finish().unwrap();
        
        let mut decoder = GzDecoder::new(&compressed[..]);
        let mut decompressed = String::new();
        decoder.read_to_string(&mut decompressed).unwrap();
        
        let restored: GameSaveData = serde_json::from_str(&decompressed).unwrap();
        assert_eq!(data, restored);
    }
}