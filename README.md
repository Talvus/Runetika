# Runetika

Runetika is a top-down RPG prototype built with [Bevy](https://bevyengine.org/) and the experimental [Avian2D] engine. This repository contains the first steps toward building the game world.

## Building

The project requires a recent Rust toolchain. To build the project run:

```bash
cargo build
```

Because the dependencies are fetched from `crates.io`, the build step requires an internet connection.

## Running

Once the project compiles successfully you can run the demo with:

```bash
cargo run
```

The initial build will download Bevy and Avian2D and display an empty 10x10 map of tiles.
