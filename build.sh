#!/bin/bash
set -e

echo "=== Starting build process ==="

# Install npm dependencies first with legacy peer deps to handle TypeScript conflicts
echo "=== Installing npm dependencies ==="
npm ci --legacy-peer-deps

# Install Elan with better error handling
echo "=== Installing Elan ==="
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
source ~/.elan/env

# Check if elan is available
echo "=== Checking Elan installation ==="
which elan || echo "Elan not found"
elan --version || echo "Elan version check failed"

# Try to build the Lean project
echo "=== Attempting to build RealAnalysisGame ==="
cd ../RealAnalysisGame
pwd
ls -la

# Install the toolchain from lean-toolchain file
echo "=== Installing Lean toolchain ==="
if [ -f lean-toolchain ]; then
    cat lean-toolchain
    elan default $(cat lean-toolchain)
else
    echo "No lean-toolchain file found, using stable"
    elan default stable
fi

echo "=== Updating dependencies (including mathlib) ==="
lake update || echo "Lake update failed, trying build anyway"

echo "=== Running lake build ==="
lake build || echo "Lake build failed, continuing anyway"

# Check if game data was generated
echo "=== Checking game data generation ==="
if [ -d ".lake/gamedata" ]; then
    echo "Game data found! Contents:"
    ls -la .lake/gamedata/
    
    # Verify key files exist
    if [ -f ".lake/gamedata/game.json" ] && [ -f ".lake/gamedata/inventory.json" ]; then
        echo "✓ Required game files found"
    else
        echo "⚠ Warning: Some required game files missing"
        echo "Files in gamedata:"
        ls -la .lake/gamedata/ || echo "Cannot list gamedata contents"
    fi
else
    echo "⚠ Warning: .lake/gamedata directory not found"
    echo "Available .lake contents:"
    ls -la .lake/ || echo "Cannot list .lake contents"
fi

# Build the web components
echo "=== Building relay ==="
cd ../lean4game
npm run build_relay

echo "=== Building client ==="
npm run build_client

# Copy game data to the client's public directory
echo "=== Copying game data to client public directory ==="
cd ../RealAnalysisGame

# Create the required directory structure in the built client
CLIENT_DATA_DIR="../lean4game/client/dist/data/g/local/RealAnalysisGame"
mkdir -p "$CLIENT_DATA_DIR"

if [ -d ".lake/gamedata" ]; then
    echo "Copying game data to $CLIENT_DATA_DIR"
    cp -r .lake/gamedata/* "$CLIENT_DATA_DIR/"
    
    echo "✓ Game data copied successfully"
    echo "Copied files:"
    ls -la "$CLIENT_DATA_DIR"
    
    # Verify the critical files
    if [ -f "$CLIENT_DATA_DIR/game.json" ] && [ -f "$CLIENT_DATA_DIR/inventory.json" ]; then
        echo "✓ Critical game files verified in client dist"
    else
        echo "❌ Critical game files missing in client dist"
        exit 1
    fi
else
    echo "❌ No game data to copy - this will cause the blank game issue"
    exit 1
fi

# Also copy to root dist if it exists (for Vercel)
ROOT_DATA_DIR="../lean4game/dist/data/g/local/RealAnalysisGame"
if [ -d "../lean4game/dist" ]; then
    mkdir -p "$ROOT_DATA_DIR"
    cp -r .lake/gamedata/* "$ROOT_DATA_DIR/"
    echo "✓ Game data also copied to root dist directory"
fi

echo "=== Build process completed ==="
echo "=== Final verification ==="
echo "Client dist structure:"
find "../lean4game/client/dist" -name "*.json" | grep -E "(game|inventory)\.json" || echo "No game/inventory.json found in client dist"
echo "Build artifacts ready for deployment"
