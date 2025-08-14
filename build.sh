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

# Build the web components
echo "=== Building relay ==="
cd ../lean4game
npm run build_relay

echo "=== Building client ==="
npm run build_client

echo "=== Build process completed ==="
