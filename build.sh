#!/bin/bash
set -e

echo "=== Starting build process ==="

# Install npm dependencies first
echo "=== Installing npm dependencies ==="
npm ci

# Try to install Lean via a package manager instead of Elan
echo "=== Installing Lean via apt ==="
curl -O https://github.com/leanprover/lean4/releases/download/v4.21.0/lean-4.21.0-linux.tar.gz
tar -xzf lean-4.21.0-linux.tar.gz
export PATH="$PWD/lean-4.21.0-linux/bin:$PATH"

# Check if Lean is available
echo "=== Checking Lean installation ==="
which lean || echo "Lean not found in PATH"
lean --version || echo "Lean version check failed"

# Try to build the Lean project
echo "=== Attempting to build RealAnalysisGame ==="
cd ../RealAnalysisGame
pwd
ls -la
lake build || echo "Lake build failed, continuing anyway"

# Build the web components
echo "=== Building relay ==="
cd ../lean4game
npm run build_relay

echo "=== Building client ==="
npm run build_client

echo "=== Build process completed ==="
