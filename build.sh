#!/bin/bash
set -e

echo "=== Starting build process ==="

# Install Elan (Lean toolchain manager)
echo "=== Installing Elan ==="
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"

# Install npm dependencies (we're already in lean4game directory)
echo "=== Installing npm dependencies ==="
npm ci

# Set up Lean toolchain and build (go to RealAnalysisGame directory)
echo "=== Setting up Lean toolchain ==="
cd ../RealAnalysisGame
pwd
ls -la
elan default $(cat lean-toolchain 2>/dev/null || echo "leanprover/lean4:stable")

echo "=== Running lake build ==="
lake build

echo "=== Lake build completed ==="

# Build the web components (go back to lean4game directory)
echo "=== Building relay ==="
cd ../lean4game
npm run build_relay

echo "=== Building client ==="
npm run build_client

echo "=== Build process completed successfully ==="
