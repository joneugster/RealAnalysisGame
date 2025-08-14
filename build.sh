#!/bin/bash
set -e

# Install Elan (Lean toolchain manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"

# Install npm dependencies
cd lean4game
npm ci

# Set up Lean toolchain and build
cd ../RealAnalysisGame
elan default $(cat lean-toolchain 2>/dev/null || echo "leanprover/lean4:stable")
lake build

# Build the web components
cd ../lean4game
npm run build_relay
npm run build_client
