#!/bin/bash
set -e

echo "=== Starting simplified build process ==="

# Just build the web components without Lean for now
echo "=== Installing npm dependencies ==="
npm ci

echo "=== Building relay ==="
npm run build_relay

echo "=== Building client ==="
npm run build_client

echo "=== Build process completed ==="
