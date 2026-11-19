#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
# Isolated, pinned tool installation. The SMT binary is an untrusted search
# heuristic; every selected core is replayed with Lean's proof-producing omega.
python3 -m pip install --upgrade --target .lake/solver-python z3-solver==4.15.4.0
.lake/solver-python/bin/z3 --version
