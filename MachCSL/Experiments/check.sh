#!/usr/bin/env bash
# Serialize standalone Lean checks across the experiment runs and cap the entire job.
# Reuse compiled imports; pass ordinary `lean` arguments, not Lake build targets.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if (( $# == 0 )); then
  echo "usage: $0 [lean options] path/to/File.lean" >&2
  exit 2
fi
mkdir -p .lake
exec 9>.lake/focused-experiments.lock
flock 9
check_log=$(mktemp .lake/focused-check-output.XXXXXX)
trap 'rm -f "$check_log"' EXIT
systemd-run --user --wait --pipe --collect --unit="req-focused-check-$$" \
  --working-directory="$PWD" \
  -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 \
  -p OOMPolicy=kill -p TasksMax=64 -p RuntimeMaxSec=180 \
  --setenv=LEAN_NUM_THREADS=1 \
  "$(command -v lake)" env lean -j1 \
  -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -Dlinter.unusedVariables=false -Dlinter.unusedSectionVars=false \
  -DmaxRecDepth=8192 \
  -Dbackward.isDefEq.respectTransparency=false \
  -Dbackward.isDefEq.respectTransparency.types=false "$@" 2>&1 | tee "$check_log"
# An explicitly stopped service can have Result=success even when its main
# process was killed. Require normal completion of Lean, not just unit success.
check_status=$(rg '^Main processes terminated with:' "$check_log" | tail -n 1 || true)
if [[ "$check_status" != 'Main processes terminated with: code=exited, status=0/SUCCESS' ]]; then
  echo "Focused check failed: Lean did not exit normally with status 0." >&2
  exit 1
fi
