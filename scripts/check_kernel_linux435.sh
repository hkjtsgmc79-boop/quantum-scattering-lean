#!/usr/bin/env bash
# Optional 4.35 independent process/kernel replay, AFTER full ordinary verification.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
if [[ "$(uname -s)" != Linux ]]; then
  echo 'BLOCKED: the documented lake check sandbox is Linux-only. Do not bypass it on macOS.'
  exit 2
fi
for tool in elan bwrap; do
  command -v "$tool" >/dev/null 2>&1 || { echo "BLOCKED: missing $tool"; exit 2; }
done
if [[ $# -gt 1 || ( $# -eq 1 && "$1" != --paranoid ) ]]; then
  echo 'Usage: bash scripts/check_kernel_linux435.sh [--paranoid]'
  exit 2
fi
OUT="reports/kernel435_$(date -u +%Y%m%dT%H%M%SZ)_$$"
mkdir -p "$OUT"
# This command may perform normal Lake dependency resolution; use only the pinned project.
elan run leanprover/lean4:v4.35.0 lake check "$@" 2>&1 | tee "$OUT/lake-check.log"
echo 'lake check finished successfully for this invocation; retain this log separately.'
