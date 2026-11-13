#!/usr/bin/env bash
# New environment + complete unchanged mathematical target; fail at first error.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
bash scripts/prepare_lean435.sh
exec bash scripts/verify.sh --target release "$@"
