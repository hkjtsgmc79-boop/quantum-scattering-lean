#!/usr/bin/env bash
# Explicitly run this script to download ONLY the pinned project environment.
# Does not change elan default, delete 4.30, or touch another project's cache.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
TC='leanprover/lean4:v4.35.0'
STAMP="$(date -u +%Y%m%dT%H%M%SZ)_$$"
OUT="reports/setup435_$STAMP"
mkdir -p "$OUT"
exec > >(tee "$OUT/setup.log") 2>&1
trap 'rc=$?; printf "SETUP_EXIT_CODE=%s\n" "$rc" > "$OUT/exit_code.txt"; exit "$rc"' EXIT
for tool in python3 git elan; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "BLOCKED: $tool is missing. See 00_START_HERE.md. No proof verification performed."
    exit 2
  fi
done
python3 -c 'import sys; assert sys.version_info >= (3,9), "Python 3.9+ required"'
# Fail before any downloads if this checkout does not target the declared version.
python3 - <<'PY'
import sys
from pathlib import Path
sys.path.insert(0,'scripts')
from migration_support import load_lock
p=Path('.')
l=load_lock(p)
assert l['target_toolchain']=='leanprover/lean4:v4.35.0'
assert (p/'lean-toolchain').read_text().strip()==l['target_toolchain']
assert 'rev = "'+l['mathlib']['commit']+'"' in (p/'lakefile.toml').read_text()
PY
# Refuse symlinked dependency directories to avoid altering a shared 4.30 checkout.
if [[ -L .lake || -L .lake/packages || -L .lake/packages/mathlib ]]; then
  echo 'BLOCKED: project dependency directories are symlinked. Use a fresh extraction.'
  exit 2
fi
elan toolchain install "$TC"
elan run "$TC" lean --version
MATHLIB_NO_CACHE_ON_UPDATE=1 elan run "$TC" lake --keep-toolchain update
# Do not obtain a cache for an unexpected resolution.
python3 - <<'PY'
import sys
from pathlib import Path
sys.path.insert(0,'scripts')
from migration_support import load_lock,require_manifest
r=Path('.');l=load_lock(r)
wanted=dict(l['transitive_packages']);wanted['mathlib']=l['mathlib']['commit']
require_manifest(r/'lake-manifest.json',wanted)
assert (r/'.lake/packages/mathlib/lean-toolchain').read_text().strip()==l['target_toolchain']
PY
elan run "$TC" lake exe cache get
# Mathlib’s cache does not build this locked dependency.
elan run "$TC" lake build Cli
LEAN="$(elan run "$TC" elan which lean)"
python3 scripts/verify.py --lean "$LEAN" --mathlib-root "$PWD/.lake/packages/mathlib" --preflight-only
printf '\nEnvironment preparation complete. NO framework proofs were verified by setup.\n'
printf 'Next: bash scripts/verify.sh --target release\n'
