#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"
python_bin=${PYTHON:-python3}
"$python_bin" -c 'import sys; sys.exit("Python >=3.11 required; set PYTHON to a suitable interpreter") if sys.version_info < (3, 11) else None'
mkdir -p .lake/verification

"$python_bin" scripts/check-pins.py
lake build GeneralizedStafford > .lake/verification/build.log 2>&1

project_lean() {
  lake env bash -c '
    repo_root=$1
    shift
    export LEAN_PATH="$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
    exec lean --trust=0 "$@"
  ' bash "$repo_root" "$@"
}

{
  echo 'module'
  echo 'import GeneralizedStafford'
  sed '/^[[:space:]]*$/d; s/^/#print axioms /' docs/endpoints.txt
} > .lake/verification/AxiomAudit.lean
project_lean .lake/verification/AxiomAudit.lean > .lake/verification/axioms.log 2>&1
"$python_bin" scripts/check-axiom-closure.py --endpoints docs/endpoints.txt .lake/verification/axioms.log
echo 'Verification passed: pinned dependencies, full library, and endpoint axioms.'
