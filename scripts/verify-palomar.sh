#!/usr/bin/env bash
set -euo pipefail

CDPATH=
repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"

tool_root=.lake/palomar-tools
bin_root=$tool_root/bin
log_dir=.lake/verification
mkdir -p "$log_dir"
python3 scripts/check-submission-modules.py >"$log_dir/module-resolution.log" 2>&1

for tool in comparator lean4export nanoda landrun; do
  if [ ! -x "$bin_root/$tool" ]; then
    echo "missing $bin_root/$tool; run scripts/bootstrap-palomar-tools.sh" >&2
    exit 1
  fi
done
bin_root=$(cd "$bin_root" && pwd)

# Tool revisions for the Lean v4.35.0-rc3 release verifier; they must match
# scripts/bootstrap-palomar-tools.sh.
expected_revisions='Comparator fd5d5bcf14177b187f66d4502071268d877887c3
ComparatorLean leanprover/lean4:v4.35.0-rc3
lean4export 66f1fb4bc256072069767fce52d39480e4524869
NanoDa 8de7e0c4ed3052745a7f8725164efd9e76d84c56
Landrun 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
Lean leanprover/lean4:v4.35.0-rc3'
actual_revisions=$(cat "$tool_root/revisions.txt")
if [ "$actual_revisions" != "$expected_revisions" ]; then
  echo "Palomar tool revision record does not match the release verifier" >&2
  exit 1
fi

python3 - <<'PY'
import json
from pathlib import Path

config = json.loads(Path("comparator.json").read_text(encoding="utf-8"))
expected = {
    "challenge_module": "GeneralizedStaffordChallenge",
    "solution_module": "GeneralizedStaffordSolution",
    "theorem_names": [
        "GeneralizedStaffordChallenge.fixedIdeal",
        "GeneralizedStaffordChallenge.fixedAnchor",
        "GeneralizedStaffordChallenge.corollaryB_dimension",
        "GeneralizedStaffordChallenge.corollaryB_fixedAnchor",
        "GeneralizedStaffordChallenge.corollaryB_fixedIdeal",
        "GeneralizedStaffordChallenge.corollaryC1",
        "GeneralizedStaffordChallenge.corollaryC1_hAll",
        "GeneralizedStaffordChallenge.corollaryC1_omega",
        "GeneralizedStaffordChallenge.corollaryC1_stable",
        "GeneralizedStaffordChallenge.corollaryC2_fullRank",
        "GeneralizedStaffordChallenge.corollaryC2_prescribed",
        "GeneralizedStaffordChallenge.corollaryC2",
        "GeneralizedStaffordChallenge.corollaryC3_lower",
        "GeneralizedStaffordChallenge.corollaryC3_upper"
    ],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "enable_nanoda": True,
}
if config != expected:
    raise SystemExit("comparator.json does not match the audited Palomar configuration")
print("Palomar configuration: exact theorem, three permitted axioms, NanoDa enabled")
PY

lake build GeneralizedStaffordChallenge >"$log_dir/challenge-build.log" 2>&1
lake build GeneralizedStaffordSolution >"$log_dir/solution-build.log" 2>&1
bash scripts/check-import-closure.sh GeneralizedStaffordChallenge
bash scripts/check-import-closure.sh GeneralizedStaffordSolution

PALOMAR_LANDRUN_BIN=$bin_root/landrun \
COMPARATOR_LANDRUN=$repo_root/scripts/landrun-wrapper.sh \
COMPARATOR_LEAN4EXPORT=$bin_root/lean4export \
COMPARATOR_NANODA=$bin_root/nanoda \
lake env "$bin_root/comparator" comparator.json \
  >"$log_dir/comparator.log" 2>&1

grep -Fq 'nanoda kernel accepts the solution' "$log_dir/comparator.log"
grep -Fq 'Lean default kernel accepts the solution' "$log_dir/comparator.log"
grep -Fq 'Your solution is okay!' "$log_dir/comparator.log"

echo "Palomar Comparator, NanoDa, and Lean kernel verification passed"
