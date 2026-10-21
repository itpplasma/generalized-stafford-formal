# Verification

Run `PYTHON=python3.14 ./scripts/verify.sh` from a checkout with the pinned
dependencies available. Python >=3.11 is required; `PYTHON` defaults to
`python3` and can select any installed compatible interpreter.
It checks the exact Lean/Mathlib pins and Mathlib's transitive lock, builds the
whole `GeneralizedStafford` library, prints the actual data and statement types,
and audits every declaration in [endpoints.txt](endpoints.txt).

The allowed logical axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Missing or malformed endpoint reports and any other axiom fail verification.
The statement and axiom audits run with `--trust=0` and the current project's
build directory first in `LEAN_PATH`. Logs are written under
`.lake/verification/` and remain untracked.

The migration replay uses Lean v4.35.0-rc3 and Mathlib
c55e6e786f49471c72fbddbec5415808896aec1e. The predecessor experiment already
passed a complete rebuild and axiom audit; this repository requires its own
replay after namespace and package changes.

A successful run would establish the imported declarations and their axiom
closures at this revision. The fresh renamed-tree replay remains pending.
The infrastructure-only setup checked shell/Python syntax, interpreter
selection, dependency pins and axiom-parser behavior without a full Lean build.
These checks do not establish informal-to-formal semantic correspondence,
construct a geometric adapter, establish literature originality, or constitute
a Palomar registration.
This private repository has no GitHub Actions build workflow; native validation
runs locally.
