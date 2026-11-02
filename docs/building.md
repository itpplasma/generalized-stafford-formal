# Building

## Pins

| Component | Revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0-rc3` |
| Mathlib | `c55e6e786f49471c72fbddbec5415808896aec1e` |
| [AlgebraicAnalysis](https://github.com/itpplasma/algebraic-analysis) | `2b3c67660777fd635b433507b3faa55ff0418878` |

`lean-toolchain` sets Lean. `lakefile.toml` sets the two dependencies, and
`lake-manifest.json` resolves them. `dependency-pins.json` is the reviewed
record that `scripts/check-pins.py` compares against all three files. It also
checks that AlgebraicAnalysis shares the single Mathlib package. Lake fetches
the dependencies into `.lake/packages/`. Do not run `lake update`.

## Build and verify

Requires [elan](https://github.com/leanprover/elan) and Python 3.11 or later
(set `PYTHON` if `python3` is older).

```sh
lake exe cache get
lake build                 # GeneralizedStafford, GeneralizedStaffordSolution
scripts/verify.sh
```

`scripts/verify.sh` checks the pins, builds the library and the solution, and
runs `#print axioms` with `--trust=0` on every name in
[endpoints.txt](endpoints.txt). It fails if an endpoint report is missing or an
axiom other than `propext`, `Classical.choice` and `Quot.sound` appears. Logs
go to `.lake/verification/`.

A single file is checked with `lake env lean <file>`. `tests/SolutionOracle.lean`
imports the solution alone and prints the axioms of each compared theorem.

## Palomar comparison

```sh
scripts/bootstrap-palomar-tools.sh   # once; builds the tools under .lake/palomar-tools
scripts/verify-palomar.sh
```

The bootstrap script builds Comparator, lean4export, NanoDa and Landrun at the
revisions recorded in [verification.md](verification.md). `verify-palomar.sh`
checks those revisions and `comparator.json`, builds the challenge and the
solution, checks that the challenge imports only Mathlib and that the solution
does not import the challenge, and runs Comparator with NanoDa enabled and
Landrun as sandbox. It succeeds only if NanoDa and the Lean kernel accept the
solution.

## Making a change

Find the affected declarations by searching for the challenge names, make the
smallest change and rerun both verifiers. A changed challenge needs a new
statement-faithfulness audit. When a compared theorem is added, extend
`Solution.lean`, `GeneralizedStaffordSolution.lean`, `comparator.json`, the
expected list in `scripts/verify-palomar.sh`, `tests/SolutionOracle.lean` and
`docs/endpoints.txt` together.

Application-independent lemmas belong in AlgebraicAnalysis. Moving one there
requires an axiom-clean proof upstream, a pin bump here and a full rerun of
both verifiers.
