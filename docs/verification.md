# Verification

How the formalization is checked and what each check establishes.

| Check | Command | What it establishes |
| --- | --- | --- |
| Pins | `scripts/check-pins.py` (run by `scripts/verify.sh`) | `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` match `dependency-pins.json`; one shared Mathlib package. |
| Build | `lake build` | The library and the solution compile at the pins. |
| Axiom check | `scripts/verify.sh` | Every name in [endpoints.txt](endpoints.txt) exists and depends only on `propext`, `Classical.choice` and `Quot.sound`, checked with `--trust=0`. |
| Palomar check (local replay) | `scripts/verify-palomar.sh` | The challenge and solution copies are byte-identical, the challenge has exactly 41 `sorry` holes; the solution proves each theorem of `comparator.json` with the challenge's exact name and type; the challenge imports only Mathlib; the solution does not import the challenge; NanoDa and the Lean kernel accept the solution. |

These checks establish that the Lean proofs are correct for the Lean
statements. Whether the statements match the intended mathematics is a
separate question.

Commands, from the repository root with `~/.elan/bin` on `PATH`:

```sh
PYTHON=python3 scripts/verify.sh
scripts/bootstrap-palomar-tools.sh   # once
scripts/verify-palomar.sh
```

Tool revisions built by `scripts/bootstrap-palomar-tools.sh` and checked by
`scripts/verify-palomar.sh`, all for Lean `leanprover/lean4:v4.35.0-rc3`:

| Tool | Exact revision |
| --- | --- |
| Comparator | `fd5d5bcf14177b187f66d4502071268d877887c3` (tag `v4.35.0-rc3`; its `lean-toolchain` is v4.35.0-rc3) |
| lean4export | `66f1fb4bc256072069767fce52d39480e4524869` (tag `v4.35.0-rc3`; the revision Comparator's manifest pins) |
| NanoDa | `8de7e0c4ed3052745a7f8725164efd9e76d84c56` (head of the default branch on 2026-11-02; no toolchain pin upstream) |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (on `main`; no Lean dependency) |
