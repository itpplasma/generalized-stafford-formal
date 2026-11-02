# Verification

This file records how the formalization is checked and what each check
establishes. [PLAN.md](../PLAN.md) holds the current gate states.

## Gates

| Gate | Command or record | What it establishes |
| --- | --- | --- |
| Pins | `scripts/check-pins.py` (run by `scripts/verify.sh`) | `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` match `dependency-pins.json`; one shared Mathlib package. |
| Build | `lake build` | The library and the solution compile at the pins. |
| Axiom audit | `scripts/verify.sh` | Every name in [endpoints.txt](endpoints.txt) exists and depends only on `propext`, `Classical.choice` and `Quot.sound`, checked with `--trust=0`. |
| Palomar comparator | `scripts/verify-palomar.sh` | The solution proves each theorem of `comparator.json` with the challenge's exact name and type; the challenge imports only Mathlib; the solution does not import the challenge; NanoDa and the Lean kernel accept the solution. |
| Statement faithfulness | independent audit `review1`, summarized in [paper-lean-specification.md](paper-lean-specification.md) | The challenge statements say what the paper says. |
| Human review | none yet | Required before any claim of human verification. |

Machine checks establish that the Lean proofs are correct for the Lean
statements. Whether those statements match the paper is the separate
statement-faithfulness question. Neither check is human review, and none of
them is publication.

## Release verification record

Status: TO BE FILLED BY THE CONTROLLER (commit, date, outcome of `scripts/verify.sh` and `scripts/verify-palomar.sh` for the 14 compared theorems).

## Palomar comparator run, 2 November 2026

This run covered the 12 compared theorems solved at that time (C.3 was not
yet in `comparator.json`). It establishes the tool set and the sandbox facts
below; the release record above supersedes its theorem list.

Tool revisions (`scripts/bootstrap-palomar-tools.sh`, checked by
`scripts/verify-palomar.sh`), all for Lean `leanprover/lean4:v4.35.0-rc3`:

| Tool | Exact revision |
| --- | --- |
| Comparator | `fd5d5bcf14177b187f66d4502071268d877887c3` (tag `v4.35.0-rc3`; its `lean-toolchain` is v4.35.0-rc3) |
| lean4export | `66f1fb4bc256072069767fce52d39480e4524869` (tag `v4.35.0-rc3`; the revision Comparator's manifest pins) |
| NanoDa | `8de7e0c4ed3052745a7f8725164efd9e76d84c56` (head of the default branch on 2026-11-02; no toolchain pin upstream) |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (on `main`; no Lean dependency) |

Commands, from the repository root with `~/.elan/bin` on `PATH`:

```sh
scripts/bootstrap-palomar-tools.sh   # CARGO_BUILD_JOBS=2
scripts/verify-palomar.sh
```

Outcome: both commands exited 0. `verify-palomar.sh` built
`GeneralizedStaffordChallenge` and `GeneralizedStaffordSolution`, passed both
import-closure checks, and printed `nanoda kernel accepts the solution`,
`Lean default kernel accepts the solution` and `Your solution is okay!`. The
log is `.lake/verification/comparator.log` (untracked).

Sandbox. Landrun ran with `--best-effort`, which Comparator always passes. The
kernel offered Landlock ABI v7, below the v9 that Landrun requests, so Landrun
enforced filesystem restrictions only: a probe showed unlisted paths
unreadable and unwritable, while the network and scope rules of the V9
profile were not applied. A strict run without `--best-effort` fails at
sandbox setup. A second run through a logging shim confirmed that the
sandboxed steps (lake builds and `lean4export`) went through
`scripts/landrun-wrapper.sh`. No unsandboxed diagnostic run was needed.

Tool path. Palomar's About page says that records verified with a Lean
toolchain's own `lake comparator` cite the toolchain commit and bundled-tool
digests, and that only earlier records cite standalone Comparator,
lean4export and Landrun revisions. This run used the standalone tools. The
toolchain's `lake comparator` was tried once and stopped because `bwrap` is
not installed; it was not installed. The Palomar pages state no required tool
version. The registry entry pages are rendered by JavaScript, so no
registered entry was inspected.

## Earlier records

Verification records of the pre-Palomar development (87 and 170 endpoint
audits, the paper/Lean map checker, the projective-width extension) apply to
the tree on branch `archive/pre-palomar-2026-11-02` only.
