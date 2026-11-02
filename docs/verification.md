# Verification

Run `PYTHON=python3.14 ./scripts/verify.sh` with the pinned dependencies and
Python >=3.11. `PYTHON` defaults to `python3`. The verifier checks pins and
paper/Lean source identities, builds the library once, then runs declaration
ownership, statement and endpoint axiom audits with `--trust=0`. The current
project build directory comes first in `LEAN_PATH`.

Lean is pinned at v4.35.0-rc3 and Mathlib at
c55e6e786f49471c72fbddbec5415808896aec1e. AlgebraicAnalysis is pinned at
7295b18a6a6e48940bde139125a96d6a2426864d (the requested main revision).
The pin check verifies its matching toolchain and full dependency closure, including exactly one shared Mathlib
package. All transitive pins are checked.
The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`;
missing endpoint reports or any other axiom fail verification.

## Evidence

The formal-C-induction extension passed
`PYTHON=python3.14 scripts/verify.sh` on 21 October 2026, exit 0, for the
uncommitted working tree. The project build, declaration-owner and statement
audits passed; all 87 endpoint axiom audits ran with `--trust=0`, with exact
union `propext`, `Classical.choice`, `Quot.sound`. The map checks 21 cards,
113 references, 6 immutable paper inputs and 35 formal inputs. Logs are
ignored under `.lake/verify-formal-C-induction.log` and
`.lake/verification/{build,statement,paper-lean-map,axioms}.log`.
This run reuses unchanged dependency build evidence rather than cleaning
all dependency outputs. It verifies the second-call bridge, full finite
two-call induction and omega affine/S38/torsion-cyclicity endpoints for actual
module germs. Arbitrary categorical-test correspondence and independent
semantic/human review remain open. No commit, push or branch was created.

The formal-B-fixed-anchor intermediate package passed
`PYTHON=python3.14 scripts/verify.sh` on 21 October 2026, exit 0, for the
uncommitted working tree. Before verification,
`lake clean generalizedStafford algebraicAnalysis` removed both packages'
build outputs. The full 9003-job project build (using the unchanged Mathlib
cache), statement audit and declaration-owner audit passed. All 71 declarations
were audited with `--trust=0`; the axiom union is exactly `propext`,
`Classical.choice`, `Quot.sound`. The map checks 21 cards, 92 references,
6 immutable paper inputs and 32 formal inputs. Logs are ignored under
`.lake/verify-fixed-anchor.log` and `.lake/verification/{build,statement,paper-lean-map,axioms}.log`.
This verifies the finite-germ intermediate package and dimension-one
consequences. At that earlier checkpoint the positive-deviation induction and omega S1
remained open; the formal-C evidence above supersedes that scope. Neither
categorical-test correspondence nor semantic/human review is implied. No commit, push or branch creation was performed.

The projective-width worker extension passed
`PYTHON=python3.14 scripts/verify.sh` on 21 October 2026, exit 0, at base revision
dbcb8d48e4349d6bc4d6ea419d1b94c613226450 plus the uncommitted extension.
The full 2125-job library build, statement audit and declaration-owner audit
passed. All 50 declarations (19 original endpoints and all 31 new declarations)
were audited with `--trust=0`; the union of axioms is exactly `propext`,
`Classical.choice`, `Quot.sound`. The source map checks 20 cards, 71 references,
5 paper inputs and 28 formal inputs. Logs are ignored under
`.lake/verification/projective-full-verify.log`, `build.log`, `statement.log`,
`paper-lean-map.log` and `axioms.log`. These checks verify conditional Lean
statements, not independent semantic review, lower-bound optimality or a new
scalar S1 producer.

The renamed library passed a full native replay at
d6a0eaba9dbef273a324fed8e0018728f92296db. After adding the full affine-left
endpoint, the full verifier passed again for all 19 endpoints. The three-file
proof/endpoint patch has SHA256
b4029a8847903d3177b1d14e1e1bca2d90bc82bcf298380c5a2f1f57924ff1b6.
The protected source fingerprints in [the map](paper-lean-map.json) identify
those exact proof inputs without a self-referential commit hash.

The map-only additions passed their static checks, rejected a synthetic
source mismatch and passed a generated Lean declaration-owner audit for all
40 mapped references. The full build was reused for those unchanged proof
sources. Logs and source-identity evidence remain under ignored
`.lake/verification/`.

The constructive-Weyl dossier update is pinned at
4c06c0bab51644daec6e6b881123319f3ac67d0b. Its refreshed map passes all
source and anchor checks. The generated owner audit is byte-identical to
the previous one and also passes `lean --trust=0`. No protected Lean or
dependency input changed, so the full proof build above is reused.
The new categorical and constructive results remain explicit omissions.

## Correspondence checks

The default map check reads immutable Git objects from the private research
checkout, by default `../generalized-stafford`. Set `PAPER_REPO` or pass
`--paper-root` to select another checkout containing the pinned commit.

```sh
python3.14 scripts/check-paper-lean-map.py
```

The checker verifies hashes, paper anchors, protected Lean coverage, map
references, dependency acyclicity and endpoint coverage. With `--lean-audit`
it emits a Lean file checking declaration existence and owning module; the
normal verifier runs that audit after building. It never refreshes the map
automatically. Changed protected sources require an explicit correspondence
review and map update.

`--formal-only` explicitly skips private paper Git-object/hash/anchor checks
and reports that limit; it is a checker option, not the full verifier's
default. Source identity and module ownership cannot prove that informal and
formal statements have the same meaning. The map records that mathematical
review separately, including partial statements and unformalized extensions.

No concrete geometric adapter, effective algorithm, literature originality,
human review or Palomar registration follows from these checks. Native
validation is local; this private repository has no heavy Actions workflow.

## Palomar comparator run, 2026-11-02

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
scripts/bootstrap-palomar-tools.sh   # CARGO_BUILD_JOBS=2; built the four tools under .lake/palomar-tools
scripts/verify-palomar.sh
```

Outcome: both commands exited 0. `verify-palomar.sh` built `GeneralizedStaffordChallenge`
and `GeneralizedStaffordSolution`, passed both import-closure checks, and printed
`nanoda kernel accepts the solution`, `Lean default kernel accepts the solution`
and `Your solution is okay!`. Its log is `.lake/verification/comparator.log`
(untracked).

Landrun ran in this container with `--best-effort`, which the Comparator
always passes. The kernel offers Landlock ABI v7, below the v9 that Landrun
asks for, so Landrun enforces filesystem restrictions only: a probe showed
unlisted paths unreadable and unwritable, while the rules that need the newer
ABI (the V9 profile's network and scope rules) are not applied. A strict run without `--best-effort` fails at sandbox setup.
A second Comparator run through a logging shim confirmed that the sandboxed
steps (lake builds and `lean4export`) went through `scripts/landrun-wrapper.sh`.
No unsandboxed diagnostic run of Comparator was needed.

Palomar's About page says records verified with a Lean toolchain's own
`lake comparator` cite the toolchain commit and bundled-tool digests, and
only earlier records cite standalone Comparator, lean4export and Landrun
revisions. This run used the standalone tools. The toolchain's `lake comparator`
was tried once as a diagnostic and stopped at `bwrap` not being installed; it
was not installed here. The Palomar pages do not state a required tool version.
The registry entry pages are JavaScript-rendered, so no registered-entry
check was made here.

The pins above describe the Lean v4.35.0-rc3 tool set only. The consumed
mathematics pins and the release record in this file above are unchanged.
