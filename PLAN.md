# Generalized Stafford formal: live formal state

Updated: 21 October 2026. Private repository; work on `main`.

## Authority and scope

The mathematical research authority is
[Generalized Stafford PLAN](https://github.com/itpplasma/generalized-stafford/blob/main/PLAN.md).
That repository owns the written proof and dependency tree. This PLAN owns
formal implementation and executable verification status only.

The imported experiment weakens the Symplectic filtration fields to
`one_mem_zero`, with no connectedness or finite-dimensional-piece fields.
The original modules and exact pins are preserved. No new mathematical or
Lean proof development is part of this infrastructure setup.

## Evidence and gates

| Gate | State | Evidence or obligation |
| --- | --- | --- |
| Source preservation and attribution | CHECKED | Import fingerprints agree; LICENSE, NOTICE and provenance retained. |
| Dependency configuration | CHECKED | Exact Lean/Mathlib and transitive manifest pins checked locally. |
| Predecessor isolated experiment | REPORTED PASS | Earlier full build and endpoint axiom audit; distinct namespace/checkout. |
| Renamed library replay | PENDING | Run scripts/verify.sh; no full Lean build in this infrastructure task. |
| Informal statement versus data interface | OPEN | Audit actual filtration/grading assumptions and quantified conclusion. |
| Written-proof correspondence | OPEN | Complete research dossier, review its dependency bridges, then pin and map each claim. |
| Concrete applications | OPEN | Weyl/Symplectic comparison and global differential-operator/Laurent–Euler structural adapters. |
| Publication or registry | DEFERRED | Separate decisions after the mathematical and formal gates. |

The initial verifier failed before compilation because default Python 3.9 lacks
`tomllib`. Infrastructure now checks Python >=3.11 and accepts `PYTHON`; this
repair is not a successful Lean replay. The declaration map is provisional.

## Next action

Complete the written abstract proof and application audit in the research
repository before further Lean development. A bounded replay of this unchanged
import may subsequently establish its migrated build status; it cannot close
semantic, literature or human-review gates by itself.
