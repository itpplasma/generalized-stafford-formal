# Generalized Stafford formal

Private Lean counterpart of the
[Generalized Stafford research dossier](https://github.com/itpplasma/generalized-stafford).
This repository preserves the experimental Mathlib-only filtered-algebra
proof after namespace migration; it is not a completed release.

The imported target is

```text
1 = d R + (B + H a) d S,     d != 0, a != 0.
```

The data intend an exhaustive unital nonnegative multiplicative filtration,
with commutative Noetherian domain associated graded of finite Krull dimension,
over an infinite field. Connectedness and finite-dimensional filtration pieces
are absent. The written generalization and concrete applications remain open
research obligations; see the research dossier's PLAN and this [PLAN](PLAN.md).

- [Candidate declaration map](docs/proof-map.md)
- [Verification procedure and evidence limits](docs/verification.md)
- [Import provenance](docs/provenance.md)
- [Universal endpoint](GeneralizedStafford/Main.lean)
- [Concrete data interface](GeneralizedStafford/Setting.lean)

With the pinned Lean toolchain and Python >=3.11 installed:

```sh
lake exe cache get
PYTHON=python3.14 ./scripts/verify.sh
```

`PYTHON` defaults to `python3`; choose any installed interpreter >=3.11.
The verifier performs a full build, prints actual statement/data types, and
checks the listed endpoint axiom closures. Its fresh replay is pending.
There is no private-repository GitHub Actions build workflow.

Apache-2.0; inherited attribution is in [NOTICE](NOTICE).
