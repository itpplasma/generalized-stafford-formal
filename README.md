# Generalized Stafford formal

Private Lean counterpart of the
[Generalized Stafford research dossier](https://github.com/itpplasma/generalized-stafford).
The library proves

```text
1 = d R + (B + H a) d S,     d != 0, a != 0,
```

for simple algebras over infinite central fields with exhaustive unital
nonnegative multiplicative filtrations and commutative Noetherian domain
associated graded of finite Krull dimension. Connectedness and
finite-dimensional filtration pieces are absent. The full affine
left-handed identity and module consequences are included.

The conditional scalar-S1 extension also proves the affine anchored bound
`floor(n/r)+1` for finite projective right modules over bilateral Ore domains,
including rank two in `M_3(A)` and general matrices. Ranks use Mathlib's Ore
localization; scalar S1 remains an explicit hypothesis. See
[ProjectiveWidth](GeneralizedStafford/ProjectiveWidth/Theorem.lean).

The full library rebuild and all 71 declaration axiom audits passed (the
original 19 endpoints, 31 projective-width declarations and 21 fixed-anchor
intermediates). A pinned
paper-to-Lean map checks source identity and declaration ownership. Broader
written central-finite, weighted-localization and crossed-product theorems,
categorical localization, the finite-integer GR-Krull candidate, concrete
geometric adapters and constructive Weyl algorithms and bounds remain outside the
current formal scope. Independent semantic review of the projective-width
extension, human review and release are still open.

The intrinsic fixed-anchor intermediate package adds finite affine germ tests,
colon bounds, activated pencils and the affine identity for Artinian principal
quotients. It also proves S38 and torsion cyclicity when the ring has right
deviation at most one. Positive-deviation two-call assembly and omega S1 remain
open. This package uses pinned [AlgebraicAnalysis](https://github.com/itpplasma/algebraic-analysis)
leaf modules and one shared Mathlib dependency; see the formal PLAN for the pin
and verification status.

- [Current state](PLAN.md)
- [Correspondence and its scope](docs/proof-map.md)
- [Verification](docs/verification.md)
- [Provenance](docs/provenance.md)
- [Universal endpoint](GeneralizedStafford/Main.lean)
- [Actual-symbol data interface](GeneralizedStafford/Setting.lean)

With pinned dependencies and Python >=3.11:

```sh
lake exe cache get
PYTHON=python3.14 ./scripts/verify.sh
```

Source-map checks need the private paper checkout at its recorded commit,
by default at `../generalized-stafford`; set `PAPER_REPO` for another path.
There is no private-repository GitHub Actions build workflow.

Apache-2.0; inherited attribution is in [NOTICE](NOTICE).
