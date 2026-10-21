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

The full library replay and all 19 endpoint axiom audits passed. A pinned
paper-to-Lean map checks source identity and declaration ownership. Broader
written central-finite, weighted-localization and crossed-product theorems,
categorical localization, the finite-integer GR-Krull candidate, concrete
geometric adapters and constructive Weyl algorithms and bounds remain outside the
current formal scope. Human review and release are still open.

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
