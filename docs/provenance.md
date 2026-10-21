# Provenance

The initial experimental proof was extracted from the Mathlib-only Paper development in
[Symplectic Stafford formal](https://github.com/itpplasma/symplectic-stafford-formal)
at 0e55a8059cc923ef39d6ddb66c5b6f6a2682b46b. The predecessor mathematical source
is [Symplectic Stafford](https://github.com/itpplasma/symplectic-stafford), with
the local generalization recorded at 55308889e51b50a0487cd73107371bfc71cf2246.

The pre-migration experiment removed `zero_piece` and `finiteDimensional` from
the filtration structure, replacing them with `one_mem_zero`. It repaired
terminal extraction by degree-zero injectivity and transported the weaker
structure to the opposite algebra. The localization, source-selection and
two-call induction arguments required no other mathematical change.

The initial import renames `SymplecticStafford.Paper` to `GeneralizedStafford`,
flattens the Paper directory, and adds a universal endpoint. Imported files
carry modification notices; `LICENSE` and `NOTICE` preserve the upstream license
and attribution. Section numbers retained in source comments refer to the
original manuscript, not a separate finalized paper in this repository.

[source-import.json](source-import.json) fingerprints each pre-migration source
and its initial renamed form. These are import provenance, not a rule forbidding
subsequent reviewed changes.

The predecessor replay archive had SHA-256
b394d0aa6f6a59849db7effbd00aed66aac1a2081092c61246f3bcff18695fd8;
the three-file patch had SHA-256
4be9f69433c6841b07b6ce4fc41c95a6205ad8070d1a611525ca0da712b9139d.
The renamed tree passed its own full native replay, including a subsequent
full replay of the added affine-left endpoint. The 19 endpoint audits use only
the three standard Lean axioms. The new source map records exact protected
file identities separately from the import fingerprints.

The written authority is
[Generalized Stafford](https://github.com/itpplasma/generalized-stafford).
Its commutative-symbol proof and applications have complete written arguments
and agent audits. Its stronger central-finite, weighted-localization and
crossed-product results are not present in this Lean library. Source-map
identity, semantic review, human review and novelty remain distinct. No
generated cache, host-specific link or prior release metadata is required by
a fresh clone.

Generic central-pencil declarations have been removed from the downstream
`GeneralizedStafford/DivisionPencil.lean` and are now imported from
`AlgebraicAnalysis.LinearAlgebra.DivisionPencil` in
[AlgebraicAnalysis](https://github.com/itpplasma/algebraic-analysis), pinned at
7295b18a6a6e48940bde139125a96d6a2426864d. Its header records the extraction,
original authorship and earlier provenance. The historical initial-import
fingerprints above remain unchanged; current source identity is recorded by
the dependency pin and paper/Lean map. No upstream LICENSE or NOTICE was changed.
