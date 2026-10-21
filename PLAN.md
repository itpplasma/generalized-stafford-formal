# Generalized Stafford formal: live formal state

Updated: 21 October 2026. Private repository; work on `main`.

The [research PLAN](https://github.com/itpplasma/generalized-stafford/blob/main/PLAN.md)
owns mathematical status. This file owns formal implementation and executable
verification. The research dossier now has a complete commutative-symbol
proof, independently audited by agents, and stronger written extensions.
Human review and literature attribution remain separate obligations.

## Verified scope

The library proves the affine identity for simple algebras over infinite
central fields with exhaustive unital nonnegative multiplicative filtrations
and actual commutative Noetherian domain symbols of finite Krull dimension.
It assumes neither connectedness nor finite-dimensional filtration pieces.
The symbol interface specifies surjectivity, exact kernels and multiplication;
it does not substitute an unrelated graded ring for the associated graded.

Both affine orientations are exported. `targetA_left_affine` gives
`1=R*d+S*d*(B+a*H)`; the older `targetA_left` remains available.
Generation, rank and cancellation consequences are also included.

The conditional projective-width extension is VERIFIED by native build and
axiom audit: over a bilateral Ore domain with scalar S1, a finite projective
of Ore rank `n` and an endomorphism of localized image rank `r>0` admit the
full affine anchored identity with `floor(n/r)+1` terms. This includes the
matrix statement and rank two in `M_3(A)`. Scalar S1 remains a HYPOTHESIS of
this extension; no new producer is asserted. The worker implementation has
not received independent semantic or human review.

| Gate | State | Evidence or remaining obligation |
| --- | --- | --- |
| Import and dependency identity | CHECKED | Import fingerprints, upstream attribution, Lean/Mathlib pins retained; AlgebraicAnalysis pinned at 7295b18a6a6e48940bde139125a96d6a2426864d with one shared Mathlib package. |
| Renamed library replay | PASSED | Full native replay at d6a0eaba9dbef273a324fed8e0018728f92296db; affine-left source patch replay also passed. |
| Endpoint axiom closure | PASSED | Cleaned project and AlgebraicAnalysis outputs, full project rebuild and all 71 declaration audits PASSED; only propext, Classical.choice and Quot.sound, with --trust=0. |
| Actual-symbol statement interface | REVIEWED | Ten fields mapped explicitly to the written filtration; see paper-lean-map.json. |
| Written-to-Lean source map | CHECKED BASELINE | 21 correspondence cards, 92 declaration references and all 71 audit entries; immutable paper revision and 32 formal input fingerprints. The fixed-anchor card is explicitly partial; source/owner checks passed. |
| Conditional projective anchored width | VERIFIED (build/axioms) | `ProjectiveWidth.projective_anchored_width`, `matrix_anchored_width`, and `matrix_rank_two_three`; prescribed-tail generation, exact Ore quotient rank, common integral dual coordinates and projective reconstruction. Morita transfer, sharp lower bounds and marked-image equality criteria remain open. |
| Broader written theorems | NOT FORMALIZED | Weighted localizations, central-finite symbols, crossed products, division-coefficient coordinate adapters, categorical localization, the full positive-deviation fixed-anchor theorem, omega S1 and constructive Weyl results remain outside this library. Finite germ intermediates and dimension-one consequences are now implemented. |
| Concrete geometric adapters | OPEN | Written applications exist; concrete Lean specializations remain absent. |
| Independent human review | OPEN | Agent proof audits are not human review. |
| Palomar and publication | DEFERRED | No registration or release performed. |

The exact source map, source hashes and scope exceptions are in
[paper-lean-map.json](docs/paper-lean-map.json). This pins a comparison
baseline; it does not certify future research commits or infer semantic
correspondence from hashes. The written rank proofs sometimes use weaker
one-sided hypotheses than the current Lean statements, as recorded per card.

## Fixed-anchor integration: complete intermediate package

The generic central pencil declarations now come from the leaf module
`AlgebraicAnalysis.LinearAlgebra.DivisionPencil`; their downstream copies are
removed. The dependency uses the requested unmerged intrinsic-stafford-separation
head 7295b18a6a6e48940bde139125a96d6a2426864d. Repinning to upstream main after
that stack merges is a future integration action. Lean and Mathlib are unchanged.

`GeneralizedStafford.FixedAnchor` proves the mixed-anchor finite-deviation colon
bound, exact recursion data (`L=T*a*d`, `C=C₀*a*d`, `a'=a*d*T*a` and
`(H₂*a')*d=(H₂*a)*d*L`), finite affine epic germ-test selection, ordinary and
activated germ pencils, and one-stratum generation while carrying finite tests.
The source-selection statement derives finite Schur spaces and torsion sections
from critical filtrations and actual module deviation, with no hypothesis
assuming the desired affine source exists.

The strongest integral endpoint is `affine_of_devLE_zero_with_tests`: for a
simple right Noetherian domain with an infinite central field, an Artinian
principal quotient gives `1=d*U+(B+H*a)*d*V`, carrying finite epic germ tests.
`affine_of_devLE_one` supplies universal affine S1 when the right regular module
has deviation at most one; `s38_of_devLE_one` and
`torsion_cyclic_of_devLE_one` use the existing consequences. The written dossier
identifies finite-length S1 as prior. These are intermediate formal results,
not the requested positive-deviation fixed-anchor theorem.

**Exact next bridge:** put `I=dR+fdR`, `J=dR+fdK`, `W=R/J`,
`v=q_J(fd)`, `u=q_J(gd)`. Derive joint injectivity of
`h ↦ (h∘v,(h∘u)L)` on each retained critical Schur space of W from the
second-call epic test `q_I(gdL)`, using `fdL=dC`. Then assemble the uniform
two-call step from an affine/test producer bounded by `DevLE e` to one bounded
by `Small e`, using the checked colon bound and germ pencils, and iterate.
`principal_quotient_finite_of_omega` proves only the input reduction for the
omega corollary. Omega S1 and omega torsion cyclicity remain OPEN.
No correspondence with arbitrary categorical tests, independent semantic
review, human review or publication is asserted. The supplied worker handoff
and `formal-scope-BC.md` were absent when work began; the written fixed-anchor
proof and research PLAN supplied the available authority.

## Verification and next work

`PYTHON=python3.14 scripts/verify.sh` checks pins and source identities, builds
once, audits declaration owners and prints statement types and axiom closures.
For formal-B-fixed-anchor, `lake clean generalizedStafford algebraicAnalysis`
preceded the full 9003-job project build. `PYTHON=python3.14 scripts/verify.sh`
passed on 21 October 2026 for this uncommitted working tree, including all
71 axiom reports, statement types and 92 mapped declaration-owner references.
The exact axiom union is `propext`, `Classical.choice`, `Quot.sound`.
Logs are ignored under `.lake/verification/` and `.lake/verify-fixed-anchor.log`.
See [verification](docs/verification.md) for commands and evidence limits.

Maintain the reviewed written proof before formalizing a stronger producer.
The research dossier now contains written constructive Weyl algorithms and
quantitative comparisons. Their implementation and formalization remain open,
as do the broader constructive producer and classical-source comparison.
No private-repository heavy GitHub Actions workflow is configured.
