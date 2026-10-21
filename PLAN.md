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
| Import and dependency identity | CHECKED | Import fingerprints, upstream attribution, exact toolchain and dependency pins retained. |
| Renamed library replay | PASSED | Full native replay at d6a0eaba9dbef273a324fed8e0018728f92296db; affine-left source patch replay also passed. |
| Endpoint axiom closure | PASSED | The original 19 endpoints and all 31 new projective-width declarations pass with only propext, Classical.choice and Quot.sound; audits use --trust=0. |
| Actual-symbol statement interface | REVIEWED | Ten fields mapped explicitly to the written filtration; see paper-lean-map.json. |
| Written-to-Lean source map | CHECKED BASELINE | 20 correspondence cards, 71 declaration references and all 50 audited declarations; immutable paper revision and 28 formal input fingerprints. Owner audit passes; semantic review of the new card remains separate. |
| Conditional projective anchored width | VERIFIED (build/axioms) | `ProjectiveWidth.projective_anchored_width`, `matrix_anchored_width`, and `matrix_rank_two_three`; prescribed-tail generation, exact Ore quotient rank, common integral dual coordinates and projective reconstruction. Morita transfer, sharp lower bounds and marked-image equality criteria remain open. |
| Broader written theorems | NOT FORMALIZED | Weighted localizations, central-finite symbols, crossed products, division-coefficient coordinate adapters, categorical localization, the finite-integer GR-Krull candidate and constructive Weyl results are outside this library. |
| Concrete geometric adapters | OPEN | Written applications exist; concrete Lean specializations remain absent. |
| Independent human review | OPEN | Agent proof audits are not human review. |
| Palomar and publication | DEFERRED | No registration or release performed. |

The exact source map, source hashes and scope exceptions are in
[paper-lean-map.json](docs/paper-lean-map.json). This pins a comparison
baseline; it does not certify future research commits or infer semantic
correspondence from hashes. The written rank proofs sometimes use weaker
one-sided hypotheses than the current Lean statements, as recorded per card.

## Verification and next work

`PYTHON=python3.14 scripts/verify.sh` checks pins and source identities, builds
once, audits declaration owners and prints statement types and axiom closures.
The full proof replay preceded the map-only additions; their static check and
generated Lean owner audit were run separately on the same proof sources.
See [verification](docs/verification.md) for commands and evidence limits.

Maintain the reviewed written proof before formalizing a stronger producer.
The research dossier now contains written constructive Weyl algorithms and
quantitative comparisons. Their implementation and formalization remain open,
as do the broader constructive producer and classical-source comparison.
No private-repository heavy GitHub Actions workflow is configured.
