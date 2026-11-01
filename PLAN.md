# Generalized Stafford formal: live formal state

Updated: 1 November 2026 (verification record); otherwise 21 October 2026.
Private repository; work on `main`.

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
| Endpoint axiom closure | PASSED | Project build and all 87 declaration audits PASSED; unchanged dependency build evidence reused; only propext, Classical.choice and Quot.sound, with --trust=0. |
| Actual-symbol statement interface | REVIEWED | Ten fields mapped explicitly to the written filtration; see paper-lean-map.json. |
| Written-to-Lean source map | CHECKED BASELINE | 21 correspondence cards, 113 declaration references and all 87 audit entries; immutable paper revision and 35 formal input fingerprints. The fixed-anchor card is explicitly partial; source/owner checks passed. |
| Conditional projective anchored width | VERIFIED (build/axioms) | `ProjectiveWidth.projective_anchored_width`, `matrix_anchored_width`, and `matrix_rank_two_three`; prescribed-tail generation, exact Ore quotient rank, common integral dual coordinates and projective reconstruction. Morita transfer, sharp lower bounds and marked-image equality criteria remain open. |
| Broader written theorems | NOT FORMALIZED | Weighted localizations, central-finite symbols, crossed products, division-coefficient coordinate adapters, arbitrary categorical localization, concrete geometric adapters and constructive Weyl results remain outside this library. The full finite-deviation fixed-anchor and omega scalar endpoints are implemented for actual module germs. |
| Concrete geometric adapters | OPEN | Written applications exist; concrete Lean specializations remain absent. |
| Independent human review | OPEN | Agent proof audits are not human review. |
| Palomar and publication | DEFERRED | No registration or release performed. |

The exact source map, source hashes and scope exceptions are in
[paper-lean-map.json](docs/paper-lean-map.json). This pins a comparison
baseline; it does not certify future research commits or infer semantic
correspondence from hashes. The written rank proofs sometimes use weaker
one-sided hypotheses than the current Lean statements, as recorded per card.

## Fixed-anchor integration: finite induction and omega endpoints

The dependency remains at the requested AlgebraicAnalysis main revision
7295b18a6a6e48940bde139125a96d6a2426864d, with unchanged Lean/Mathlib pins.
Generic division and activated pencils come from its leaf modules.

`GeneralizedStafford.FixedAnchor.SecondCall` proves that the second-call epic
test `q_I(gdL)` makes `(fd,gdL)` epic modulo `J`. Epic cancellation gives
joint injectivity on every retained critical Schur space; `fdL=dC` proves
`vL=0`. No splitting, lifted generator or source-selection conclusion is assumed.

`affineBound_step` in `FixedAnchor/Descent.lean`
lowers the uniform bound from `DevLE e` to `Small e`, carrying every finite
family of actual bounded Noetherian torsion epic germ tests. Both recursive
calls keep `d` fixed, using `L=T*a*d`, `C=C₀*a*d`, `a'=a*d*T*a`,
`F₂=H₂*a'`, `g=H₂*a` and `F₂*d=g*d*L`. The checked colon bound controls
`R/J`. Activated pencils kill its top stratum, ordinary pencils preserve old
tests, and infinitude of the central field supplies a scalar outside their
finite exceptional union. The update is `B+(H+lambda*H₂)*a`.

`affineBound_descend` iterates exactly `N+1` times from `Small (N+1)` to
`Small 0`. `affine_of_finite_deviation_with_tests` extracts integral `U,V`.
The plain endpoint `affine_of_finite_deviation` proves, for a simple right
Noetherian domain with an infinite central field, `d,a!=0` and a finite
`Module.DevLE` bound on `R/dR`, for every `B`:

    ∃ H U V, 1 = d*U + (B+H*a)*d*V.

`affine_of_devLE_omega` uses AlgebraicAnalysis's `Module.DevLEOmega` principal
quotient reduction. `s38_of_devLE_omega` and `torsion_cyclic_of_devLE_omega`
then reuse the existing consequences. The earlier deviation-zero and
ring-deviation-one endpoints remain available.

This is native build/axiom evidence for actual module germs. Correspondence
with arbitrary categorical tests, independent semantic review, human review,
applications and publication remain separate obligations. The supplied
formal-C handoff was absent on entry; the full formal-B handoff, existing
files and written fixed-anchor §3 supplied the authority.

## Verification and next work

**1 November 2026 fresh verification of the committed head.** Commit
`5c92c4d014bbe4148e024e345ef73b5fc60767c5` (which adds `FixedAnchor/SecondCall`
after the 21 October working-tree run) passed `scripts/verify.sh` in a clean
cloud container: `lake exe cache get`, a full `lake build` (9006 jobs), pins,
the paper/Lean map (21 items, 113 references, paper revision
`a7591a668fdc90f1422e2a4cd9754082c44d6b60`), the statement audit and all 87
endpoint axiom reports with exactly `propext`, `Classical.choice`, `Quot.sound`.
Only deprecation and unused-variable linter warnings were emitted. This is
build/axiom evidence only; semantic correspondence and human review remain open.

**Formalization gate.** New Lean waits for the research repository's gate
(its AGENTS.md): a finished, independently audited written proof at a frozen
commit, and necessity for the final stated theorem on a stable route. The
research dossier is currently consolidating a canonical core note and running
hypothesis-removal lanes that may replace descent lemmas, so no new theorem
development starts here yet.


`PYTHON=python3.14 scripts/verify.sh` checks pins and source identities, builds
once, audits declaration owners and prints statement types and axiom closures.
For formal-C-induction, `PYTHON=python3.14 scripts/verify.sh` passed on
21 October 2026 for the uncommitted working tree, including the project build,
87 endpoint axiom reports, statement types and 113 mapped declaration-owner
references. The axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`.
This run reuses unchanged dependency build evidence; it is not a new clean
rebuild of all dependencies. Logs are ignored under `.lake/verification/` and
`.lake/verify-formal-C-induction.log`. No commit, push or branch was created.
See [verification](docs/verification.md) for commands and evidence limits.

Maintain the reviewed written proof before formalizing a stronger producer.
The research dossier now contains written constructive Weyl algorithms and
quantitative comparisons. Their implementation and formalization remain open,
as do the broader constructive producer and classical-source comparison.
No private-repository heavy GitHub Actions workflow is configured.
