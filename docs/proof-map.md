# Written proof and Lean correspondence

The machine-readable [paper-lean-map.json](paper-lean-map.json) records 21
correspondence cards for the commutative-symbol proof and consequences,
92 declaration references and all 71 audit entries (19 original
endpoints, 31 projective-width additions and 21 fixed-anchor intermediates). It pins an immutable
[research dossier](https://github.com/itpplasma/generalized-stafford) commit
and fingerprints all proof sources, dependency pins and audit inputs.

Each card separates statement equivalence from proof-route correspondence.
The actual-symbol card maps all ten fields, including exact kernels,
surjectivity and multiplication. Rank cards identify weaker right-Ore written
hypotheses where Lean retains bilateral ones. Source identity and declaration
ownership pass executable checks; semantic correspondence rests on the
recorded mathematical comparison, not hashes alone.

| Mathematical step | Lean declaration | Source |
| --- | --- | --- |
| Unital filtration and exact associated graded symbols | `FilteredAlgebraData` | [Setting](../GeneralizedStafford/Setting.lean) |
| Leading-term lifting and Artin–Rees | `FilteredAlgebraData.artinRees` | [Setting](../GeneralizedStafford/Setting.lean) |
| Full-symbol Ore localization | `FilteredAlgebraData.ore_condition`, `isRightFractions` | [Localization](../GeneralizedStafford/Localization.lean) |
| Survival and finite length at support components | `FilteredAlgebraData.survival`, `finiteLength` | [Localization](../GeneralizedStafford/Localization.lean) |
| Simultaneous affine source selection | `Test.exists_source` | [SourceSelection](../GeneralizedStafford/SourceSelection.lean) |
| Common-colon support union | `FilteredAlgebraData.support_union` | [Induction](../GeneralizedStafford/Induction.lean) |
| Two-call dimension descent | `FilteredAlgebraData.Ph_all` | [Induction](../GeneralizedStafford/Induction.lean) |
| Degree-zero extraction and affine identity | `FilteredAlgebraData.one_mem_of_grIdeal_eq_top`, `targetA` | [Induction](../GeneralizedStafford/Induction.lean) |
| Opposite-handed identity | `FilteredAlgebraData.targetA_left_affine` (full affine), `targetA_left` (legacy) | [Opposite](../GeneralizedStafford/Opposite.lean) |
| Same-divisor, generation and cancellation consequences | `FilteredAlgebraData.s38`, `torsion_cyclic`, `stable_range`, `stably_free`, `cancellation` | [ConsequencesForU](../GeneralizedStafford/ConsequencesForU.lean) |
| Universal exported statement | `universalStatement` | [Main](../GeneralizedStafford/Main.lean) |


All declarations are in `GeneralizedStafford`. The new full affine-left
endpoint closes the earlier mismatch between a full written left identity
and the older same-divisor-only wrapper. The ten-field interface and exact
statement are also printed by the statement audit.

The broader weighted-localization theorem, central-finite symbols, crossed
products, coordinate and geometric adapters, projective transport, finite-top
extensions, categorical localization, the full positive-deviation fixed-anchor theorem, omega S1
and constructive Weyl algorithms and bounds are not formalized here.
The source map records these omissions explicitly. Human review and full
programme completion remain open in the two repositories' PLAN files.

The new conditional projective-width card covers §§1–2 of
`docs/projective-anchored-width.md` at research revision
a7591a668fdc90f1422e2a4cd9754082c44d6b60. The previous four mapped mathematical
sources retain their statements; the only change in `docs/proof.md` since the
previous pin consists of literature-attribution paragraphs. This extension
reuses `S38`, `two_torsion_eq_span_singleton` and finite torsion cyclicity.
`ProjectiveWidth.prescribed_generators` proves generation with prescribed
offsets and a nonzero right tail. `projective_anchored_width` then proves
`floor(n/r)+1` terms for every finite projective of Ore rank `n` and localized
image rank `r>0`. The noncommutative matrix adapter gives
`matrix_anchored_width` and the two-term `matrix_rank_two_three`.

These claims are VERIFIED for build and axiom closure; scalar S1 and bilateral
Ore are HYPOTHESES. This worker card awaits independent semantic review and
does not establish whole-dossier correspondence. In particular, projective
transport above means integral Morita transfer, which remains outside this
extension, along with §§4–5's sharp lower bounds and marked-image criteria.

The partial fixed-anchor card maps §§2–3 of `docs/fixed-anchor-gluing.md` at
the same immutable research revision. The finite test lists consist of actual
module germs; critical filtrations supply their finite dual lists. The new
[reduction](../GeneralizedStafford/FixedAnchor/Reduction.lean),
[germ tests](../GeneralizedStafford/FixedAnchor/GermTests.lean),
[pencils](../GeneralizedStafford/FixedAnchor/Pencils.lean),
[top-stratum theorem](../GeneralizedStafford/FixedAnchor/FiniteTop.lean) and
[dimension-one consequences](../GeneralizedStafford/FixedAnchor/Corollaries.lean)
cover exact recursive products, colon deviation bounds, affine source selection,
ordinary/activated pencils, generation at one top stratum, the full affine
identity for deviation-zero principal quotients and S38/torsion cyclicity when
the ring has right deviation at most one. The central field is expressed by
`[Field k] [Infinite k] [Algebra k R]`; right Noetherianity is
`IsNoetherian Rᵐᵒᵖ R` and quotient bounds are `Module.DevLE`.

The next missing lemma connects the second-call epic test `q_I(gdL)` to joint
injectivity against the retained critical factors of `R/J`. The uniform
two-call bound-lowering induction, finite iteration and omega S1/cyclicity
are still absent. `principal_quotient_finite_of_omega` supplies only the
principal-quotient bound. This card establishes neither arbitrary categorical
test correspondence nor whole-proof correspondence; independent semantic
and human reviews remain open. Generic division pencils are imported from
the pinned AlgebraicAnalysis leaf module after removing the downstream copies.
