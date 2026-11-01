# Written proof and Lean correspondence

The machine-readable [paper-lean-map.json](paper-lean-map.json) records 21
correspondence cards for the commutative-symbol proof and consequences,
113 declaration references and all 87 audit entries (19 original
endpoints, 31 projective-width additions and 37 fixed-anchor declarations). It pins an immutable
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
extensions, arbitrary categorical localization, and constructive Weyl algorithms
and bounds are not formalized here. The finite-deviation and omega scalar
fixed-anchor endpoints are implemented using actual module germs.
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

The [second-call bridge](../GeneralizedStafford/FixedAnchor/SecondCall.lean)
now proves epicity of `(fd,gdL)` modulo `J` from the canonical epic test
`q_I(gdL)`, then derives joint injectivity on every retained critical Schur
space by cancellation. The relation `fdL=dC` proves `vL=0`.
The [descent](../GeneralizedStafford/FixedAnchor/Descent.lean) combines this
activated pencil with the colon bound, ordinary pencils for old tests and
choice outside a finite central-scalar exception set. `affineBound_step`
lowers `DevLE e` to `Small e` uniformly, preserving the original anchor and
using the exact ordered recursive products of §3.

The [finite induction](../GeneralizedStafford/FixedAnchor/Induction.lean)
iterates `N+1` times to level zero and extracts actual right coefficients.
`affine_of_finite_deviation` gives `1=d*U+(B+H*a)*d*V` under a finite bound on
`R/dR`; its `_with_tests` version carries finite actual epic germ tests.
`affine_of_devLE_omega`, `s38_of_devLE_omega` and
`torsion_cyclic_of_devLE_omega` use the upstream principal-quotient reduction
and existing generation consequences.

The card remains partial because no correspondence with arbitrary categorical
tests or whole-proof correspondence is asserted. Independent semantic and
human reviews remain open. Generic division and activated pencils are
imported from pinned AlgebraicAnalysis leaf modules.

## Core Theorem A' (fixed ideal), domain case

Two partial cards map `docs/core-theorem.md` at research revision
`522b9658fabfc257cbc76599146eb4790df5c360` (its paper record pins that commit
individually; the other records keep the map-wide revision). The
[fixed-ideal module](../GeneralizedStafford/FixedAnchor/FixedIdeal.lean)
proves, for a simple right Noetherian **domain** with an infinite central field:

- `fixed_ideal`: if the right ideal `I` contains a nonzero element and
  `Module.DevLE Rᵐᵒᵖ N (R ⧸ I)`, then for every `x` and `t ≠ 0` there is `H`
  with `I ⊔ principalRightIdeal (x + H*t) = ⊤` (Theorem A'); the `_with_tests`
  form also satisfies any finite family of actual epic germ tests.
- `fixed_anchor_of_fixed_ideal`: Theorem A, `1 = d*U + (B+H*a)*d*V`, obtained
  from A' with `I = dR`, `x = B*d`, `t = a*d` exactly as in §1.
- `quotient_finite_of_omega`, `fixed_ideal_of_devLE_omega`: Corollary B.
- `prescribed_cyclic` (+ `_of_principal`, `_of_devLE_omega`): Corollary C.1.
- `two_generated_of_principal` (+ `_of_devLE_omega`) and
  `exists_two_generators_of_principal`: Corollary C.2, with `a ≠ 0` in place of
  `aQ = IQ`.

The descent `idealBound_step` is the colon-free two-call step of §4: the second
call needs only a nonzero `b` with `f*b ∈ I`; the stability pencil of Lemma 3.6
replaces the older activated pencil and colon bound. Source selection (Lemma
3.6) is the existing actual-germ theorem `exists_affine_epic_tests`.

Statement differences: only domains (regular = nonzero); tests are actual module
germs rather than arbitrary objects of `C_e`; torsion is `IsTorsionRight`
(nonzero denominators); C.2 assumes `a ≠ 0`. The zero-divisor case, C.3 and
Remark 6.5 are not formalized. Build/axiom evidence only; semantic and human
review remain open.
