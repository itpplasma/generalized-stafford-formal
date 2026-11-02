# Paper and Lean specification

This document maps the written proof to the Lean declarations and records the
choices made when stating it in Lean. The [literature index](literature.md)
lists the classical sources and the modules that use them.

## Sources

- Research note `docs/core-theorem.md` of the private repository
  `itpplasma/generalized-stafford`, cited as "core". It is the canonical
  written proof, with independent agent proof-audits of Sections 0-8.
- `docs/lane-C3-rank-without-morita.md` of the same repository, cited as
  "lane-C3". It replaces the matrix-ring transfer in the upper bound of C.3 and
  is the frozen written source for the Lean proof of that bound.
- Manuscript `docs/manuscript/main.tex`, cited by `\label`. It proves
  Theorem A' by the two-call descent and Theorem A from A', and gives the
  corollary proofs in its Section 6, where the upper bound of C.3 uses a
  Morita (matrix-ring) transfer. The Lean proof of that bound follows the
  audited Morita-free note lane-C3 instead (research commit `251049f`). A
  shortened paper may cite the Lean proofs of the corollaries listed below.

Namespaces: `GeneralizedStafford` (library), `AlgebraicAnalysis` (pinned
dependency), `GeneralizedStaffordChallenge` (Palomar challenge and solution).
Lean paths are relative to this repository.

## Statements

Each challenge theorem `<name>` is proved as `<name>_proof` in
`GeneralizedStafford/Challenge/Transport.lean` from the library declaration in
the same row, and restated under `<name>` in `GeneralizedStaffordSolution.lean`
(identical copy `Solution.lean`). The challenge is
`GeneralizedStaffordChallenge.lean` (identical copy `Challenge.lean`).

| Paper statement | Challenge theorem | Library declaration | Library file |
| --- | --- | --- | --- |
| Theorem A' (fixed ideal); core §1, proof §4; manuscript `sec:descent` | `fixedIdeal` | `fixed_ideal` | `GeneralizedStafford/TheoremA.lean` |
| Theorem A (fixed anchor); core §1; manuscript `sec:descent` | `fixedAnchor` | `fixed_anchor` | `GeneralizedStafford/TheoremA.lean` |
| Corollary B, dimension part; core Lemma 6.1; manuscript `lem:Hall` without the ordinal clause | `corollaryB_dimension` | `principal_quotient_finite_of_omega`, `principalQuotientsFinite_of_devLE_omega`, `quotient_finite_of_omega` | `GeneralizedStafford/CorollaryB.lean` |
| Corollary B for Theorem A | `corollaryB_fixedAnchor` | `fixed_anchor_of_devLE_omega` | `GeneralizedStafford/CorollaryB.lean` |
| Corollary B for Theorem A' | `corollaryB_fixedIdeal` | `fixed_ideal_of_devLE_omega` | `GeneralizedStafford/CorollaryB.lean` |
| C.1, stable form; manuscript `prop:C1`(a) | `corollaryC1_stable` | `span_pair_eq_span_affine` | `GeneralizedStafford/Modules.lean` |
| C.1; core Lemma 6.2; `prop:C1`(b) | `corollaryC1` | `prescribed_cyclic` | `GeneralizedStafford/Modules.lean` |
| C.1 under (H_all); core Lemma 6.2, last sentence | `corollaryC1_hAll` | `prescribed_cyclic_of_hAll` | `GeneralizedStafford/Modules.lean` |
| C.1 under (H_omega); core Corollary C.1 | `corollaryC1_omega` | `prescribed_cyclic_of_devLE_omega` | `GeneralizedStafford/Modules.lean` |
| C.2, existence of `a` with `aQ = IQ`; core Lemma 6.3, first step | `corollaryC2_fullRank` | `AlgebraicAnalysis.Goldie.exists_mem_forall_exists_mul_mem` | AlgebraicAnalysis `RingTheory/Goldie/Basic.lean` |
| C.2, prescribed form; core Lemma 6.3; `prop:C2` | `corollaryC2_prescribed` | `two_generated_prescribed` | `GeneralizedStafford/Modules.lean` |
| C.2, two generators; core Corollary C.2 | `corollaryC2` | `two_generated` | `GeneralizedStafford/Modules.lean` |
| C.3, lower bound `ceil(rho M) <= mu(M)`; core Lemma 6.4; `prop:C3` | `corollaryC3_lower` | `le_mul_of_span_eq_top` (from AlgebraicAnalysis `Goldie.le_mul_of_uniformDim`) | `GeneralizedStafford/GeneratorBounds.lean` |
| C.3, upper bound `mu(M) <= floor(rho M) + 1`; lane-C3; `prop:C3` | `corollaryC3_upper` | `exists_span_eq_top_of_lt_mul` (rank form `spanRank_le_of_goldieRank_lt`, base case `cyclic_of_goldieRank_lt`) | `GeneralizedStafford/GeneratorBounds.lean` |

The library endpoints audited by `scripts/verify.sh` are listed in
[endpoints.txt](endpoints.txt).

## Conventions in the challenge

| Paper | Challenge | Note |
| --- | --- | --- |
| right module `M`, product `m r` | `[Module Rᵐᵒᵖ M]`, `MulOpposite.op r • m` | `op r • x = x * r` in `R` holds by `rfl` |
| right ideal, `xR`, `I + J` | `Submodule Rᵐᵒᵖ R`, `Submodule.span Rᵐᵒᵖ {x}`, `I ⊔ J` | products stay in the displayed order |
| (S) simple | `IsSimpleRing R` | includes `R ≠ 0` |
| (N) right Noetherian | `IsNoetherian Rᵐᵒᵖ R` | ACC on right ideals |
| (Z) infinite centre | `Infinite (Subring.center R)` | the centre is a field under (S) |
| regular element | `IsRegularElement d` | two-sided; definitionally `d ∈ R⁰` |
| `Kdim M <= n`, finite `Kdim`, `Kdim M <= omega` | `DevDimLE`, `HasFiniteDevDim`, `DevDimLEOmega`, via `PosetDevLE` on submodule lattices | Gabriel-Rentschler deviation, not Mathlib's `Order.KrullDimLE` |
| Goldie-torsion module, `t(M)` | `IsGoldieTorsion`, `goldieTorsionPart` | `t(M)` is a span; under (S), (N) it equals the set of torsion elements |
| uniform dimension `>= n`, `<= n` | `UDimGE`, `UDimLE` | via `iSupIndep` families of nonzero submodules |
| `mu(M) <= m` | `SpanRankLE R M m` | a `Finset` of at most `m` generators |
| (H_all), (H_omega) | `HAll`, `HOmega` | |
| finite module | `Module.Finite Rᵐᵒᵖ M` | |

Rings live in universe `u` and modules in universe `v`; every theorem is stated
for all universes.

## Faithfulness choices

- **C.2, `aQ = IQ`.** Stated elementwise: `a ∈ I` and every `y ∈ I` has a
  regular `s` with `y s ∈ aR`. Under (S), (N) this is equivalent to
  `aQ = IQ`, because `y ∈ aQ` iff `y s = a r` for some `r` and regular `s`.
- **C.2, full-rank existence.** Stated under (S), (N) only. The paper states
  C.2 under (S), (N), (Z), (H_all); this step is Goldie theory and needs less.
- **C.3, no division or rounding.** With `l = udim(M/t(M))` and
  `s = udim(R_R)`, the lower bound reads `l <= m s` whenever `M` is generated
  by `m` elements, and the upper bound reads "`M` is generated by `q`
  elements whenever `l < q s`". These are equivalent to
  `ceil(rho M) <= mu(M)` and `mu(M) <= floor(rho M) + 1` given two classical
  identities under (S), (N): `s = udim(R_R)` for `Q = M_s(D)`, and
  `length_Q(M ⊗_R Q) = udim(M/t(M))` (Goldie; McConnell-Robson 2.2-2.3). The
  challenge does not formalize `rho` itself. The lower bound assumes only
  (S), (N), as in the paper.
- **Omissions.** Not stated: the ordinal clause `delta(d) < Kdim R` of
  `lem:Hall`; the instance `R = dR + HdR` of Theorem A (`B = 0`, `a = 1`) as a
  separate theorem; opposite-side statements (core Remark 6.5); Theorem D and
  manuscript Sections 7-11 (beyond `omega`, applications, sharpness, finite
  centre). Each omission makes the formal content weaker, never stronger.

## Statement-faithfulness audit

An independent audit (2 November 2026) compared the challenge with core
Sections 0, 1, 6 and the manuscript. Its durable record is
`docs/lane-palomar-statement-audit.md` of the research repository at commit
`1f05218`, with the audited challenge frozen at sha256
`4cb2cd5e7a6043f4c38fecddb78850d6f8012048c91a7de7e188d18598dc9e95`. Later
changes to the challenge are renames and docstrings only, as confirmed by
the final review of 2 November 2026. The audit compiled the candidate and a
sanity file checking the right-module encoding by `rfl`,
`IsRegularElement d ↔ d ∈ R⁰`, that `PosetDevLE 0 ℕᵒᵈ` fails (the bound is
not trivially true), that the zero module satisfies every bound, and that
`UDimLE R R 0` fails for nonzero `R` (the C.3 lower bound is not vacuous).

| Scope | Verdict |
| --- | --- |
| 1. Definitions (deviation, regularity, torsion, uniform dimension, generator count, (H_all), (H_omega)) | PASS |
| 2. Hypotheses (S), (N), (Z) | PASS |
| 3. Statements of A', A, B, C.1, C.2 against the paper | PASS; none stronger than the paper, omissions documented |
| 4. C.3 via uniform dimension, including the edge cases `M = 0`, torsion `M`, integral `rho`, `s = 0` | PASS, given the two classical Goldie identities |
| 5. Readability | REPAIR: renames `KrullDimLE` → `DevDimLE`, `HasFiniteKrullDim` → `HasFiniteDevDim`, `KrullDimLEOmega` → `DevDimLEOmega`, `GeneratedBy` → `SpanRankLE`, and docstring additions. Applied without statement change. |

The audit covers statement faithfulness only. It does not audit the proofs;
the Lean kernel and the local replay of the Palomar check verify those.

## Proof steps

### Conventions and inputs

| Paper item | Lean declaration | File |
| --- | --- | --- |
| core §0 C1, right modules, right ideals | `[Module Rᵐᵒᵖ M]`, `Submodule Rᵐᵒᵖ R`, `principalRightIdeal x` = `xR` | `GeneralizedStafford/Basic.lean` (module docstring) |
| core §0 C2, regular element | `d ∈ R⁰` (library); `IsRegularElement` (challenge) | `GeneralizedStafford/Basic.lean`; `Challenge.lean` |
| core §0 C3, `Kdim M ≤ n`, `Kdim M ≤ ω` | `Module.DevLE Rᵐᵒᵖ n M`, `Module.DevLEOmega Rᵐᵒᵖ M` (AlgebraicAnalysis); `DevDimLE`, `HasFiniteDevDim`, `DevDimLEOmega` (challenge) | AlgebraicAnalysis `Module/Deviation.lean`, `Module/DeviationOmega.lean`; `Challenge.lean` |
| core §0 C4, Goldie torsion | `AlgebraicAnalysis.Goldie.IsGoldieTorsion`; `IsGoldieTorsion` (challenge) | AlgebraicAnalysis `RingTheory/Goldie/Torsion.lean`; `Challenge.lean` |
| core §0 (Z), infinite centre | infinite field `k` with `[Algebra k R]` (library); `Infinite (Subring.center R)` (challenge); bridge `withCentre` | `GeneralizedStafford/Challenge/Transport.lean` |
| (H_all) | `PrincipalQuotientsFinite` (the name `HAll` is kept for the challenge's copy); `HAll` (challenge); bridge `hAll_iff` | `GeneralizedStafford/Basic.lean`; `Challenge.lean`; `GeneralizedStafford/Challenge/Transport.lean` |
| (H_omega) | `Module.DevLEOmega Rᵐᵒᵖ R`; `HOmega` (challenge); bridge `hOmega_iff` | `Challenge.lean`; `GeneralizedStafford/Challenge/Transport.lean` |
| core §2 I1 (Goldie): regular `b` with `f b ∈ I` | `AlgebraicAnalysis.Goldie.exists_mul_mem_of_mem_nonZeroDivisors` | AlgebraicAnalysis `RingTheory/Goldie/Basic.lean` |
| core §2 I1: `R/I` Goldie-torsion under (Reg_I) | `AlgebraicAnalysis.Goldie.isGoldieTorsion_quotient` | AlgebraicAnalysis `RingTheory/Goldie/Torsion.lean` |
| core §2 I1: common regular annihilator | `AlgebraicAnalysis.Goldie.IsGoldieTorsion.exists_common_regular_annihilator` | AlgebraicAnalysis `RingTheory/Goldie/Torsion.lean` |
| core §2 I1(b): Goldie's theorem, `Q` simple Artinian (used only for C.3) | `AlgebraicAnalysis.Goldie.exists_ringEquiv_matrix_divisionRing` | AlgebraicAnalysis `RingTheory/Goldie/QuotientRing.lean` |
| core §2 I2, I3 (Gabriel quotient, finite top strata) | germ calculus `Module.Germ.Hom`, `Hom.Epic`, `Module.CriticalFiltration`, `Hom.finite_of_devLE`, `Hom.epic_iff_injective_comp_topFactors` | AlgebraicAnalysis `Module/Germ.lean`, `Module/GermSchur.lean`, `Module/DualSeparationGeneral.lean` |
| core §2 I4 (central eigenvalues, pencils) | `AlgebraicAnalysis.TorsionEscape.centralPencil_injective_finite`, `reversed_centralPencil_injective_finite` | AlgebraicAnalysis `Module/TorsionEscape.lean` |
| core §2 I1, I5 for C.3: `M_Q`, `t(M)`, Goldie rank `l(M) = length_Q(M_Q)`, `s = l(R_R)`, additivity | `Goldie.FractionModule`, `Goldie.goldieTorsionPart`, `Goldie.goldieRank`, `Goldie.goldieRank_eq_add_of_exact`, `Goldie.goldieRank_self` | AlgebraicAnalysis `RingTheory/Goldie/Rank.lean` |
| C.3 note B1--B7: `s = udim(R_R)`, `l(M) = udim(M/t(M))`; `udim` | `Goldie.uniformDimGE_quotient_iff`, `uniformDimLE_quotient_iff`, `uniformDimGE_self_iff`, `uniformDimLE_self_iff`; `Module.UniformDimGE`, `UniformDimLE`; `UDimGE`, `UDimLE` (challenge), bridges `uDimGE_iff`, `uDimLE_iff`, `goldieTorsionPart_eq` | AlgebraicAnalysis `RingTheory/Goldie/Rank.lean`, `Module/UniformDimension.lean`; `GeneralizedStafford/Challenge/Transport.lean` |
| core Lemma 6.4 (case `l < s`): idempotents of `Q` with common denominators `f_i`, `r_i` | `Goldie.exists_idempotent_denominators` | AlgebraicAnalysis `RingTheory/Goldie/Idempotents.lean` |
| core Lemma 6.4 (case `l < s`): successive choice, simplicity argument | `exists_span_fraction_eq_top`, `eq_top_of_forall_toFractionModule_smul_mem` | `GeneralizedStafford/GeneratorBounds.lean` |
| C.3 note U3--U9: `Q_Q ↪ M_Q`, `pR ≅ R_R`, `l(M/pR) = l(M) - s` | `exists_injective_smul_of_length_le`, `exists_injective_toSpanSingleton`, `exists_goldieRank_eq_add_quotient` | `GeneralizedStafford/GeneratorBounds.lean` |
| elementary: `R/X` quotient of `R/dR`; `uR ≅ R/ann(u)`; `R/J = 0 ⇒ J = R` | `devLE_quotient_of_le`, `principalRightIdeal_le`, `cyclicMap`, `devLE_quotient_ker_cyclicMap_iff`, `eq_top_of_small_zero` | `GeneralizedStafford/Basic.lean` |

### Section 3: germs and source selection (manuscript `sec:germs`)

| Paper item | Lean declaration | File |
| --- | --- | --- |
| core §3 "Central scalars", manuscript `eq:central` (E1) | `oppositeCentralField`, `section_central_scalar` | `GeneralizedStafford/Germs.lean` |
| core Lemma 3.1, `lem:unit` (unit germs) | `smul_mkQ_epic_iff` (with `quotient_section_epic_iff`) | `GeneralizedStafford/Germs.lean` |
| core Lemma 3.2, `lem:epic` (epic criterion) | `Module.Germ.Hom.epic_iff_injective_comp_topFactors` | AlgebraicAnalysis `Module/DualSeparationGeneral.lean` |
| core Lemma 3.3, `lem:pencil` (pencils) | `AlgebraicAnalysis.TorsionEscape.centralPencil_injective_finite`, `reversed_centralPencil_injective_finite` | AlgebraicAnalysis `Module/TorsionEscape.lean` |
| core Lemma 3.4, `lem:escape` (escape) | `AlgebraicAnalysis.Goldie.IsGoldieTorsion.exists_smul_mul_not_mem` | AlgebraicAnalysis `RingTheory/Goldie/Torsion.lean` |
| core Lemma 3.5, `lem:rank` (maximal rank) | `AlgebraicAnalysis.Goldie.IsGoldieTorsion.exists_injective_right_mul` | AlgebraicAnalysis `RingTheory/Goldie/Torsion.lean` |
| core Lemma 3.6, `lem:select`, stability | `germ_pencil_finite`, `GermTest.pencil_finite`, `test_pencil_identity` | `GeneralizedStafford/Germs.lean` |
| core Lemma 3.6, `lem:select`, selection Steps 1--2 | `exists_affine_direction_of_goldie`, `exists_affine_source_of_goldie`, `exists_affine_germ_tests`, `exists_affine_epic_tests`, `GermTest.exists_affine_satisfied` | `GeneralizedStafford/Germs.lean` |
| core §3 "test" `(e, V, q, z, c)` and satisfaction | `GermTest`, `GermTest.Satisfied` | `GeneralizedStafford/Germs.lean` |
| core §4 step 3, the unit test `(e, V_J, q_J, 0, 1)` | `unitTest`, `unitTest_satisfied_iff` | `GeneralizedStafford/Germs.lean` |

### Section 4: the two-call descent (manuscript `sec:descent`)

| Paper item | Lean declaration | File |
| --- | --- | --- |
| core §4 assertion `P(h)` (with `e = N - h + 1`) | `IdealBound` | `GeneralizedStafford/Descent.lean` |
| core §4 base `P(0)` | `idealBound_initial` | `GeneralizedStafford/Descent.lean` |
| core §4 step `P(h) ⇒ P(h+1)`, steps 1--8 (comments `Step 1` ... `Step 8` in the proof) | `idealBound_step` | `GeneralizedStafford/Descent.lean` |
| core §4 inclusion (4.2), manuscript `eq:inclusion` | `mul_mem_sup_pencil` | `GeneralizedStafford/Descent.lean` |
| core §4 step 8 (affine form) | `affine_update` | `GeneralizedStafford/Descent.lean` |
| core §4 termination, §5 E2 | `idealBound_zero` | `GeneralizedStafford/Descent.lean` |

### Main results

| Paper item | Lean declaration (library) | Challenge name (Palomar) | Files |
| --- | --- | --- | --- |
| Theorem A' (fixed ideal), core §1; manuscript intro, proof in `sec:descent` | `fixed_ideal` | `fixedIdeal` | `GeneralizedStafford/TheoremA.lean`; `Challenge.lean`, `Solution.lean` |
| Theorem A (fixed anchor), core §1; manuscript intro, proof in `sec:descent` | `fixed_anchor` | `fixedAnchor` | `GeneralizedStafford/TheoremA.lean`; `Challenge.lean`, `Solution.lean` |
| Corollary B, dimension part: core Lemma 6.1; manuscript `lem:Hall` (without the ordinal clause `δ(d) < Kdim R`) | `principal_quotient_finite_of_omega`, `principalQuotientsFinite_of_devLE_omega`, `quotient_finite_of_omega` | `corollaryB_dimension` | `GeneralizedStafford/CorollaryB.lean` |
| Corollary B for Theorem A | `fixed_anchor_of_devLE_omega` | `corollaryB_fixedAnchor` | `GeneralizedStafford/CorollaryB.lean` |
| Corollary B for Theorem A' | `fixed_ideal_of_devLE_omega` | `corollaryB_fixedIdeal` | `GeneralizedStafford/CorollaryB.lean` |
| C.1 stable cyclicity: manuscript `prop:C1`(a) | `span_pair_eq_span_affine` | `corollaryC1_stable` | `GeneralizedStafford/Modules.lean` |
| C.1: core Lemma 6.2; manuscript `prop:C1`(b) | `prescribed_cyclic` (induction `prescribed_cyclic_aux`, `prescribed_cyclic_of_cyclic`) | `corollaryC1` | `GeneralizedStafford/Modules.lean` |
| C.1 under (H_all): core Lemma 6.2, last sentence; `prop:C1`, last sentence | `prescribed_cyclic_of_hAll` | `corollaryC1_hAll` | `GeneralizedStafford/Modules.lean` |
| C.1 under (H_omega): core Corollary C.1 | `prescribed_cyclic_of_devLE_omega` | `corollaryC1_omega` | `GeneralizedStafford/Modules.lean` |
| C.2, full-rank element `aQ = IQ`: core Lemma 6.3, first step; `prop:C2`, first sentence | `AlgebraicAnalysis.Goldie.exists_mem_forall_exists_mul_mem` | `corollaryC2_fullRank` | AlgebraicAnalysis `RingTheory/Goldie/Basic.lean` |
| C.2, prescribed form: core Lemma 6.3; `prop:C2` | `two_generated_prescribed` | `corollaryC2_prescribed` | `GeneralizedStafford/Modules.lean` |
| C.2, every right ideal two-generated: core Corollary C.2; `prop:C2` | `two_generated` | `corollaryC2` | `GeneralizedStafford/Modules.lean` |
| C.3, lower bound `⌈ρ⌉ ≤ μ`: core Lemma 6.4; `prop:C3` | `le_mul_of_span_eq_top` (from AlgebraicAnalysis `Goldie.le_mul_of_uniformDim`) | `corollaryC3_lower` | `GeneralizedStafford/GeneratorBounds.lean` |
| C.3, upper bound `μ ≤ ⌊ρ⌋ + 1`: core Lemma 6.4 (case `l < s`) and `lane-C3-rank-without-morita.md` (induction on `q`); `prop:C3` | `exists_span_eq_top_of_lt_mul` (rank form `spanRank_le_of_goldieRank_lt`, base case `cyclic_of_goldieRank_lt`) | `corollaryC3_upper` | `GeneralizedStafford/GeneratorBounds.lean` |

Each challenge name `<name>` is proved as `<name>_proof` in
`GeneralizedStafford/Challenge/Transport.lean` from the library declaration
in the same row, and restated under `<name>` in `GeneralizedStaffordSolution.lean`
(identical copy `Solution.lean`).

### Not formalized (non-claims)

Theorem D and manuscript Sections 7--11 (beyond `ω`, applications, sharpness,
finite-centre testbed); the ordinal clause of `lem:Hall`; the instance
`R = dR + HdR` of Theorem A (B = 0, a = 1) as a separate statement;
opposite-side statements (core Remark 6.5).
