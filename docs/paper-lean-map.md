# Paper to Lean map

Sources: research note `docs/core-theorem.md` (repository
`itpplasma/generalized-stafford`; cited as "core") and manuscript
`docs/manuscript/main.tex` (cited by `\label`). Lean paths are relative to this
repository. Namespaces: `GeneralizedStafford` (library), `AlgebraicAnalysis`
(pinned dependency `itpplasma/algebraic-analysis`), and
`GeneralizedStaffordChallenge` (Palomar challenge and solution).

## Conventions and inputs

| Paper item | Lean declaration | File |
| --- | --- | --- |
| core §0 C1, right modules, right ideals | `[Module Rᵐᵒᵖ M]`, `Submodule Rᵐᵒᵖ R`, `principalRightIdeal x` = `xR` | `GeneralizedStafford/Basic.lean` (module docstring) |
| core §0 C2, regular element | `d ∈ R⁰` (library); `IsRegularElement` (challenge) | `GeneralizedStafford/Basic.lean`; `Challenge.lean` |
| core §0 C3, `Kdim M ≤ n`, `Kdim M ≤ ω` | `Module.DevLE Rᵐᵒᵖ n M`, `Module.DevLEOmega Rᵐᵒᵖ M` (AlgebraicAnalysis); `DevDimLE`, `HasFiniteDevDim`, `DevDimLEOmega` (challenge) | AlgebraicAnalysis `Module/Deviation.lean`, `Module/DeviationOmega.lean`; `Challenge.lean` |
| core §0 C4, Goldie torsion | `AlgebraicAnalysis.Goldie.IsGoldieTorsion`; `IsGoldieTorsion` (challenge) | AlgebraicAnalysis `RingTheory/Goldie/Torsion.lean`; `Challenge.lean` |
| core §0 (Z), infinite centre | infinite field `k` with `[Algebra k R]` (library); `Infinite (Subring.center R)` (challenge); bridge `withCentre` | `GeneralizedStafford/Challenge/Transport.lean` |
| (H_all) | `PrincipalQuotientsFinite`; `HAll` (challenge); bridge `hAll_iff` | `GeneralizedStafford/Basic.lean`; `Challenge.lean`; `GeneralizedStafford/Challenge/Transport.lean` |
| (H_omega) | `Module.DevLEOmega Rᵐᵒᵖ R`; `HOmega` (challenge); bridge `hOmega_iff` | `Challenge.lean`; `GeneralizedStafford/Challenge/Transport.lean` |
| core §2 I1 (Goldie): regular `b` with `f b ∈ I` | `AlgebraicAnalysis.Goldie.exists_mul_mem_of_mem_nonZeroDivisors` | AlgebraicAnalysis `RingTheory/Goldie/Basic.lean` |
| core §2 I1: `R/I` Goldie-torsion under (Reg_I) | `AlgebraicAnalysis.Goldie.isGoldieTorsion_quotient` | AlgebraicAnalysis `RingTheory/Goldie/Torsion.lean` |
| core §2 I1: common regular annihilator | `AlgebraicAnalysis.Goldie.IsGoldieTorsion.exists_common_regular_annihilator` | AlgebraicAnalysis `RingTheory/Goldie/Torsion.lean` |
| core §2 I1(b): Goldie's theorem, `Q` simple Artinian (not used by the proofs below) | `AlgebraicAnalysis.Goldie.exists_ringEquiv_matrix_divisionRing` | AlgebraicAnalysis `RingTheory/Goldie/QuotientRing.lean` |
| core §2 I2, I3 (Gabriel quotient, finite top strata) | germ calculus `Module.Germ.Hom`, `Hom.Epic`, `Module.CriticalFiltration`, `Hom.finite_of_devLE`, `Hom.epic_iff_injective_comp_topFactors` | AlgebraicAnalysis `Module/Germ.lean`, `Module/GermSchur.lean`, `Module/DualSeparationGeneral.lean` |
| core §2 I4 (central eigenvalues, pencils) | `AlgebraicAnalysis.TorsionEscape.centralPencil_injective_finite`, `reversed_centralPencil_injective_finite` | AlgebraicAnalysis `Module/TorsionEscape.lean` |
| elementary: `R/X` quotient of `R/dR`; `uR ≅ R/ann(u)`; `R/J = 0 ⇒ J = R` | `devLE_quotient_of_le`, `principalRightIdeal_le`, `cyclicMap`, `devLE_quotient_ker_cyclicMap_iff`, `eq_top_of_small_zero` | `GeneralizedStafford/Basic.lean` |

## Section 3: germs and source selection (manuscript `sec:germs`)

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

## Section 4: the two-call descent (manuscript `sec:descent`)

| Paper item | Lean declaration | File |
| --- | --- | --- |
| core §4 assertion `P(h)` (with `e = N - h + 1`) | `IdealBound` | `GeneralizedStafford/Descent.lean` |
| core §4 base `P(0)` | `idealBound_initial` | `GeneralizedStafford/Descent.lean` |
| core §4 step `P(h) ⇒ P(h+1)`, steps 1--8 (comments `Step 1` ... `Step 8` in the proof) | `idealBound_step` | `GeneralizedStafford/Descent.lean` |
| core §4 inclusion (4.2), manuscript `eq:inclusion` | `mul_mem_sup_pencil` | `GeneralizedStafford/Descent.lean` |
| core §4 step 8 (affine form) | `affine_update` | `GeneralizedStafford/Descent.lean` |
| core §4 termination, §5 E2 | `idealBound_zero` | `GeneralizedStafford/Descent.lean` |

## Main results

| Paper item | Lean declaration (library) | Challenge name (Palomar) | Files |
| --- | --- | --- | --- |
| Theorem A' (fixed ideal), core §1; manuscript intro, proof in `sec:descent` | `fixed_ideal` | `fixedIdeal` | `GeneralizedStafford/TheoremA.lean`; `Challenge.lean`, `Solution.lean` |
| Theorem A (fixed anchor), core §1; manuscript intro, proof in `sec:descent` | `fixed_anchor` | `fixedAnchor` | `GeneralizedStafford/TheoremA.lean`; `Challenge.lean`, `Solution.lean` |
| Corollary B, dimension part: core Lemma 6.1; manuscript `lem:Hall` (without the ordinal clause `δ(d) < Kdim R`) | `principal_quotient_finite_of_omega`, `principalQuotientsFinite_of_devLE_omega`, `quotient_finite_of_omega` | `corollaryB_dimension` | `GeneralizedStafford/CorollaryB.lean` |
| Corollary B for Theorem A | `fixed_anchor_of_devLE_omega` | `corollaryB_fixedAnchor` | `GeneralizedStafford/CorollaryB.lean` |
| Corollary B for Theorem A' | `fixed_ideal_of_devLE_omega` | `corollaryB_fixedIdeal` | `GeneralizedStafford/CorollaryB.lean` |
| C.1 stable cyclicity: manuscript `prop:C1`(a) | `span_pair_eq_span_affine` | `corollaryC1_stable` | `GeneralizedStafford/Modules.lean` |
| C.1: core Lemma 6.2; manuscript `prop:C1`(b) | `prescribed_cyclic` (induction `prescribed_cyclic_aux`, `prescribed_cyclic_of_cyclic`) | `corollaryC1` | `GeneralizedStafford/Modules.lean` |
| C.1 under (H_all): core Lemma 6.2, last sentence; `prop:C1`, last sentence | `prescribed_cyclic_of_principal` | `corollaryC1_hAll` | `GeneralizedStafford/Modules.lean` |
| C.1 under (H_omega): core Corollary C.1 | `prescribed_cyclic_of_devLE_omega` | `corollaryC1_omega` | `GeneralizedStafford/Modules.lean` |
| C.2, full-rank element `aQ = IQ`: core Lemma 6.3, first step; `prop:C2`, first sentence | `AlgebraicAnalysis.Goldie.exists_mem_forall_exists_mul_mem` | `corollaryC2_fullRank` | AlgebraicAnalysis `RingTheory/Goldie/Basic.lean` |
| C.2, prescribed form: core Lemma 6.3; `prop:C2` | `two_generated_of_principal` | `corollaryC2_prescribed` | `GeneralizedStafford/Modules.lean` |
| C.2, every right ideal two-generated: core Corollary C.2; `prop:C2` | `two_generated` | `corollaryC2` | `GeneralizedStafford/Modules.lean` |
| C.3, lower bound: core Lemma 6.4; `prop:C3` | not formalized | `corollaryC3_lower` (open) | `Challenge.lean`; see `docs/open-holes.md` |
| C.3, upper bound: core Lemma 6.4; `prop:C3` | not formalized | `corollaryC3_upper` (open) | `Challenge.lean`; see `docs/open-holes.md` |

Each challenge name `<name>` is proved as `<name>_proof` in
`GeneralizedStafford/Challenge/Transport.lean` from the library declaration
in the same row, and restated under `<name>` in `GeneralizedStaffordSolution.lean`
(identical copy `Solution.lean`).

## Not formalized (non-claims)

Theorem D and manuscript Sections 7--11 (beyond `ω`, applications, sharpness,
finite-centre testbed); the ordinal clause of `lem:Hall`; the instance
`R = dR + HdR` of Theorem A (B = 0, a = 1) as a separate statement;
opposite-side statements (core Remark 6.5).
