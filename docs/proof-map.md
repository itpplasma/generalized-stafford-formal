# Candidate declaration map

Reviewed correspondence: **pending**. The mathematical authority is the
[research proof dossier](https://github.com/itpplasma/generalized-stafford/blob/main/docs/proof.md).
Its current note is an outline, not a completed written proof. The table below
identifies imported declarations for candidate proof steps; it does not certify
whole-proof correspondence or concrete applicability. The original manuscript
section references in imported code are retained as historical locators.

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
| Opposite-handed identity | `FilteredAlgebraData.targetA_left` | [Opposite](../GeneralizedStafford/Opposite.lean) |
| Same-divisor, generation and cancellation consequences | `FilteredAlgebraData.s38`, `torsion_cyclic`, `stable_range`, `stably_free`, `cancellation` | [ConsequencesForU](../GeneralizedStafford/ConsequencesForU.lean) |
| Universal exported statement | `universalStatement` | [Main](../GeneralizedStafford/Main.lean) |

All declarations above are in `GeneralizedStafford`. The configured endpoint
axiom audit will cover the theorem, producer and representative consequences. The statement
audit prints the generalized data, so accidental restoration of connectedness
or finite-dimensional-piece hypotheses is visible in its output. These checks
do not replace semantic review of changed hypotheses.

The Weyl, smooth-affine differential-operator and Laurent–Euler applications
are proposed specializations. Their written structural proofs, statement
comparison and concrete Lean adapters remain separate open obligations.
