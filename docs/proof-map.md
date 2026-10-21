# Written proof and Lean correspondence

The machine-readable [paper-lean-map.json](paper-lean-map.json) records 19
correspondence cards for the commutative-symbol proof and consequences,
40 declaration references and all 19 audited endpoints. It pins an immutable
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
extensions, categorical localization, the finite-integer GR-Krull candidate
and constructive Weyl algorithms and bounds are not formalized here.
The source map records these omissions explicitly. Human review and full
programme completion remain open in the two repositories' PLAN files.
