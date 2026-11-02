# Open holes for the Palomar challenge

`GeneralizedStaffordChallenge.lean` (identical copy `Challenge.lean`) keeps one
deliberate `sorry` per compared theorem. `GeneralizedStaffordSolution.lean`
(identical copy `Solution.lean`) contains no `sorry`.

Status: no open holes among the 46 compared theorems of `comparator.json`. The first 40 are proved
and were accepted by the local Comparator replay; the six differential-operator statements below are
proved locally and await the Palomar replay. Twenty-five are as before (fourteen via
`GeneralizedStafford/Challenge/Transport.lean`; the two `weylTwoGenerated*` theorems and the nine
Weyl algebra statements via `GeneralizedStafford/Challenge/WeylTransport.lean`). The eight filtered-ring
statements below are proved in `GeneralizedStafford/Challenge/FilteredTransport.lean` from
`GeneralizedStafford/Filtered.lean` and the AlgebraicAnalysis symbol lemmas, with no hypothesis beyond
the statements themselves.

Solved: `fixedIdeal`, `fixedAnchor`, `corollaryB_dimension`,
`corollaryB_fixedAnchor`, `corollaryB_fixedIdeal`, `corollaryC1`,
`corollaryC1_hAll`, `corollaryC1_omega`, `corollaryC1_stable`,
`corollaryC2_fullRank`, `corollaryC2_prescribed`, `corollaryC2`,
`corollaryC3_lower`, `corollaryC3_upper`, `weylTwoGeneratedRight`,
`weylTwoGeneratedLeft`.

Solved Weyl algebra statements (`A_n(k)`, `k` of characteristic zero): `weylConjecture38`
(Stafford's Conjecture 3.8), `weylAffineForm` (Theorem A), `weylFixedIdeal` (Theorem A'),
`weylTorsionCyclicRight` and `weylTorsionCyclicLeft` (Corollary C.1, cyclicity),
`weylPrescribedCyclicRight` and `weylPrescribedCyclicLeft` (Corollary C.1, prescribed
generator), `weylPrescribedTwoGeneratedRight` and `weylPrescribedTwoGeneratedLeft`
(Corollary C.2, prescribed first generator). The regular-element facts they need come from
AlgebraicAnalysis `Weyl.isDomain` (`A_n(k)` is a domain).

Solved filtered-ring statements (a simple `k`-algebra `R` with a filtration and a symbol into a
commutative Noetherian graded algebra of finite Krull dimension, both sides): `filteredHypotheses`
((N), (Z), `Kdim ≤ m`), `filteredTheoremA` (Theorem A, right and left forms), `filteredFixedIdeal`
(Theorem A'), `filteredCorollaryB` (dimension part of Corollary B), `filteredPrescribedCyclic`
(C.1, prescribed and stable), `filteredTwoGenerated` (C.2), `filteredGeneratorBounds` (C.3) and
`filteredDomain` (Theorem A for nonzero anchors when the symbol is a domain).

Solved simple-quotient statements of enveloping algebras (`U(𝔤)/J` as a simple `k`-algebra `R`
with a surjective algebra map `U(𝔤) → R`, `𝔤` finite-dimensional, `k` infinite): `envelopingHypotheses`
((N), (Z), `Kdim ≤ dim 𝔤` on both sides), `envelopingTheoremA`, `envelopingFixedIdeal`,
`envelopingCorollaryB`, `envelopingPrescribedCyclic` (C.1), `envelopingTwoGenerated` (C.2) and
`envelopingGeneratorBounds` (C.3). They are proved in `GeneralizedStafford/Challenge/EnvelopingTransport.lean`
from `GeneralizedStafford/Enveloping.lean`, which uses the PBW symbol presentation of AlgebraicAnalysis
(`pbwSymbolPresentation`, no PBW theorem beyond spanning), with no hypothesis beyond the statements.

Solved differential-operator statements (`D_k(A)` for a field `k` of characteristic zero and a smooth
domain `A` of finite type over `k`): `diffOpTwoGeneratedRight` and `diffOpTwoGeneratedLeft` (two
generators for right and left ideals), `diffOpFixedAnchor` (Theorem A, right and left forms),
`diffOpGlobalStafford` (the identity `1 = d R + F d S`), and `diffOpCyclicRight` and `diffOpCyclicLeft`
(cyclicity of finitely generated torsion modules). They are proved in
`GeneralizedStafford/Challenge/DiffOpTransport.lean` from `GeneralizedStafford/DifferentialOperators.lean`
and the AlgebraicAnalysis differential operators (pin `71af6ec`). The bridge is `IsDifferentialOperator P`
equals membership in AlgebraicAnalysis' `DifferentialOperators.algebra`, and `diffOps k A` equals that
subalgebra. The closure proofs of `diffOps` are complete inside the challenge and are not compared.

Add a solution theorem only when its proof is checked; never add `sorry`.
When one is added, extend `Solution.lean`, `GeneralizedStaffordSolution.lean`,
`comparator.json`, the expected list in `scripts/verify-palomar.sh`,
`tests/SolutionOracle.lean` and `docs/endpoints.txt` together.
