# Open holes for the Palomar challenge

`GeneralizedStaffordChallenge.lean` (identical copy `Challenge.lean`) keeps one
deliberate `sorry` per compared theorem. `GeneralizedStaffordSolution.lean`
(identical copy `Solution.lean`) contains no `sorry`.

Status: no open holes. All 25 theorems of `comparator.json` are proved and accepted by the
comparator. Fourteen are proved via `GeneralizedStafford/Challenge/Transport.lean`; the two
`weylTwoGenerated*` theorems and the nine Weyl algebra statements below are proved in
`GeneralizedStafford/Challenge/WeylTransport.lean` from `GeneralizedStafford/Weyl.lean`,
with no hypothesis beyond the statements themselves.

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

Add a solution theorem only when its proof is checked; never add `sorry`.
When one is added, extend `Solution.lean`, `GeneralizedStaffordSolution.lean`,
`comparator.json`, the expected list in `scripts/verify-palomar.sh`,
`tests/SolutionOracle.lean` and `docs/endpoints.txt` together.
