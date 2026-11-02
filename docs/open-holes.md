# Open holes for the Palomar challenge

`GeneralizedStaffordChallenge.lean` (identical copy `Challenge.lean`) keeps one
deliberate `sorry` per compared theorem. `GeneralizedStaffordSolution.lean`
(identical copy `Solution.lean`) contains no `sorry`.

Status: no open holes. All 14 theorems of `comparator.json` are proved (via `GeneralizedStafford/Challenge/Transport.lean`) and accepted by the comparator.

Solved: `fixedIdeal`, `fixedAnchor`, `corollaryB_dimension`,
`corollaryB_fixedAnchor`, `corollaryB_fixedIdeal`, `corollaryC1`,
`corollaryC1_hAll`, `corollaryC1_omega`, `corollaryC1_stable`,
`corollaryC2_fullRank`, `corollaryC2_prescribed`, `corollaryC2`,
`corollaryC3_lower`, `corollaryC3_upper`.

Add a solution theorem only when its proof is checked; never add `sorry`.
When one is added, extend `Solution.lean`, `GeneralizedStaffordSolution.lean`,
`comparator.json`, the expected list in `scripts/verify-palomar.sh`,
`tests/SolutionOracle.lean` and `docs/endpoints.txt` together.
