# Open holes for the Palomar challenge

`GeneralizedStaffordChallenge.lean` (identical copy `Challenge.lean`) keeps one
deliberate `sorry` per compared theorem. `GeneralizedStaffordSolution.lean`
(identical copy `Solution.lean`) contains no `sorry`.

Status: no open holes. All 16 theorems of `comparator.json` are proved (the fourteen via `GeneralizedStafford/Challenge/Transport.lean`, the two Weyl theorems via `GeneralizedStafford/Challenge/WeylTransport.lean`) and accepted by the comparator.

Solved: `fixedIdeal`, `fixedAnchor`, `corollaryB_dimension`,
`corollaryB_fixedAnchor`, `corollaryB_fixedIdeal`, `corollaryC1`,
`corollaryC1_hAll`, `corollaryC1_omega`, `corollaryC1_stable`,
`corollaryC2_fullRank`, `corollaryC2_prescribed`, `corollaryC2`,
`corollaryC3_lower`, `corollaryC3_upper`, `weylTwoGeneratedRight`,
`weylTwoGeneratedLeft`.

Not yet in the challenge (no statement is added without a proof): the Weyl algebra
statements of Conjecture 3.8, the affine form, the fixed ideal, torsion and prescribed
cyclicity (right and left), and prescribed two-generation (right and left). Each needs
that nonzero elements of `A_n(k)` are regular, i.e. that `A_n(k)` has no zero divisors.
AlgebraicAnalysis does not provide this yet. `GeneralizedStafford/Weyl.lean` proves
these consequences from the explicit hypothesis `NoZeroDivisorsWeyl`.

Add a solution theorem only when its proof is checked; never add `sorry`.
When one is added, extend `Solution.lean`, `GeneralizedStaffordSolution.lean`,
`comparator.json`, the expected list in `scripts/verify-palomar.sh`,
`tests/SolutionOracle.lean` and `docs/endpoints.txt` together.
