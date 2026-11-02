# Open holes for the Palomar challenge

Status of `GeneralizedStaffordChallenge.lean` (identical copy `Challenge.lean`)
against `GeneralizedStaffordSolution.lean` (identical copy `Solution.lean`). The
challenge keeps one deliberate `sorry` per compared theorem; the solution
contains no `sorry`.

## Solved (proved in `GeneralizedStafford/Challenge/Transport.lean`)

`fixedIdeal`, `fixedAnchor`, `corollaryB_dimension`, `corollaryB_fixedAnchor`,
`corollaryB_fixedIdeal`, `corollaryC1`, `corollaryC1_hAll`, `corollaryC1_omega`,
`corollaryC1_stable`, `corollaryC2_fullRank`, `corollaryC2_prescribed`,
`corollaryC2`. These are the twelve `theorem_names` of `comparator.json`.

## Not yet solved (absent from the solution)

| Challenge declaration | Paper statement | Status |
| --- | --- | --- |
| `corollaryC3_lower` | C.3, `⌈ρ⌉ ≤ μ` (core Lemma 6.4; manuscript `prop:C3`) | uniform-dimension theory being built in another lane |
| `corollaryC3_upper` | C.3, `μ ≤ ⌊ρ⌋ + 1` (core Lemma 6.4; manuscript `prop:C3`) | uniform-dimension theory being built in another lane |

Add a solution theorem only when its proof is checked; do not add `sorry`.
When one is added, extend `Solution.lean`, `GeneralizedStaffordSolution.lean`,
`comparator.json`, the expected list in `scripts/verify-palomar.sh`,
`tests/SolutionOracle.lean` and `docs/endpoints.txt` together.
