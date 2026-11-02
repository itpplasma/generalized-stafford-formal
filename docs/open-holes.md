# Open holes for the Palomar challenge

Status of `GeneralizedStaffordChallenge.lean` (copy `Challenge.lean`) against
`GeneralizedStaffordSolution.lean`. The challenge keeps one deliberate `sorry`
per compared theorem; the solution contains no `sorry`.

## Solved (transported in `GeneralizedStafford/Challenge/Transport.lean`)

`fixedIdeal`, `fixedAnchor`, `corollaryB_dimension`, `corollaryB_fixedAnchor`,
`corollaryB_fixedIdeal`, `corollaryC1`, `corollaryC1_hAll`, `corollaryC1_omega`,
`corollaryC2_prescribed`. These are the `theorem_names` of `comparator.json`.

## Not yet solved (absent from the solution; proved in other lanes)

| Challenge declaration | Paper statement | Proposed route (from the challenge notes) |
| --- | --- | --- |
| `corollaryC1_stable` | C.1 stable cyclicity, `prop:C1`(a) | `Regular.fixed_ideal` on `ker(r ↦ u r)` with offset 0 and tail `t b`, as in the manuscript proof; the computation is inside `Regular.prescribed_cyclic_aux` |
| `corollaryC2_fullRank` | C.2, existence of `a ∈ I` with `aQ = IQ` (Lemma 6.3, first step) | not formalized |
| `corollaryC2` | C.2, every right ideal two-generated | `corollaryC2_fullRank` with `corollaryC2_prescribed`; only domains are formalized in `Regular.two_generated_of_principal` |
| `corollaryC3_lower` | C.3, `⌈ρ⌉ ≤ μ` | not formalized |
| `corollaryC3_upper` | C.3, `μ ≤ ⌊ρ⌋ + 1` | not formalized |

Add a solution theorem only when its proof is checked; do not add `sorry`.

## TODO for the controller

- Palomar tool pins: `scripts/bootstrap-palomar-tools.sh` and the expected
  revisions in `scripts/verify-palomar.sh` are copied from the model project
  (Lean v4.33.0, comparator toolchain v4.34.0-rc1). This project uses Lean
  v4.35.0-rc3. Choose matching Comparator, lean4export, NanoDa and Landrun
  revisions, then update both scripts. Not done here: the revisions were not
  guessed.
- `scripts/verify.sh` builds only `GeneralizedStafford`; the Challenge and
  Solution targets are built by `scripts/verify-palomar.sh` and the commands in
  the commit body.
