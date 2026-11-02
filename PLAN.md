# Generalized Stafford formal: live state

Updated: 2 November 2026. Private repository.

Status: TO BE FINALIZED BY THE CONTROLLER (expected: 14 of 14 challenge theorems proved at commit <SHA>; gates below).

The private research repository `itpplasma/generalized-stafford` owns the
mathematics and its status. This file owns the formal state only.

## Scope

The library formalizes Theorem A', Theorem A and Corollaries B, C.1, C.2 and
C.3 of the research note `docs/core-theorem.md`, with the C.3 upper bound
following `docs/lane-C3-rank-without-morita.md`. The Palomar challenge
`GeneralizedStaffordChallenge.lean` (copy `Challenge.lean`) states the 14
compared theorems listed in `comparator.json`.
[docs/paper-lean-specification.md](docs/paper-lean-specification.md) maps
each statement to its challenge name and library declaration.

## Gates

| Gate | State | Evidence or remaining obligation |
| --- | --- | --- |
| Build | CONTROLLER | `lake build` of `GeneralizedStafford` and `GeneralizedStaffordSolution` at the release commit. |
| Axiom audit | CONTROLLER | `scripts/verify.sh`: pins, build and `#print axioms` for every name in `docs/endpoints.txt` with `--trust=0`; only `propext`, `Classical.choice`, `Quot.sound`. |
| Palomar comparator | CONTROLLER | `scripts/verify-palomar.sh`: Comparator with NanoDa and the Lean kernel, sandboxed by Landrun; see [verification](docs/verification.md). The run of 2 November 2026 covered the 12 theorems solved then. |
| Statement faithfulness | PASS | Independent audit `review1` of the challenge: definitions, hypotheses, statements and the C.3 encoding PASS; readability REPAIR (renames and docstrings) applied without statement change. |
| Human review | OPEN | Agent audits are not human review. |
| Palomar registration | NOT DONE | Requires explicit human authorization ([runbook](docs/release-runbook.md)). |
| Release, DOI, visibility change | NOT DONE | Requires explicit human authorization. |

## Non-claims

The ordinal clause `delta(d) < Kdim R` of the manuscript's dimension lemma,
opposite-side statements (core Remark 6.5), Theorem D and the manuscript's
sections beyond `omega`, applications and examples are not formalized. C.3 is
stated through uniform dimensions; its identification with `rho` uses two
classical Goldie identities that are not formalized in the challenge.

## History

The Palomar layout replaced the earlier tree on 2 November 2026. The earlier
development (filtered and actual-symbol algebras, projective anchored width,
the first fixed-anchor package and its paper/Lean map) is preserved
unchanged on branch `archive/pre-palomar-2026-11-02` at
`7697e11786b4b20e28b6c727650d3cf036232969`. Its verification records apply to
that tree only.
