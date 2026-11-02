# Generalized Stafford formal: live state

Updated: 2 November 2026. Private repository.

Status: 14 of 14 challenge theorems proved and verified at commit `2539e681d971` (2 November 2026); gates below.

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
| Build | PASSED | `lake build` of `GeneralizedStafford` and `GeneralizedStaffordSolution` at the release commit. |
| Axiom audit | PASSED (46 endpoint reports) | `scripts/verify.sh`: pins, build and `#print axioms` for every name in `docs/endpoints.txt` with `--trust=0`; only `propext`, `Classical.choice`, `Quot.sound`. |
| Palomar check (local replay) | PASSED (14 theorems) | `scripts/verify-palomar.sh`: accepted in a local replay of the Palomar check (Comparator with NanoDa and the Lean kernel; Landrun in best-effort mode); not registered on Palomar. See [verification](docs/verification.md). |
| Statement faithfulness | PASS | Independent audit, durable record `docs/lane-palomar-statement-audit.md` of the research repository at commit `1f05218` (frozen challenge sha256 `4cb2cd5e7a6043f4c38fecddb78850d6f8012048c91a7de7e188d18598dc9e95`): definitions, hypotheses, statements and the C.3 encoding PASS; readability REPAIR (renames and docstrings) applied without statement change. Later challenge changes are name/docstring-only, confirmed by the final review of 2 November 2026. |
| Human review | OPEN | Agent audits are not human review. |
| Palomar registration | NOT DONE | Requires explicit human authorization ([runbook](docs/release-runbook.md)). |
| Release, DOI, visibility change | NOT DONE | Requires explicit human authorization. |

## Pending

- Move the application-independent section *Auxiliary module theory (to be
  upstreamed to AlgebraicAnalysis)* of `GeneralizedStafford/GeneratorBounds.lean`
  to AlgebraicAnalysis, following its rules, and re-pin.

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
