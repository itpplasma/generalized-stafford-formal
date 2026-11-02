# Generalized Stafford formal: live state

Updated: 2 November 2026. Private repository.

Status: 33 of 33 challenge theorems (14 abstract, 11 Weyl-algebra, 8 filtered-ring applications) proved and verified at commit `ff27d2a9adb2` (2 November 2026; the Lean sources are those of that commit, and the later commit recording it changes no Lean file); gates below.

This file records the formal state only.

## Scope

The library formalizes Theorem A', Theorem A and Corollaries B, C.1, C.2 and
C.3. The Palomar challenge `GeneralizedStaffordChallenge.lean` (copy
`Challenge.lean`) states the 33 compared theorems listed in `comparator.json`.

## Gates

| Gate | State | Evidence or remaining obligation |
| --- | --- | --- |
| Build | PASSED | `lake build` of `GeneralizedStafford` and `GeneralizedStaffordSolution` at the release commit. |
| Axiom audit | PASSED (46 endpoint reports) | `scripts/verify.sh`: pins, build and `#print axioms` for every name in `docs/endpoints.txt` with `--trust=0`; only `propext`, `Classical.choice`, `Quot.sound`. |
| Palomar check (local replay) | PASSED (33 theorems) | `scripts/verify-palomar.sh`: accepted in a local replay of the Palomar check (Comparator with NanoDa and the Lean kernel; Landrun in best-effort mode); not registered on Palomar. See [verification](docs/verification.md). |
| Statement faithfulness | PASS | An independent statement-faithfulness audit (2 November 2026) passed; audited challenge sha256 `4cb2cd5e7a6043f4c38fecddb78850d6f8012048c91a7de7e188d18598dc9e95`. Definitions, hypotheses, statements and the C.3 encoding passed; readability repairs (renames and docstrings) were applied without statement change. Later challenge changes are name/docstring-only, confirmed by the final review of 2 November 2026. |
| Human review | OPEN | Agent audits are not human review. |
| Palomar registration | NOT DONE | Requires explicit human authorization ([runbook](docs/release-runbook.md)). |
| Release, DOI, visibility change | NOT DONE | Requires explicit human authorization. |

## Pending

- Move the application-independent section *Auxiliary module theory (to be
  upstreamed to AlgebraicAnalysis)* of `GeneralizedStafford/GeneratorBounds.lean`
  to AlgebraicAnalysis, following its rules, and re-pin.

## Non-claims

The ordinal refinement `delta(d) < Kdim R` of the dimension part of Corollary B,
opposite-side statements, results beyond `omega`, applications and examples are
not formalized. C.3 is
stated through uniform dimensions; its identification with `rho` uses two
classical Goldie identities that are not formalized in the challenge.

## History

The Palomar layout replaced the earlier tree on 2 November 2026. The earlier
development (filtered and actual-symbol algebras, projective anchored width,
the first fixed-anchor package and its statement map) is preserved
unchanged on branch `archive/pre-palomar-2026-11-02` at
`7697e11786b4b20e28b6c727650d3cf036232969`. Its verification records apply to
that tree only.
