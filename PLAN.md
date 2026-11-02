# Generalized Stafford formal: live state

Updated: 2 November 2026. Private repository.

Status: 46 of 46 challenge theorems (14 abstract, 11 Weyl-algebra, 8 filtered-ring, 7 enveloping-algebra, 6 differential-operator applications) proved and verified at commit `fa98d22efe417b98d54d96902ab4d597bb5e0059` on branch `freeze` (2 November 2026; AlgebraicAnalysis pinned at `42dad436fcaf0fcd7f0e854ac5abe30825752158`; the later commit recording it changes no Lean file); gates below.

This file records the formal state only.

## Scope

The library formalizes Theorem A', Theorem A and Corollaries B, C.1, C.2 and
C.3, and their applications to the Weyl algebras `Aₙ(k)` in characteristic zero,
to simple algebras over an infinite field with a filtration whose associated
graded ring is commutative Noetherian of finite Krull dimension, to simple
quotients of enveloping algebras of finite-dimensional Lie algebras over an
infinite field, and to differential operators `D_k(A)` on
smooth affine domains in characteristic zero. The Palomar challenge
`GeneralizedStaffordChallenge.lean` (copy `Challenge.lean`) states the 46 compared theorems listed in `comparator.json`.

## Gates

| Gate | State | Evidence or remaining obligation |
| --- | --- | --- |
| Build | PASSED | `lake build` of `GeneralizedStafford` and `GeneralizedStaffordSolution` at the verified commit. |
| Axiom audit | PASSED (46 endpoint reports) | `scripts/verify.sh`: pins, build and `#print axioms` for every name in `docs/endpoints.txt` with `--trust=0`; only `propext`, `Classical.choice`, `Quot.sound`. |
| Palomar check (local replay) | PASSED (46 theorems) | `scripts/verify-palomar.sh`: accepted in a local replay of the Palomar check (Comparator with NanoDa and the Lean kernel; Landrun in best-effort mode); not registered on Palomar. See [verification](docs/verification.md). |
| Statement faithfulness | PASS | An independent statement-faithfulness audit (2 November 2026) passed; audited challenge sha256 `4cb2cd5e7a6043f4c38fecddb78850d6f8012048c91a7de7e188d18598dc9e95`. Definitions, hypotheses, statements and the C.3 encoding passed; readability repairs (renames and docstrings) were applied without statement change. Later challenge changes are name/docstring-only, confirmed by the final review of 2 November 2026. |
| Human review | OPEN | Agent audits are not human review. |
| Palomar registration | NOT DONE | Requires explicit human authorization ([runbook](docs/release-runbook.md)). |
| Release, DOI, visibility change | NOT DONE | Requires explicit human authorization. |

## Non-claims

The abstract theorems (A', A, B, C.1-C.3) are stated for right ideals and right
modules over a right Noetherian ring; no abstract left-sided form is stated.
Left-sided forms are stated for the applications: every filtered-ring and
enveloping-algebra statement holds for `R` and `Rᵐᵒᵖ`; for the Weyl algebras
and for `D_k(A)` the two-generation and cyclicity statements, and for `D_k(A)`
also Theorem A, have right and left forms. Not formalized: the ordinal refinement
`delta(d) < Kdim R` of the dimension part of Corollary B, results beyond
`omega`, and applications other than these four classes. C.3 is stated through
uniform dimensions; its identification with `rho` uses two classical Goldie
identities that are not formalized in the challenge.

## History

The Palomar layout replaced the earlier tree on 2 November 2026. The earlier
development (filtered and actual-symbol algebras, projective anchored width,
the first fixed-anchor package and its statement map) is preserved
unchanged on branch `archive/pre-palomar-2026-11-02` at
`7697e11786b4b20e28b6c727650d3cf036232969`. Its verification records apply to
that tree only.
