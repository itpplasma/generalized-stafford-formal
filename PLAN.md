# Generalized Stafford formal: live state

Updated: 2 November 2026. Private repository.

Status: 41 of 41 challenge theorems (13 abstract, 11 Weyl-algebra, 6 filtered-ring, 5 enveloping-algebra, 6 differential-operator applications) proved and verified on branch `paper-scope` at commit `7f225191531b4e766b2f42992714b1d30b2e3494` (2 November 2026; AlgebraicAnalysis pinned at `22b3946c0cfc13960cd238319acea76ae0d5f168`). The challenge now states exactly the numbered results of the paper; the earlier 46-theorem freeze `17f84e3bc693b309f40dc5c75a901ec891214bf0` is superseded, and a new freeze waits for the statement-faithfulness audit of the reduced challenge; gates below.

This file records the formal state only.

## Scope

The library formalizes Theorem A', Theorem A and Corollaries B, C.1 and C.2,
and their applications to the Weyl algebras `Aₙ(k)` in characteristic zero,
to simple algebras over an infinite field with a filtration whose associated
graded ring is commutative Noetherian of finite Krull dimension, to simple
quotients of enveloping algebras of finite-dimensional Lie algebras over an
infinite field, and to differential operators `D_k(A)` on
smooth affine domains in characteristic zero. The Palomar challenge
`GeneralizedStaffordChallenge.lean` (copy `Challenge.lean`) states the 41 compared theorems listed in `comparator.json`: one or more for each numbered result of the paper, and `knownDimension_hAll_of_omega`, the cited input of Corollary B.
The paper no longer states Corollary C.3 (generator bounds) or the dimension
fact "`Kdim R <= omega` implies `Kdim(R/dR)` finite" (it cites McConnell-Robson
6.3.9); the seven compared theorems for them were removed with the C.3 library
module. The dimension fact stays proved in `GeneralizedStafford/CorollaryB.lean`
because Corollary B uses it, and the challenge states it in the form (H_omega) implies (H_all).

## Gates

| Gate | State | Evidence or remaining obligation |
| --- | --- | --- |
| Build | PASSED | `lake build` of `GeneralizedStafford` and `GeneralizedStaffordSolution` at the verified commit. |
| Axiom audit | PASSED (81 endpoint reports) | `scripts/verify.sh`: pins, build and `#print axioms` for every name in `docs/endpoints.txt` with `--trust=0`; only `propext`, `Classical.choice`, `Quot.sound`. |
| Palomar check (local replay) | PASSED (41 theorems) | `scripts/verify-palomar.sh`: accepted in a local replay of the Palomar check (Comparator with NanoDa and the Lean kernel; Landrun in best-effort mode); not registered on Palomar. See [verification](docs/verification.md). |
| Statement faithfulness | OPEN | The reduced challenge (sha256 `778588a0d79f7216ce1e416159ad53092a38aa172dcdf095505dc4764be9890a`) needs an independent statement-faithfulness audit. Its 41 statements are those of the earlier challenge except the new `corollaryC2_omega` (the omega case of C.2, stated in the paper's Corollary C) and `knownDimension_hAll_of_omega` (McConnell-Robson 6.3.9, cited input of Corollary B); the audit of 2 November 2026 (sha256 `4cb2cd5e7a6043f4c38fecddb78850d6f8012048c91a7de7e188d18598dc9e95`) covered that earlier 46-theorem file and does not by itself certify the reduced one. |
| Human review | OPEN | Agent audits are not human review. |
| Palomar registration | NOT DONE | Requires explicit human authorization ([runbook](docs/release-runbook.md)). |
| Release, DOI, visibility change | NOT DONE | Requires explicit human authorization. |

## Non-claims

The abstract theorems (A', A, B, C.1, C.2) are stated for right ideals and right
modules over a right Noetherian ring; no abstract left-sided form is stated.
Left-sided forms are stated for the applications: every filtered-ring and
enveloping-algebra statement holds for `R` and `Rᵐᵒᵖ`; for the Weyl algebras
and for `D_k(A)` the two-generation and cyclicity statements, and for `D_k(A)`
also Theorem A, have right and left forms. Not formalized: the ordinal refinement
`delta(d) < Kdim R`, results beyond `omega`, Corollary C.3 (removed from the
paper; its proof is at commit `17f84e3`), and applications
other than these four classes.

## History

The Palomar layout replaced the earlier tree on 2 November 2026. The earlier
development (filtered and actual-symbol algebras, projective anchored width,
the first fixed-anchor package and its statement map) is preserved
unchanged on branch `archive/pre-palomar-2026-11-02` at
`7697e11786b4b20e28b6c727650d3cf036232969`. Its verification records apply to
that tree only.
