# Agent rules: generalized-stafford-formal

This repository owns the Lean 4 formalization of Theorem A', Theorem A and
Corollaries B, C.1 and C.2, and their Palomar interface. `PLAN.md` is the only
live status document; read it before any edit. The written proof lives in the
written proof is kept outside this repository. Nothing here imports it or
needs it to build or verify.

## Non-negotiable rules

- `Challenge.lean` and `GeneralizedStaffordChallenge.lean` are frozen and
  byte-identical. They import only Mathlib, define everything inline, and
  contain exactly one deliberate `sorry` per compared theorem. A statement
  change needs a new statement-faithfulness audit and explicit human approval.
- `Solution.lean` and `GeneralizedStaffordSolution.lean` are byte-identical,
  never import the challenge, and prove theorems with the challenge's exact
  names and types. `comparator.json` lists exactly those theorems.
- No `axiom` declarations, no `sorry` outside the challenge files, no
  `native_decide`, `Lean.ofReduceBool`, `unsafe` or `implemented_by`. The
  permitted axioms are `propext`, `Quot.sound` and `Classical.choice`.
- Keep the noncommutative order and sidedness. Right modules are
  `[Module Rᵐᵒᵖ M]`, right ideals are `Submodule Rᵐᵒᵖ R`, and `(B + H * a) * d * V`
  is never reordered.
- Pins (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`,
  `dependency-pins.json`) change only by an explicit task. Never run
  `lake update`. A bump requires a full rebuild, `scripts/verify.sh` and
  `scripts/verify-palomar.sh`.
- Reusable, application-independent mathematics belongs in AlgebraicAnalysis,
  following its rules. Do not duplicate its declarations here.
- Tests need an independent oracle (a consumer with `#print axioms`, or a
  concrete computation), not a restatement of the patch.
- Keep `.lake`, caches, logs and scratch untracked.

## Style

- Namespace `GeneralizedStafford`; one file per topic (conventions, germs,
  descent, theorems, corollaries).
- Each module docstring names the statements it proves. Corollary files give
  the proof idea in a few sentences, because they are read as the proofs of
  their corollaries.
- Every public declaration has a docstring in plain mathematical English with
  the standard notation (`d, a, B, H, U, V, I, x, t`). In the library, (S) and
  (N) are instance arguments (`[IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]`) and
  (Z) is an infinite central field `k` with `[Field k] [Infinite k]
  [Algebra k R]`. Named hypotheses: `hreg` (a regular
  element), `hfin` (finite deviation), `homega` (`Kdim R ≤ ω`) and `hall`
  ((H_all)).
- Mathlib naming and sidedness conventions. `#print axioms` lines belong in
  tests and verifier scripts, not in library files.

## Claims

- Keep separate: kernel verification, statement faithfulness, written proof,
  human review, literature attribution and publication. One does not imply
  another.
- Make no novelty or priority claim. Absence from the literature searched is
  not originality. Attribute imported classical arguments.

## Publication policy

No visibility change, tag, release, DOI, Palomar registration or journal
submission without explicit human authorization. No person may be contacted
and no author added without it. `docs/release-runbook.md` lists these human
actions; agents prepare, humans execute.
