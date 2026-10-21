# Agent guidance

- Work on `main`, as requested by Chris. Use English; preserve unrelated work.
- `PLAN.md` owns formal work status. The mathematical research authority is
  `itpplasma/generalized-stafford/PLAN.md`; its proof dossier and dependency
  tree must precede new theorem development or promotion.
- This is an imported experimental Lean development. Predecessor verification
  is evidence, not a replay of this renamed tree or a semantic proof audit.
- Do not add `sorry`, custom axioms, `native_decide`, or source-selection
  hypotheses assuming the conclusion. Preserve right multiplication order.
- Preserve exact Lean/Mathlib pins and upstream LICENSE/NOTICE/provenance.
  A bump requires a full rebuild and endpoint axiom audit.
- Run `scripts/verify.sh` after proof changes. It requires Python >=3.11;
  select the interpreter with `PYTHON` when necessary.
- Keep `.lake`, caches, logs and scratch untracked. This repository is private:
  no heavy GitHub Actions CI. Native verification runs locally.
- `docs/proof-map.md` is a candidate declaration map, not established
  whole-proof correspondence. Do not label missing concrete adapters complete.
- Distinguish build/axiom evidence, statement review, written proof, applications,
  literature attribution, human review and publication. No release is implied.
