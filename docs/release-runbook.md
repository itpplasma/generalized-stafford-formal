# Release runbook

Agents prepare; humans decide and execute. Each action below needs explicit
authorization from Christopher Albert, given for that action.

## Human-only actions

| Action | State |
| --- | --- |
| Change repository visibility (private to public) | done 2 November 2026 (authorized by Christopher Albert) |
| Create a tag or GitHub release | not done |
| Archive on Zenodo and mint a DOI | not done |
| Register on Palomar | not done |
| Submit the write-up for publication or contact anyone external | not done |
| Add an author | not done |

## Before any of these actions

1. Fix the target commit on `main`. The reviewed work is on branch
   `palomar`; the target commit is on `main` after the controller
   fast-forwards `main` to the reviewed `palomar` head. Confirm the gates in
   `PLAN.md`: build, axiom audit and the local replay of the Palomar check
   passed at that commit; statement faithfulness audited for the current
   challenge bytes.
2. If Lean sources, pins, challenge or solution bytes, `comparator.json` or the
   verifier scripts changed since the recorded run, rerun `scripts/verify.sh`
   and `scripts/verify-palomar.sh` and record the new run in
   `docs/verification.md`. A changed challenge also needs a new
   statement-faithfulness audit.
3. Fill the `verification` block of `formalization.yaml` (commit, allowed
   axioms) and, for a release, add version, date and DOI to `CITATION.cff`.
   Keep `registration_status` accurate.
4. Check README, PLAN, `formalization.yaml` and `CITATION.cff` for the same
   status, pins and wording.
5. Check that AlgebraicAnalysis is reachable at the pinned revision for anyone
   who will build the release.

## Palomar submission

Palomar compares `GeneralizedStaffordChallenge` with
`GeneralizedStaffordSolution` using `comparator.json`. The local replay is
`scripts/verify-palomar.sh`; [verification.md](verification.md) records the
tool revisions and the sandbox limits of the last run. A Palomar record is
separate from a GitHub release, a DOI, human review and journal publication.

## Wording

Describe the work as a formalization of the stated theorems with
machine-checked proofs. Do not claim novelty or priority. Do not describe agent
audits as human review. State that human review is pending until it is done.
