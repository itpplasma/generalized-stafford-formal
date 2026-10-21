# Verification

Run `PYTHON=python3.14 ./scripts/verify.sh` with the pinned dependencies and
Python >=3.11. `PYTHON` defaults to `python3`. The verifier checks pins and
paper/Lean source identities, builds the library once, then runs declaration
ownership, statement and endpoint axiom audits with `--trust=0`. The current
project build directory comes first in `LEAN_PATH`.

Lean is pinned at v4.35.0-rc3 and Mathlib at
c55e6e786f49471c72fbddbec5415808896aec1e. All transitive pins are checked.
The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`;
missing endpoint reports or any other axiom fail verification.

## Evidence

The renamed library passed a full native replay at
d6a0eaba9dbef273a324fed8e0018728f92296db. After adding the full affine-left
endpoint, the full verifier passed again for all 19 endpoints. The three-file
proof/endpoint patch has SHA256
b4029a8847903d3177b1d14e1e1bca2d90bc82bcf298380c5a2f1f57924ff1b6.
The protected source fingerprints in [the map](paper-lean-map.json) identify
those exact proof inputs without a self-referential commit hash.

The map-only additions passed their static checks, rejected a synthetic
source mismatch and passed a generated Lean declaration-owner audit for all
40 mapped references. The full build was reused for those unchanged proof
sources. Logs and source-identity evidence remain under ignored
`.lake/verification/`.

The constructive-Weyl dossier update is pinned at
4c06c0bab51644daec6e6b881123319f3ac67d0b. Its refreshed map passes all
source and anchor checks. The generated owner audit is byte-identical to
the previous one and also passes `lean --trust=0`. No protected Lean or
dependency input changed, so the full proof build above is reused.
The new categorical and constructive results remain explicit omissions.

## Correspondence checks

The default map check reads immutable Git objects from the private research
checkout, by default `../generalized-stafford`. Set `PAPER_REPO` or pass
`--paper-root` to select another checkout containing the pinned commit.

```sh
python3.14 scripts/check-paper-lean-map.py
```

The checker verifies hashes, paper anchors, protected Lean coverage, map
references, dependency acyclicity and endpoint coverage. With `--lean-audit`
it emits a Lean file checking declaration existence and owning module; the
normal verifier runs that audit after building. It never refreshes the map
automatically. Changed protected sources require an explicit correspondence
review and map update.

`--formal-only` explicitly skips private paper Git-object/hash/anchor checks
and reports that limit; it is a checker option, not the full verifier's
default. Source identity and module ownership cannot prove that informal and
formal statements have the same meaning. The map records that mathematical
review separately, including partial statements and unformalized extensions.

No concrete geometric adapter, effective algorithm, literature originality,
human review or Palomar registration follows from these checks. Native
validation is local; this private repository has no heavy Actions workflow.
