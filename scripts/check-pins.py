#!/usr/bin/env python3
"""Check dependency declarations against the reviewed release pin record."""
import json
import re
import tomllib
from pathlib import Path

record = json.loads(Path('dependency-pins.json').read_text())
if Path('lean-toolchain').read_text().strip() != record['lean_toolchain']:
    raise SystemExit('Lean toolchain pin mismatch')
requires = {r['name']: r for r in tomllib.loads(Path('lakefile.toml').read_text()).get('require', [])}
package_list = json.loads(Path('lake-manifest.json').read_text()).get('packages', [])
packages = {p['name']: p for p in package_list}
if len(package_list) != len(packages):
    raise SystemExit('manifest contains duplicate packages (Mathlib must be shared)')
if set(requires) != {'mathlib', 'algebraicAnalysis'}:
    raise SystemExit('expected direct Mathlib and AlgebraicAnalysis dependencies')
if set(requires) != set(record['packages']):
    raise SystemExit('direct dependency names differ from reviewed pin record')
for name, expected in record['packages'].items():
    url, rev = expected['url'], expected['revision']
    if not re.fullmatch('[0-9a-f]{40}', rev):
        raise SystemExit(f'{name}: revision is not a full commit')
    req, pkg = requires[name], packages.get(name, {})
    if req.get('git') != url or req.get('rev') != rev:
        raise SystemExit(f'{name}: lakefile pin mismatch')
    if pkg.get('rev') != rev or pkg.get('inputRev') != rev or pkg.get('url') != url:
        raise SystemExit(f'{name}: manifest pin mismatch')
mathlib_manifest = json.loads(Path('.lake/packages/mathlib/lake-manifest.json').read_text())
closure = {p['name']: p for p in mathlib_manifest.get('packages', [])}
if set(packages) != set(requires) | set(closure):
    raise SystemExit('manifest is not exactly the direct dependencies and Mathlib closure')
for name, expected in closure.items():
    if any(packages[name].get(key) != expected.get(key) for key in ('type', 'url', 'rev')):
        raise SystemExit(f'{name}: release manifest differs from pinned Mathlib dependency closure')
upstream = Path('.lake/packages/algebraicAnalysis')
if (upstream / 'lean-toolchain').read_text().strip() != record['lean_toolchain']:
    raise SystemExit('AlgebraicAnalysis Lean toolchain differs')
upstream_requires = tomllib.loads((upstream / 'lakefile.toml').read_text())['require']
if len(upstream_requires) != 1 or upstream_requires[0]['name'] != 'mathlib':
    raise SystemExit('unexpected AlgebraicAnalysis direct dependency closure')
shared = upstream_requires[0]
if (shared['git'].removesuffix('.git') != record['packages']['mathlib']['url']
        or shared['rev'] != record['packages']['mathlib']['revision']):
    raise SystemExit('AlgebraicAnalysis must use the same pinned Mathlib')
upstream_packages = json.loads((upstream / 'lake-manifest.json').read_text())['packages']
if {p['name'] for p in upstream_packages} != {'mathlib'} | set(closure):
    raise SystemExit('unexpected AlgebraicAnalysis manifest closure')
for pkg in upstream_packages:
    shared = packages[pkg['name']]
    if (pkg['type'] != shared['type'] or pkg['rev'] != shared['rev']
            or pkg['url'].removesuffix('.git') != shared['url'].removesuffix('.git')):
        raise SystemExit(f'{pkg["name"]}: AlgebraicAnalysis manifest closure differs')
print(f'pins: exact Lean, AlgebraicAnalysis, ONE shared Mathlib and {len(closure)} transitive dependencies')
