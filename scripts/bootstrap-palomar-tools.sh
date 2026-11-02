#!/usr/bin/env bash
set -euo pipefail

CDPATH=
repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"

tool_root=.lake/palomar-tools
source_root=$tool_root/src
bin_root=$tool_root/bin
mkdir -p "$source_root" "$bin_root"

# Exact revisions for this project's Lean toolchain. Comparator and lean4export
# are the commits tagged v4.35.0-rc3 upstream (Comparator's lean-toolchain is
# v4.35.0-rc3 and its manifest pins lean4export 66f1fb4). NanoDa has no
# toolchain; 8de7e0c is the head of its default branch when this was pinned and
# reads the standard lean4export JSON format, which is unchanged between v4.33.0
# and v4.35.0-rc3 (only the partial-declaration filter changed). Landrun has no
# Lean dependency; 811cfff is on its main branch.
lean_toolchain=leanprover/lean4:v4.35.0-rc3
comparator_rev=fd5d5bcf14177b187f66d4502071268d877887c3
lean4export_rev=66f1fb4bc256072069767fce52d39480e4524869
nanoda_rev=8de7e0c4ed3052745a7f8725164efd9e76d84c56
landrun_rev=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4

checkout_exact() {
  name=$1
  url=$2
  revision=$3
  destination=$source_root/$name

  if [ ! -d "$destination/.git" ]; then
    rm -rf "$destination"
    git clone --filter=blob:none --no-checkout "$url" "$destination"
  fi
  git -C "$destination" remote set-url origin "$url"
  git -C "$destination" fetch --force --tags origin
  if ! git -C "$destination" cat-file -e "$revision^{commit}" 2>/dev/null; then
    git -C "$destination" fetch --force origin "$revision"
  fi
  git -C "$destination" checkout --detach --force "$revision"
  git -C "$destination" clean -ffdx
  actual=$(git -C "$destination" rev-parse HEAD)
  if [ "$actual" != "$revision" ]; then
    echo "$name resolved to $actual, expected $revision" >&2
    exit 1
  fi
}

checkout_exact comparator https://github.com/leanprover/comparator "$comparator_rev"
checkout_exact lean4export https://github.com/leanprover/lean4export "$lean4export_rev"
checkout_exact nanoda https://github.com/ammkrn/nanoda_lib "$nanoda_rev"
checkout_exact landrun https://github.com/zouuup/landrun "$landrun_rev"

(
  cd "$source_root/lean4export"
  ELAN_TOOLCHAIN=$lean_toolchain lake build lean4export
)
cp "$source_root/lean4export/.lake/build/bin/lean4export" "$bin_root/lean4export"

(
  cd "$source_root/comparator"
  # Comparator's own kernel API follows its pinned repository toolchain.
  # The exporter separately uses the submission's exact Lean toolchain.
  test "$(tr -d '\r\n' < lean-toolchain)" = "$lean_toolchain"
  ELAN_TOOLCHAIN=$lean_toolchain lake build comparator
)
cp "$source_root/comparator/.lake/build/bin/comparator" "$bin_root/comparator"

(
  cd "$source_root/nanoda"
  CARGO_INCREMENTAL=0 cargo build --locked --release --bin nanoda_bin
)
cp "$source_root/nanoda/target/release/nanoda_bin" "$bin_root/nanoda"

(
  cd "$source_root/landrun"
  CGO_ENABLED=0 go build -mod=readonly -trimpath -o "../../bin/landrun" ./cmd/landrun
)

for tool in comparator lean4export nanoda landrun; do
  test -x "$bin_root/$tool"
done

cat >"$tool_root/revisions.txt" <<EOF
Comparator $comparator_rev
ComparatorLean $lean_toolchain
lean4export $lean4export_rev
NanoDa $nanoda_rev
Landrun $landrun_rev
Lean $lean_toolchain
EOF

echo "Palomar tools built at $tool_root"
