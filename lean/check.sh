#!/bin/sh
# Reuse a populated Lake project's compiled packages; do not invoke Lake or fetch anything.
set -eu

if [ "$#" -ne 1 ]; then
  echo "Usage: sh check.sh /absolute/path/to/existing-lean-project" >&2
  exit 2
fi

reuse_project=$1
source_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
project_dir=$(CDPATH= cd -- "$source_dir/.." && pwd)
python3 "$project_dir/scripts/check_sources.py" --reuse "$reuse_project"
IFS= read -r reuse_toolchain < "$project_dir/lean-toolchain"
reuse_paths=
for reuse_package in "$reuse_project"/.lake/packages/*; do
  reuse_lib="$reuse_package/.lake/build/lib/lean"
  if [ -d "$reuse_lib" ]; then
    reuse_paths="${reuse_paths:+$reuse_paths:}$reuse_lib"
  fi
done
if [ ! -f "$reuse_project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ]; then
  echo "The supplied project needs an already compiled Mathlib installation." >&2
  exit 2
fi

build_dir="$source_dir/.build"
mkdir -p "$build_dir"
export LEAN_PATH="$build_dir:$reuse_paths"
cd "$source_dir"
# Omitting Elan's --install flag makes a missing toolchain an error, not a download.
for source_module in $(awk '/^import / {print $2}' CurveSymmetry.lean) CurveSymmetry; do
  elan run "$reuse_toolchain" lean -DwarningAsError=true \
    -o "$build_dir/$source_module.olean" "$source_module.lean"
done
elan run "$reuse_toolchain" lean -DwarningAsError=true "$project_dir/verification/Audit.lean"
