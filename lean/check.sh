#!/bin/sh
# Reuse a populated Lake project's compiled packages; do not invoke Lake or fetch anything.
set -eu

if [ "$#" -ne 1 ]; then
  echo "Usage: sh check.sh /absolute/path/to/existing-lean-project" >&2
  exit 2
fi

reuse_project=$1
IFS= read -r reuse_toolchain < "$reuse_project/lean-toolchain"
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

source_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build_dir="$source_dir/.build"
mkdir -p "$build_dir"
export LEAN_PATH="$build_dir:$reuse_paths"
cd "$source_dir"
# Omitting Elan's --install flag makes a missing toolchain an error, not a download.
for source_module in RotationSupport Irreducibility RealLocus Elimination GeometricRotation RotationGroup Translation EuclideanCenter ChangeCenter DirectBound Reflection EuclideanParameters ReflectionBound FamilyQuadratic Blowup FamilyIrreducibility FamilyRealLocus FamilyRotations Fermat Sharpness RealEquation EqualityForm Normalization ExtremalClassification IsometryInterface CartesianCoordinates CartesianReal CartesianDescent DirectIsometries PaperBounds FamilySingularities FamilyCharts FamilyTransport; do
  elan run "$reuse_toolchain" lean -DwarningAsError=true \
    -o "$build_dir/$source_module.olean" "$source_module.lean"
done
