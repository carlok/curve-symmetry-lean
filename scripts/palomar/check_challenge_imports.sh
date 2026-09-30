#!/bin/sh
# Pre-check only, NOT the Palomar Comparator: the Challenge may import Mathlib
# (the whole library or its modules) and nothing else. Any other import line,
# including one with several modules or a trailing comment, is rejected.
# Usage: sh check_challenge_imports.sh [Challenge.lean]
set -eu
file=${1:-Challenge.lean}
imports=$(grep -E '^[[:space:]]*((public|private|meta)[[:space:]]+)*import[[:space:]]' "$file" || true)
if [ -z "$imports" ]; then
  echo "No import found in $file" >&2
  exit 1
fi
bad=$(printf '%s\n' "$imports" | grep -vE '^import Mathlib(\.[A-Za-z0-9_.]+)?[[:space:]]*$' || true)
if [ -n "$bad" ]; then
  echo "Forbidden Challenge import(s) in $file:" >&2
  printf '%s\n' "$bad" >&2
  exit 1
fi
echo "Challenge imports only Mathlib: $(printf '%s\n' "$imports" | tr '\n' ' ')"
