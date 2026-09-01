#!/usr/bin/env bash
# Cartographer driver: source tree -> code property graph -> formalization graph.
#
# Usage: cartographer/run.sh <source-dir> [output.json]
#
# For a C/C++ tree with conditional compilation (`#ifdef PLATFORM_X`), set
# CPP_DEFINES to a comma-separated list of names the real build would define,
# e.g. `CPP_DEFINES=SQLITE_OS_UNIX cartographer/run.sh sqlite/src`. Joern's C
# frontend does not run the preprocessor: a name that stays undefined leaves
# every function it guards with its raw source still on `.code` but ZERO ast
# children, which export_ast.sc's `stmt` now reports as an honest
# `stmt:empty-ast-children` hole rather than silently exporting `skip`.
set -euo pipefail

SRC="${1:?usage: run.sh <source-dir> [out.json]}"
OUT="${2:-formalization-graph.json}"
JOERN="${JOERN_HOME:-$HOME/joern}/joern-cli"
WORK="$(mktemp -d)"

FRONTEND_ARGS=()
if [ -n "${CPP_DEFINES:-}" ]; then
  FRONTEND_ARGS+=(--frontend-args)
  IFS=',' read -ra NAMES <<< "$CPP_DEFINES"
  for name in "${NAMES[@]}"; do
    FRONTEND_ARGS+=(--define "$name")
  done
fi

"$JOERN/joern-parse" "$SRC" --output "$WORK/cpg.bin" "${FRONTEND_ARGS[@]}"
"$JOERN/joern" --script "$(dirname "$0")/formalization_graph.sc" \
  --param cpgPath="$WORK/cpg.bin" --param out="$OUT"

echo "formalization graph -> $OUT"
