#!/usr/bin/env bash
# autoform — point at any codebase Joern can parse, get Lean.
#
#   ./autoform.sh <source-dir> [ModuleName]
#
#   source ──Joern──▶ CPG ──▶ neutral JSON AST ──▶ Lean Core program ──▶ ledger
#                      │                                    │
#                      └─▶ formalization graph              └─▶ differential vs runtime
#
# The CPG is the universal front end: C/C++/Java/JavaScript/Python/Kotlin/binaries all
# normalize to one node vocabulary, so one semantics and one exporter cover all of them.
set -euo pipefail

SRC="${1:?usage: autoform.sh <source-dir> [ModuleName]}"
MOD="${2:-Translated}"
ROOT="$(cd "$(dirname "$0")" && pwd)"
JOERN="${JOERN_HOME:-$HOME/joern}/joern-cli"
WORK="$(mktemp -d)"
# Unconditional cleanup: `set -e` means any failing stage below (a `lake build`
# hitting a heartbeat/recDepth limit, an unresolved codebase, ...) exits the
# script immediately, and a plain trailing `rm -rf` at the bottom of the file is
# never reached on that path. Every failed run used to leak `$WORK`'s full CPG
# binary + exported AST JSON (measured on a real SQLite attempt: ~100-200 MB per
# leaked run) and Joern's own project cache under `$ROOT/workspace` forever.
trap 'rm -rf "$WORK" "$ROOT/workspace"' EXIT
export PATH="$HOME/.elan/bin:$PATH"
cd "$ROOT"

echo "==> [1/6] parsing $SRC"
"$JOERN/joern-parse" "$SRC" --output "$WORK/cpg.bin" >/dev/null 2>&1

echo "==> [2/6] cartographer: formalization graph"
"$JOERN/joern" --script "$ROOT/cartographer/formalization_graph.sc" \
  --param cpgPath="$WORK/cpg.bin" --param out="$ROOT/formalization-graph.json" 2>&1 \
  | grep -E "^wrote|^pure" || true

echo "==> [3/6] transpiler: CPG -> neutral AST"
EXPORT_OUT="$("$JOERN/joern" --script "$ROOT/cartographer/export_ast.sc" \
  --param cpgPath="$WORK/cpg.bin" --param out="$WORK/ast.json" 2>&1)" && EXPORT_STATUS=0 || EXPORT_STATUS=$?
if [ "$EXPORT_STATUS" -ne 0 ] || ! grep -qE "^exported" <<<"$EXPORT_OUT"; then
  echo "$EXPORT_OUT" >&2
  echo "==> [3/6] FAILED: export_ast.sc did not report success (see output above)" >&2
  exit 1
fi
grep -E "^exported" <<<"$EXPORT_OUT"
cp "$WORK/ast.json" "$ROOT/ast-$MOD.json"

echo "==> [4/6] rendering Lean"
python3 "$ROOT/cartographer/render_lean.py" "$WORK/ast.json" \
  "$ROOT/Autoform/Generated/$MOD.lean" "$MOD"

echo "==> [5/6] type-checking generated Lean"
lake build "Autoform.Generated.$MOD"

echo "==> [6/6] differential conformance vs the real runtime"
python3 "$ROOT/scripts/differential.py" "$WORK/ast.json" "$SRC" "$MOD" 5 || true

sed "s/@MODULE@/$MOD/g" "$ROOT/scripts/ledger.lean.tmpl" > "$WORK/Ledger.lean"
lake env lean "$WORK/Ledger.lean"
