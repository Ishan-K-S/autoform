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
# `export_ast.sc`'s own comments are full of real prose punctuation (em-dashes,
# curly quotes). Joern's C frontend does not need a locale to run correctly,
# but the JVM's OWN source-file reads (compiling the script itself, and a
# separate "scan every .sc file for `using` directives" classpath step) fall
# back to the PLATFORM DEFAULT charset when none is set -- which is plain
# ASCII/POSIX on a bare container with no locale configured, Colab's own
# default runtime included. Reading any non-ASCII byte under that charset
# throws mid-file, corrupting the compiler's own view of everything after it
# and surfacing as a cascade of unrelated "Not found" errors from that point
# to the end of the file -- not a hint that anything in the source itself is
# wrong. Confirmed live: identical failure, same two line numbers, across
# four completely unrelated fixtures, on a Colab runtime that reproduced it
# after this session's own local sandbox (once it hit the identical failure
# earlier) could not, purely because the sandbox's own commands had been
# carrying `LANG=C.UTF-8` explicitly ever since -- a workaround on the
# CALLER's side, never fixed here, where every actual invocation needs it.
export LANG="${LANG:-C.UTF-8}"
export LC_ALL="${LC_ALL:-C.UTF-8}"
export JAVA_TOOL_OPTIONS="${JAVA_TOOL_OPTIONS:-} -Dfile.encoding=UTF-8"
cd "$ROOT"

# `009-reduce-remaining-holes-4`: `cartographer/run.sh`'s own `CPP_DEFINES`
# mechanism, ported here so `autoform.sh` (the pipeline this whole feature's
# own local sandbox testing runs, and what `notebooks/*.ipynb`'s
# `run_one_background` calls for the FULL corpus) has the SAME capability
# `run_one_chunked_background`'s own separate, inline joern-parse call
# already had -- this script had simply never been given it. For a C/C++
# tree, set CPP_DEFINES to a comma-separated list of names Joern's C frontend
# (which does not run the real preprocessor) should treat as defined --
# either bare (`SQLITE_TEST`, an `#ifdef`-guarded feature flag: without it,
# guarded code parses with its raw `.code` kept but ZERO ast children,
# reported honestly as `stmt:empty-ast-children`) or `NAME=VALUE` (a plain
# macro TOKEN substitution: `ALIGN128=`, `SQLITE_API=`, `SQLITE_EXTERN=extern`
# -- SQLite's own attribute/linkage macros, which the frontend cannot resolve
# at all without preprocessing and gives up on entirely, reported as
# `stmt:UNKNOWN:CASTProblemDeclaration`; a DIFFERENT failure mode from the
# `#ifdef` case, needing a value substitution rather than a bare presence
# flag). Empty by default: no behavior change for a codebase this does not
# apply to, or when the caller does not set it.
FRONTEND_ARGS=()
if [ -n "${CPP_DEFINES:-}" ]; then
  FRONTEND_ARGS+=(--frontend-args)
  IFS=',' read -ra CPP_DEFINE_NAMES <<< "$CPP_DEFINES"
  for name in "${CPP_DEFINE_NAMES[@]}"; do
    FRONTEND_ARGS+=(--define "$name")
  done
fi

echo "==> [1/6] parsing $SRC"
"$JOERN/joern-parse" "$SRC" --output "$WORK/cpg.bin" "${FRONTEND_ARGS[@]}" >/dev/null 2>&1

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
