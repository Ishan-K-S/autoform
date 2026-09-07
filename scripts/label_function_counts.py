#!/usr/bin/env python3
"""For each hole label, how many DISTINCT FUNCTIONS carry it -- not just how many
occurrences exist. holesByLabel (the Lean-produced ledger's own field, `Program.
ledgerJson` in Autoform/Ledger.lean) counts occurrences: a label with 500 occurrences
concentrated in 3 functions (a big switch/goto cluster, say) and a label with 500
occurrences spread across 400 functions look IDENTICAL under that count, but fixing
the first helps 3 functions and fixing the second helps up to 400 -- occurrence count
alone cannot tell them apart, and picking the next thing to fix by that number alone
systematically favors already-concentrated, low-value labels.

Reads the SAME `ast-<Module>.json` `autoform.sh`/`run_one_background` already save at
the repo root (no new CPG walk, no re-running the pipeline) and produces, per label,
both `occurrences` and `functions` -- the second is what a "how many functions would
this unblock, at most" question actually needs. `functions` is an upper bound on the
gain from fixing that ONE label: a function carrying that label AND others stays
holing regardless.

Usage:
    python3 scripts/label_function_counts.py ast-Sqlite.json
    python3 scripts/label_function_counts.py ast-Sqlite.json --merge-into ledger-Sqlite.json

With --merge-into, writes the result into that ledger JSON's own
"holesByLabelFunctionCount" field (creating it if absent) and rewrites the file in
place -- the same file `load_ledger()`/the notebook's own pipeline already produces,
so the merged field survives a normal `load_ledger(...)` call with no extra step.
"""
import json
import sys


def walk_holes(node, out):
    """Collect (label, kind) pairs the same way scripts/sacm.py's own walk_holes does --
    kept as an independent, minimal copy rather than importing sacm.py, since this
    script has no other dependency on it and duplicating ~10 lines is cheaper than a
    cross-script import contract."""
    if isinstance(node, dict):
        if node.get("k") in ("hole", "holeS"):
            out.append(node.get("label", "<unlabelled>"))
        for v in node.values():
            walk_holes(v, out)
    elif isinstance(node, list):
        for item in node:
            walk_holes(item, out)


def label_function_counts(ast):
    """-> {label: {"occurrences": int, "functions": int}}"""
    occurrences = {}
    functions = {}
    for fn in ast:
        found = []
        walk_holes(fn.get("body"), found)
        for label in found:
            occurrences[label] = occurrences.get(label, 0) + 1
        for label in set(found):
            functions[label] = functions.get(label, 0) + 1
    return {
        label: {"occurrences": occurrences[label], "functions": functions[label]}
        for label in occurrences
    }


def main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 1
    ast_path = argv[1]
    merge_into = None
    if "--merge-into" in argv:
        merge_into = argv[argv.index("--merge-into") + 1]

    ast = json.load(open(ast_path))
    counts = label_function_counts(ast)

    ranked = sorted(counts.items(), key=lambda kv: -kv[1]["functions"])
    print(f"{'label':45s} {'occ':>6s} {'fns':>6s} {'occ/fn':>7s}")
    for label, c in ranked:
        ratio = c["occurrences"] / c["functions"]
        print(f"{label:45s} {c['occurrences']:6d} {c['functions']:6d} {ratio:7.2f}")

    if merge_into:
        ledger = json.load(open(merge_into))
        ledger["holesByLabelFunctionCount"] = counts
        json.dump(ledger, open(merge_into, "w"), indent=2)
        print(f"\nmerged into {merge_into} as \"holesByLabelFunctionCount\"")

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
