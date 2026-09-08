#!/usr/bin/env python3
"""For each hole label, how many functions would become FULLY hole-free if that ONE
label were fixed -- not merely how many functions contain it somewhere.

The earlier version of this script counted "how many functions carry this label at
all," which sounded like the same "how many functions would this unblock" question
but silently wasn't: a function that carries the label ALONGSIDE nine others stays
holing regardless of what happens to this one label, yet still added to that count --
diluting every label's number with credit it cannot actually deliver on its own, and
in practice made two very differently-productive labels (fixing one clears a function
outright; fixing the other barely dents it) look equally worth chasing. Confirmed
live this session: fixing `op:cast:pointer:int-to-pointer` in several already-messy
functions (`exprAnalyze`, `sqlite3_randomness`) removed the label but left hole-free
completely unchanged, because each function had unrelated holes of its own the whole
time -- the OLD count had no way to say that in advance.

`onlyFunctions` answers the sharper question directly: a function counts for a label
ONLY when that label is the function's ENTIRE hole set (one or more OCCURRENCES of
it, zero of anything else) -- i.e. fixing this one label, and nothing else, is
sufficient to move that function into the hole-free column. Ranking labels by this
number instead of raw occurrence count or "touches" points at the next fix that
actually pays off in hole-free functions, not just in shrinking a hole tally.

Reads the SAME `ast-<Module>.json` `autoform.sh`/`run_one_background` already save at
the repo root (no new CPG walk, no re-running the pipeline).

Usage:
    python3 scripts/label_function_counts.py ast-Sqlite.json
    python3 scripts/label_function_counts.py ast-Sqlite.json --merge-into ledger-Sqlite.json

With --merge-into, writes the result into that ledger JSON's own
"holesByLabelOnlyFunctionCount" field (creating it if absent) and rewrites the file
in place -- the same file `load_ledger()`/the notebook's own pipeline already
produces, so the merged field survives a normal `load_ledger(...)` call with no extra
step.
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
    """-> {label: {"occurrences": int, "onlyFunctions": int}}

    `occurrences`: total occurrence count of the label across the corpus (unchanged
    from before -- still the right number for "how big is this problem raw").

    `onlyFunctions`: number of functions whose distinct hole-label SET is exactly
    `{label}` -- fixing this one label is both necessary and SUFFICIENT to make that
    function hole-free. A function with two occurrences of the same label but no
    other label still counts once here; a function with this label plus even one
    occurrence of any other label counts zero, for every label it carries."""
    occurrences = {}
    only_functions = {}
    for fn in ast:
        found = []
        walk_holes(fn.get("body"), found)
        for label in found:
            occurrences[label] = occurrences.get(label, 0) + 1
        distinct = set(found)
        if len(distinct) == 1:
            sole_label = next(iter(distinct))
            only_functions[sole_label] = only_functions.get(sole_label, 0) + 1
    return {
        label: {"occurrences": occurrences[label], "onlyFunctions": only_functions.get(label, 0)}
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

    ranked = sorted(counts.items(), key=lambda kv: -kv[1]["onlyFunctions"])
    print(f"{'label':45s} {'occ':>6s} {'only':>6s}")
    for label, c in ranked:
        print(f"{label:45s} {c['occurrences']:6d} {c['onlyFunctions']:6d}")

    if merge_into:
        ledger = json.load(open(merge_into))
        ledger["holesByLabelOnlyFunctionCount"] = counts
        json.dump(ledger, open(merge_into, "w"), indent=2)
        print(f"\nmerged into {merge_into} as \"holesByLabelOnlyFunctionCount\"")

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
