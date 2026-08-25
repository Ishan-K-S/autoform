#!/usr/bin/env python3
"""check_specs_fresh.py — is each specification module still about the corpus it was
generated from?

A specification is a statement about a *specific rendering* of a corpus, not about the
project in the abstract. Closing a hole changes what the translated function computes, so
improving coverage can turn a true law false or a false law true. Specs do not rot
gracefully; they invert.

That is not hypothetical. It happened three times in one day:

  * `C_tfFree` asserted the cachetools context contains no `tryFinally`. The exporter
    learned to translate `try/finally`, the assertion became FALSE, and 72 fuel-transported
    laws that rested on it had to be demoted to obligations.
  * Fifteen V8 laws were recorded as refuted. They were evaluated against a module carrying
    55 `op:shiftLeft` holes; the current export has none. Seven of the fifteen are true
    against the current corpus, and the "refutation" described a program that no longer
    existed.
  * A cost of 11 GB was quoted as a property of the fuel transport. It was a property of the
    module layout, and moved by three orders of magnitude when the layout changed.

In every case the specs were internally consistent and the build was green. Nothing tied a
spec to the corpus version it was generated against, so nothing could notice.

This binds them. `artifact-manifest.json` gains a `specs` section recording, per spec
module, the `ast_sha256` of the corpus it was generated from. A mismatch means the specs
describe a program that is no longer the one in the tree — reported as STALE, with the
instruction to re-generate rather than to re-record.

Re-recording without re-generating is the failure mode to avoid: it makes the check agree
with whatever is there, which is a rubber stamp rather than a gate. `--record` therefore
prints what it is overwriting.

## Silence is not success

The check above needs a corpus hash it can *recompute from the tree*. It used to accept
three sources: the tracked `ast-<M>.json`, an `ast_hint` path, and — when both were absent
— `artifact-manifest.json`'s own `ast_sha256` field. That third source made the gate
vacuous. `corpus_ast_sha256` is also a manifest field, so on a fresh clone of the four
untracked corpora the gate compared the manifest against itself, agreed with itself, and
exited 0 without saying anything about the 74 tracked `SpecsGen/V8Base` spec files it was
supposed to be guarding. It was dark in CI in exactly the sense of §44.

The fallback is gone. A corpus hash now comes only from bytes on disk. When a spec module
is **tracked in git** and its corpus cannot be hashed from the tree, that is reported as
UNVERIFIABLE and exits 3 — the same verdict and the same exit code `check_render.py` uses
for the same situation. An untracked spec module with an absent corpus is a local build
product that legitimately does not exist in a fresh clone; it is reported as SKIPPED and
does not fail. Tracked theorems pinned to a corpus nobody can see is a different thing,
and it now has its own name.

Usage:  scripts/check_specs_fresh.py [--record]
Exit:   0 all specs current; 1 at least one stale; 2 nothing checkable;
        3 all checkable specs current, but a tracked spec module has no verifiable corpus.
"""
from __future__ import annotations
import argparse, hashlib, json, os, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MANIFEST = os.path.join(ROOT, "artifact-manifest.json")

# spec module (path under Autoform/) -> corpus module it is about
SPECS = {
    "SpecsGen/V8Base": "V8Base",
    "SpecsGen/Cachetools": "Cachetools",
    "SpecsGen/LinuxLib": "LinuxLibSample",
    "SpecsGen/LinuxLibSample": "LinuxLibSample",
    "SpecsGen/V8BaseSample": "V8BaseSample",
    "Specs/V8Spec": "V8BaseSample",
    "Specs/CachetoolsSpec": "Cachetools",
}


def sha(path: str) -> str | None:
    if not os.path.exists(path):
        return None
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for blk in iter(lambda: fh.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def corpus_hash(man: dict, corpus: str) -> tuple[str | None, str]:
    """Hash of the AST the corpus module is rendered from, and where it came from.

    Only bytes on disk count. The manifest's own `ast_sha256` is deliberately NOT a
    fallback: `corpus_ast_sha256` lives in the same file, so accepting it would compare
    the manifest against itself and pass whatever is recorded.
    """
    ent = man.get("modules", {}).get(corpus, {})
    tracked = os.path.join(ROOT, f"ast-{corpus}.json")
    if os.path.isfile(tracked):
        return sha(tracked), f"ast-{corpus}.json"
    hint = ent.get("ast_hint")
    if hint and os.path.isfile(hint):
        return sha(hint), hint
    where = f"ast-{corpus}.json"
    if ent.get("ast_hint"):
        where += f" nor {ent['ast_hint']}"
    return None, f"no AST on disk ({where})"


def git_tracked(rel: str) -> bool | None:
    """Is anything under `rel` tracked in git? None if git cannot answer."""
    try:
        p = subprocess.run(["git", "ls-files", "-z", "--", rel], cwd=ROOT,
                           capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.SubprocessError):
        return None
    if p.returncode != 0:
        return None
    return bool(p.stdout.strip("\0").strip())


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--record", action="store_true",
                    help="pin the current corpus hashes (only after re-generating)")
    a = ap.parse_args()
    man = json.load(open(MANIFEST))
    specs = man.setdefault("specs", {})
    stale, unchecked, unverifiable, skipped, ok = [], [], [], [], 0

    for spec, corpus in SPECS.items():
        if not os.path.exists(os.path.join(ROOT, "Autoform", spec + ".lean")) and \
           not os.path.isdir(os.path.join(ROOT, "Autoform", spec)):
            continue
        cur, src = corpus_hash(man, corpus)
        if cur is None:
            # The corpus cannot be hashed from the tree. Whether that is acceptable
            # depends on whether the SPECS are tracked: a tracked theorem pinned to an
            # invisible corpus is unverifiable and must not pass; an untracked spec
            # module is a local build product and legitimately absent in a fresh clone.
            answers = [git_tracked(f"Autoform/{spec}.lean"),
                       git_tracked(f"Autoform/{spec}")]
            tracked = True if True in answers else (
                None if None in answers else False)
            rec = specs.get(spec, {}).get("corpus_ast_sha256")
            if tracked is False:
                skipped.append(f"{spec}: corpus {corpus} — {src}; spec module is not "
                               f"tracked in git, so nothing in the repository depends on it")
            else:
                how = "tracked in git" if tracked else "of unknown git status"
                unverifiable.append(
                    f"{spec}: {how}, pinned to corpus {corpus} @ "
                    f"{(rec or 'never pinned')[:12]}, but {src}.\n"
                    f"    The corpus cannot be recomputed from this tree, so the pin "
                    f"cannot be checked by anything. Re-export the corpus AST, or stop "
                    f"tracking specs whose corpus is not tracked.")
            continue
        rec = specs.get(spec, {}).get("corpus_ast_sha256")
        if a.record:
            if rec and rec != cur:
                print(f"  re-pinning {spec}: {rec[:12]} -> {cur[:12]} (from {src})")
            specs[spec] = {"corpus": corpus, "corpus_ast_sha256": cur, "source": src}
            ok += 1
            continue
        if rec is None:
            unchecked.append(f"{spec}: never pinned — run --record after generating")
        elif rec != cur:
            stale.append(f"{spec}: generated against corpus {corpus} @ {rec[:12]}, "
                         f"tree now has {cur[:12]} ({src}).\n"
                         f"    The laws describe a different program. RE-GENERATE the specs; "
                         f"do not re-record the hash.")
        else:
            ok += 1

    if a.record:
        json.dump(man, open(MANIFEST, "w"), indent=1, sort_keys=True)
        print(f"check_specs_fresh: pinned {ok} spec module(s)")
        return 0
    for k in skipped:
        print(f"SKIPPED  {k}")
    for u in unchecked:
        print(f"UNPINNED {u}", file=sys.stderr)
    for u in unverifiable:
        print(f"UNVERIFIABLE {u}", file=sys.stderr)
    for s in stale:
        print(f"STALE    {s}", file=sys.stderr)
    if stale:
        print(f"\ncheck_specs_fresh: {len(stale)} spec module(s) describe a corpus that has "
              f"changed under them.", file=sys.stderr)
        return 1
    if not ok and (unchecked or unverifiable):
        print("\ncheck_specs_fresh: nothing could be checked.", file=sys.stderr)
        return 2
    if unverifiable:
        print(f"\ncheck_specs_fresh: {ok} spec module(s) match their corpus, but "
              f"{len(unverifiable)} tracked spec module(s) are pinned to a corpus this tree "
              f"cannot produce. This check does not speak for them.", file=sys.stderr)
        return 3
    print(f"check_specs_fresh: {ok} spec module(s) match the corpus they were generated from"
          + (f"; {len(skipped)} untracked spec module(s) skipped" if skipped else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
