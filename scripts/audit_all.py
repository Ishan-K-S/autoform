#!/usr/bin/env python3
"""
Trust-audit sweep (STRATEGY.md Tier 3/4).

Three independent checks, each of which can fail the build:

  1. AXIOM SWEEP  -- every declaration in the built `Autoform` library is asked what it
     actually stands on, via `Lean.collectAxioms` (the same primitive that
     `Autoform/Harness/Audit.lean`'s `#audit_axioms` uses).  `sorryAx` means "not
     proved"; `Lean.ofReduceBool` / `Lean.ofReduceNat` mean "the Lean compiler was
     trusted".  Either is a trusted-code leak.

  2. SOURCE SWEEP -- grep for the escape hatches that do not show up as axioms:
     `sorry`, `partial`, `unsafe`, `native_decide`, `@[implemented_by]`, `axiom`.
     Comments and docstrings are stripped first so that prose about `sorry` is not
     reported as a `sorry`.  The Core semantics is *claimed* to be free of all of
     these; this verifies the claim instead of restating it.

  3. KERNEL RECHECK -- `leanchecker` (shipped with the Lean toolchain since v4.28.0;
     formerly the standalone `lean4checker`) replays the compiled `.olean`s through the
     kernel again, starting from an empty environment (`--fresh`).  This catches
     environment hacking and any `.olean` that does not correspond to a
     kernel-accepted derivation.  If the binary is genuinely absent we say so, loudly,
     as an UNVERIFIED gap.  A gap that is reported is a gap; a gap that is skipped
     silently is a lie.

Outputs `audit.json` plus a human summary.  Exits non-zero if any trusted-code leak is
found, so it can gate CI.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# Axioms whose presence changes what a proof means.  Mirrors
# `Autoform.Audit.suspiciousAxioms`.
SUSPICIOUS_AXIOMS = {"sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat"}

# Axioms that are part of ordinary Lean mathematics and are not a leak.
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}

# Modules that are *generated* output rather than hand-written trusted base.
GENERATED_PREFIX = "Autoform.Generated"

# The subtree that is claimed to be escape-hatch free.
CORE_DIR = "Autoform/Lang/Core"

# Files whose escape hatches are deliberate demonstrations, not debt.
# `Demo.lean` proves a `sorry`-admitted theorem *on purpose* to show the audit
# catching it.  It is still reported, just not counted as a failure.
DEMONSTRATION_FILES = {"Demo.lean"}


def elan_env() -> dict:
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan" / "bin") + os.pathsep + env.get("PATH", "")
    return env


# --------------------------------------------------------------------------- #
# 1. Axiom sweep
# --------------------------------------------------------------------------- #

AXIOM_SWEEP_LEAN = r"""
import Autoform
import Lean
open Lean Elab Command

/-- Sweep every declaration whose defining module is under `Autoform`, and report its
axiom basis.  This is exactly what `#audit_axioms` does, applied to everything. -/
run_cmd do
  let env ← getEnv
  let mut out : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`Autoform).isPrefixOf mod do continue
    let axs ← liftCoreM <| collectAxioms n
    let kind := match ci with
      | .thmInfo _    => "theorem"
      | .axiomInfo _  => "axiom"
      | .defnInfo _   => "def"
      | .opaqueInfo _ => "opaque"
      | .ctorInfo _   => "ctor"
      | .inductInfo _ => "inductive"
      | .recInfo _    => "rec"
      | .quotInfo _   => "quot"
    out := out.push <| Json.mkObj
      [ ("name",   Json.str n.toString)
      , ("module", Json.str mod.toString)
      , ("kind",   Json.str kind)
      , ("axioms", Json.arr (axs.map (Json.str ·.toString))) ]
  IO.println "AUTOFORM_AUDIT_BEGIN"
  IO.println (Json.arr out).compress
  IO.println "AUTOFORM_AUDIT_END"
"""


def axiom_sweep() -> dict:
    """Run the Lean-side sweep and classify the result."""
    result = {
        "status": "unknown",
        "declarations": 0,
        "leaks": [],
        "declared_axioms": [],
        "nonstandard_axioms": [],
        "axiom_histogram": {},
        "error": None,
    }

    tmp = tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", dir=str(REPO), delete=False, prefix="_audit_sweep_"
    )
    try:
        tmp.write(AXIOM_SWEEP_LEAN)
        tmp.close()
        proc = subprocess.run(
            ["lake", "env", "lean", os.path.basename(tmp.name)],
            cwd=str(REPO), env=elan_env(), capture_output=True, text=True, timeout=1800,
        )
    except FileNotFoundError as e:
        result["status"] = "ERROR"
        result["error"] = f"lake not found: {e}"
        return result
    except subprocess.TimeoutExpired:
        result["status"] = "ERROR"
        result["error"] = "lake env lean timed out"
        return result
    finally:
        try:
            os.unlink(tmp.name)
        except OSError:
            pass

    out = proc.stdout
    if "AUTOFORM_AUDIT_BEGIN" not in out:
        result["status"] = "ERROR"
        result["error"] = (proc.stdout + proc.stderr)[-4000:]
        return result

    payload = out.split("AUTOFORM_AUDIT_BEGIN", 1)[1].split("AUTOFORM_AUDIT_END", 1)[0]
    decls = json.loads(payload.strip())
    result["declarations"] = len(decls)

    hist: dict[str, int] = {}
    for d in decls:
        for a in d["axioms"]:
            hist[a] = hist.get(a, 0) + 1
        bad = sorted(set(d["axioms"]) & SUSPICIOUS_AXIOMS)
        if bad:
            result["leaks"].append(
                {"name": d["name"], "module": d["module"], "kind": d["kind"],
                 "leaked": bad, "basis": d["axioms"]}
            )
        if d["kind"] == "axiom":
            result["declared_axioms"].append({"name": d["name"], "module": d["module"]})
        odd = sorted(set(d["axioms"]) - STANDARD_AXIOMS - SUSPICIOUS_AXIOMS)
        if odd:
            result["nonstandard_axioms"].append(
                {"name": d["name"], "module": d["module"], "axioms": odd}
            )
    result["axiom_histogram"] = dict(sorted(hist.items(), key=lambda kv: -kv[1]))
    result["status"] = "LEAK" if result["leaks"] else "CLEAN"
    return result


# --------------------------------------------------------------------------- #
# 2. Source sweep
# --------------------------------------------------------------------------- #

def strip_lean_comments(src: str) -> str:
    """Blank out `/- ... -/` (nesting, incl. `/-!` and `/--`) and `--` comments.

    Characters are replaced by spaces rather than deleted so that line and column
    numbers survive.  String literals are respected so that `"--"` inside a string is
    not treated as a comment start.
    """
    out = list(src)
    i, n = 0, len(src)
    depth = 0
    in_str = False
    while i < n:
        c = src[i]
        if depth == 0 and in_str:
            if c == "\\":
                out[i] = " "
                if i + 1 < n and src[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
                continue
            if c == '"':
                in_str = False
                out[i] = " "
                i += 1
                continue
            if c != "\n":
                out[i] = " "
            i += 1
            continue
        if src.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth > 0 and src.startswith("-/", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth > 0:
            if c != "\n":
                out[i] = " "
            i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        if c == '"':
            in_str = True
            out[i] = " "
            i += 1
            continue
        i += 1
    return "".join(out)


PATTERNS = [
    ("sorry",          re.compile(r"(?<![\w.])sorry(?![\w])")),
    ("sorryAx",        re.compile(r"(?<![\w.])sorryAx(?![\w])")),
    ("partial",        re.compile(r"(?<![\w.])partial(?![\w])")),
    ("unsafe",         re.compile(r"(?<![\w.])unsafe(?![\w])")),
    ("native_decide",  re.compile(r"(?<![\w.])native_decide(?![\w])")),
    ("implemented_by", re.compile(r"@\[[^\]]*implemented_by")),
    ("axiom",          re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+)?axiom(?![\w])",
                                  re.MULTILINE)),
    ("extern",         re.compile(r"@\[[^\]]*extern")),
]


def source_sweep() -> dict:
    findings = []
    scanned = 0
    for path in sorted(REPO.rglob("*.lean")):
        rel = path.relative_to(REPO).as_posix()
        if rel.startswith(".lake/") or "/.lake/" in rel:
            continue
        # `.claude/worktrees/<id>/` holds agent worktrees -- full checkouts of this
        # repository. Without this the sweep walked 18 copies of every module, so a
        # finding was reported at a path that is not the project, and `scanned` counted
        # the same file many times. A gate that reports findings against copies of
        # itself is noise, and noise is what a real finding hides in.
        if rel.startswith(".claude/") or "/.claude/" in rel:
            continue
        scanned += 1
        try:
            raw = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        code = strip_lean_comments(raw)
        lines = raw.splitlines()
        for kind, pat in PATTERNS:
            for m in pat.finditer(code):
                line_no = code.count("\n", 0, m.start()) + 1
                findings.append({
                    "kind": kind,
                    "file": rel,
                    "line": line_no,
                    "text": (lines[line_no - 1].strip() if line_no <= len(lines) else ""),
                    "demonstration": Path(rel).name in DEMONSTRATION_FILES,
                })

    core = [f for f in findings if f["file"].startswith(CORE_DIR)]
    generated = [f for f in findings if f["file"].startswith("Autoform/Generated/")]
    return {
        "files_scanned": scanned,
        "findings": findings,
        "by_kind": {k: sum(1 for f in findings if f["kind"] == k) for k, _ in PATTERNS},
        "core_findings": core,
        "core_clean": not core,
        "generated_findings": generated,
    }


# --------------------------------------------------------------------------- #
# 3. lean4checker
# --------------------------------------------------------------------------- #

def _leanchecker_exe() -> str | None:
    """Locate `leanchecker`.

    Since Lean v4.28.0 the former standalone `lean4checker` is part of the toolchain
    and ships as `leanchecker` in every elan toolchain, so no separate build is
    needed.  Order: $LEANCHECKER, PATH (with elan's bin prepended), the active
    toolchain's bin directory, then a legacy locally-built `lean4checker`.
    """
    override = os.environ.get("LEANCHECKER")
    if override:
        return override if Path(override).exists() else None

    env = elan_env()
    exe = shutil.which("leanchecker", path=env["PATH"])
    if exe:
        return exe

    # elan installs toolchains under ~/.elan/toolchains/<name>/bin.
    try:
        toolchain = (REPO / "lean-toolchain").read_text().strip()
    except OSError:
        toolchain = ""
    if toolchain:
        cand = (Path.home() / ".elan" / "toolchains"
                / toolchain.replace("/", "--").replace(":", "---") / "bin" / "leanchecker")
        if cand.exists():
            return str(cand)

    # Legacy: a from-source build of the deprecated standalone repo.
    exe = shutil.which("lean4checker", path=env["PATH"])
    if exe:
        return exe
    for cand in (REPO / ".lake" / "packages" / "lean4checker" / ".lake" / "build" / "bin" / "lean4checker",):
        if cand.exists():
            return str(cand)
    return None


def lean4checker(fresh: bool = True) -> dict:
    """Externally re-verify the .olean files, or report the gap honestly.

    We invoke it through `lake env` so that LEAN_PATH covers this package *and* its
    dependencies' build directories.

    `--fresh` replays every constant -- imported ones included -- into an empty
    environment.  That is the mode we rely on: it is the one demonstrated to reject a
    tampered `.olean` anywhere in the transitive import graph, at the cost of being
    single-threaded (~1.5 min for `Autoform`).  Without `--fresh` the checker can
    silently check almost nothing when the named module is a bare re-export list, which
    is exactly the shape `Autoform.lean` has; see STRATEGY.md 19 on silent oracles.
    """
    exe = _leanchecker_exe()
    if exe is None:
        return {
            "status": "UNVERIFIED",
            "available": False,
            "detail": (
                "leanchecker was not found. The .olean files have therefore NOT been "
                "re-verified by an independent kernel run: everything below rests on the "
                "elaborator's own kernel calls and on the assumption that the .oleans on "
                "disk correspond to the source. This is STRATEGY.md Tier 4's open gap, "
                "not a passing check. Since Lean v4.28.0 `leanchecker` ships with the "
                "toolchain, so this normally means elan's bin directory is not on PATH; "
                "otherwise set $LEANCHECKER to the binary."
            ),
        }

    cmd = ["lake", "env", exe] + (["--fresh"] if fresh else []) + ["Autoform"]
    try:
        proc = subprocess.run(
            cmd, cwd=str(REPO), env=elan_env(),
            capture_output=True, text=True, timeout=3600,
        )
    except FileNotFoundError as e:
        return {"status": "ERROR", "available": True, "exe": exe,
                "command": " ".join(cmd), "detail": f"could not run: {e}"}
    except subprocess.TimeoutExpired:
        return {"status": "ERROR", "available": True, "exe": exe,
                "command": " ".join(cmd), "detail": "leanchecker timed out"}

    return {
        "status": "VERIFIED" if proc.returncode == 0 else "FAILED",
        "available": True,
        "exe": exe,
        "mode": "fresh" if fresh else "module",
        "command": " ".join(cmd),
        "returncode": proc.returncode,
        "stdout": proc.stdout[-4000:],
        "stderr": proc.stderr[-4000:],
        "detail": (
            "the kernel replayed every constant reachable from `Autoform` into a fresh "
            "environment and accepted them all"
            if proc.returncode == 0 else
            "the independent kernel REJECTED the compiled environment"
        ),
    }


# --------------------------------------------------------------------------- #
# Report
# --------------------------------------------------------------------------- #

def main() -> int:
    ap = argparse.ArgumentParser(description="autoform trust-audit sweep")
    ap.add_argument("-o", "--output", default=str(REPO / "audit.json"))
    ap.add_argument("--skip-lean", action="store_true",
                    help="source sweep only (no lake invocation)")
    ap.add_argument("--strict", action="store_true",
                    help="also fail on demonstration sorries and on a missing leanchecker")
    ap.add_argument("--no-fresh", action="store_true",
                    help="run leanchecker without --fresh (faster, weaker: it may check "
                         "almost nothing for a re-export-only root module)")
    args = ap.parse_args()

    report: dict = {"repo": str(REPO)}
    report["source_sweep"] = source_sweep()
    report["axiom_sweep"] = (
        {"status": "SKIPPED", "leaks": [], "declarations": 0,
         "declared_axioms": [], "nonstandard_axioms": [], "axiom_histogram": {}}
        if args.skip_lean else axiom_sweep()
    )
    report["lean4checker"] = (
        {"status": "SKIPPED", "available": False} if args.skip_lean
        else lean4checker(fresh=not args.no_fresh)
    )

    ax = report["axiom_sweep"]
    src = report["source_sweep"]
    l4c = report["lean4checker"]

    real_src_leaks = [
        f for f in src["findings"]
        # `sorryAx` as a source token is a *name mention* (Audit.lean lists it as a
        # thing to look for); only the axiom sweep can tell a real one. So it is
        # reported but does not by itself fail the build.
        if f["kind"] in ("sorry", "native_decide") and not f["demonstration"]
    ]
    failures = []
    if ax["status"] == "LEAK":
        failures.append(f"{len(ax['leaks'])} declaration(s) with a trusted-code axiom")
    if ax["status"] == "ERROR":
        failures.append("axiom sweep could not run: " + str(ax.get("error"))[:200])
    if real_src_leaks:
        failures.append(f"{len(real_src_leaks)} sorry/native_decide in source")
    if l4c["status"] == "FAILED":
        failures.append("leanchecker rejected the .oleans")
    if l4c["status"] == "ERROR":
        failures.append("leanchecker could not run: " + str(l4c.get("detail"))[:200])
    if args.strict and l4c["status"] == "UNVERIFIED":
        failures.append("leanchecker unavailable (--strict)")

    report["verdict"] = {"failures": failures, "pass": not failures}

    Path(args.output).write_text(json.dumps(report, indent=2) + "\n")

    # ---- human summary ----
    p = print
    p("=" * 74)
    p("autoform trust audit")
    p("=" * 74)
    p("")
    p(f"[1] AXIOM SWEEP  ({ax['status']})")
    if ax["status"] == "ERROR":
        p("    could not run:")
        for line in str(ax.get("error", ""))[-1500:].splitlines():
            p("      " + line)
    else:
        p(f"    {ax['declarations']} declarations in the built Autoform library")
        p(f"    axiom histogram: {ax['axiom_histogram'] or '{} (no declaration uses any axiom)'}")
        if ax["declared_axioms"]:
            p(f"    {len(ax['declared_axioms'])} `axiom` declaration(s):")
            for a in ax["declared_axioms"]:
                p(f"      {a['name']}  ({a['module']})")
        else:
            p("    no `axiom` declarations of our own")
        if ax["leaks"]:
            p(f"    !! TRUSTED-CODE LEAK in {len(ax['leaks'])} declaration(s):")
            for d in ax["leaks"][:40]:
                p(f"      {d['name']}: {', '.join(d['leaked'])}")
        else:
            p("    no sorryAx / ofReduceBool / ofReduceNat anywhere in the library")
    p("")
    p(f"[2] SOURCE SWEEP  ({src['files_scanned']} .lean files, comments stripped)")
    if not src["findings"]:
        p("    no escape hatches found")
    for kind, _ in PATTERNS:
        hits = [f for f in src["findings"] if f["kind"] == kind]
        if not hits:
            continue
        p(f"    {kind}: {len(hits)}")
        for f in hits[:25]:
            tag = "  [demonstration]" if f["demonstration"] else ""
            p(f"      {f['file']}:{f['line']}: {f['text'][:90]}{tag}")
    p("")
    p(f"    Core semantics ({CORE_DIR}) claim: free of sorry/partial/unsafe/"
      "native_decide/implemented_by/axiom")
    if src["core_clean"]:
        p("    VERIFIED: no findings under Core.")
    else:
        p(f"    CLAIM FALSE: {len(src['core_findings'])} finding(s) under Core:")
        for f in src["core_findings"]:
            p(f"      {f['file']}:{f['line']} [{f['kind']}] {f['text'][:90]}")
    p("")
    p(f"[3] KERNEL RECHECK / leanchecker  ({l4c['status']})")
    if l4c["status"] in ("UNVERIFIED", "ERROR"):
        p("    " + str(l4c.get("detail")))
    elif l4c["status"] == "SKIPPED":
        p("    skipped (--skip-lean)")
    else:
        p(f"    {l4c.get('command')}  -> returncode {l4c.get('returncode')}")
        p("    " + str(l4c.get("detail")))
        if l4c["status"] == "FAILED":
            for line in ((l4c.get("stdout") or "") + (l4c.get("stderr") or ""))[-1500:].splitlines():
                p("      " + line)
    p("")
    p("-" * 74)
    if failures:
        p("VERDICT: FAIL")
        for f in failures:
            p("  - " + f)
    else:
        p("VERDICT: PASS (no trusted-code leak)")
        if l4c["status"] == "UNVERIFIED":
            p("  caveat: kernel re-check UNVERIFIED (leanchecker absent)")
    p(f"wrote {args.output}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
