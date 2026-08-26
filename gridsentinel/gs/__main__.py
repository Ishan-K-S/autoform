"""Console entry points for GridSentinel.

The two harnesses (`run.py`, `run_v2.py`) live at the repository root and are
owned elsewhere; this module does not reimplement them, it locates and calls
them.  It exists so that `pyproject.toml` can declare stable console scripts
(`gridsentinel-experiment`, `gridsentinel-attacks`, `gridsentinel-verify`)
without moving files that other agents own.

Each wrapper returns a process exit status, which is what a Makefile and CI
need and what `run.py` / `gs.verify.main()` do not provide on their own: both
return result dictionaries.  `verify_main` therefore inspects the returned
dictionary and fails the process if any proof layer regresses.

    python -m gs verify        # same as gridsentinel-verify
    python -m gs experiment --seed 0
    python -m gs attacks --seed 0

macOS note: invoke the interpreter as `arch -arm64 .venv/bin/python`, and
never under `timeout`.  See CONTRIBUTING.md.
"""

import os
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _load_harness(module_name):
    """Import `run` / `run_v2` from the repository root.

    Falls back to a plain import so that an installation which does put the
    harnesses on `sys.path` still works.
    """
    if REPO_ROOT not in sys.path:
        sys.path.insert(0, REPO_ROOT)
    try:
        return __import__(module_name)
    except ImportError:
        sys.stderr.write(
            "gridsentinel: cannot import harness %r.  The harnesses live at "
            "the repository root; run from a checkout, or install with "
            "`pip install -e .`.\n" % module_name)
        raise


def experiment_main(argv=None):
    """`gridsentinel-experiment` -- run.py, the v1 shield experiment."""
    run = _load_harness("run")
    res = run.main(argv if argv is not None else sys.argv[1:])
    return 0 if res else 1


def attacks_main(argv=None):
    """`gridsentinel-attacks` -- run_v2.py, the adversary catalogue."""
    run_v2 = _load_harness("run_v2")
    rc = run_v2.main(argv if argv is not None else sys.argv[1:])
    return 0 if rc is None else int(rc)


def verify_main(argv=None):
    """`gridsentinel-verify` -- the Z3 proof suite, with a pass/fail gate.

    `gs.verify.main()` prints its report and returns the raw results; it does
    not decide anything.  The gate below is what makes a proof regression fail
    a build.  It deliberately does NOT gate on the known negative results
    (DW5, the false-data-injection theorem): those are `sat` by design and
    documented as such in docs/PROOF.md 8.7.
    """
    del argv
    from gs import verify
    res = verify.main()

    # Layer 0: the FPM entries are side conditions Z3 could not close and are
    # reported as ASSUMED rather than PROVED; excluded, as verify.main's own
    # summary excludes them.
    layer0 = [t for t in res["nonfinite"] if not t["name"].startswith("FPM")]
    gates = [
        ("layer 0 (non-finite handling)", all(t["proved"] for t in layer0)),
        ("layer 1 (numeric)", bool(res["numeric"]["proved"])),
        ("layer 2 (logic)", bool(res["logic"]["proved"])),
        ("defect regressions", all(r["fixed"] for r in res["regression"])),
    ]
    print("")
    print("PROOF GATE")
    for name, ok in gates:
        print("  %-34s %s" % (name, "PASS" if ok else "FAIL"))
    failed = [n for n, ok in gates if not ok]
    if failed:
        sys.stderr.write("gridsentinel-verify: PROOF REGRESSION in %s\n"
                         % ", ".join(failed))
        return 1
    print("  all gates pass (see docs/PROOF.md for what is NOT proved --"
          " notably assumption A8)")
    return 0


def report_main(argv=None):
    """`gridsentinel-report` -- re-render figures from an existing run."""
    from gs import report
    report.main(argv if argv is not None else sys.argv[1:])
    return 0


_COMMANDS = {
    "experiment": experiment_main,
    "attacks": attacks_main,
    "verify": verify_main,
    "report": report_main,
}


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if not argv or argv[0] in ("-h", "--help") or argv[0] not in _COMMANDS:
        sys.stderr.write(
            "usage: python -m gs {%s} [args...]\n"
            % "|".join(sorted(_COMMANDS)))
        return 0 if (argv and argv[0] in ("-h", "--help")) else 2
    return _COMMANDS[argv[0]](argv[1:])


if __name__ == "__main__":
    sys.exit(main())
