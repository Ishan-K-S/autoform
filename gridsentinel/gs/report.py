"""Rendering: terminal tables + matplotlib figures for out/results.json.

Legibility in light AND dark contexts is handled the only way that actually
works for a raster figure embedded in an unknown page: every figure carries
its own OPAQUE near-white canvas and near-black ink, so it never inherits the
host background, and the categorical palette is the Okabe-Ito colour-blind
safe set, which keeps adequate contrast against that canvas.
"""

from __future__ import print_function

import json
import os
import sys

# Okabe-Ito, plus a neutral.  Distinguishable in mono and to CVD readers.
INK = "#16181d"
CANVAS = "#fbfbfd"
GRID = "#c9ccd4"
ARM_COLOR = {
    "baseline": "#0072B2",        # blue
    "ai_unshielded": "#D55E00",   # vermillion
    "ai_shielded": "#009E73",     # bluish green
}
ARM_LABEL = {
    "baseline": "A  baseline",
    "ai_unshielded": "B  ai_unshielded",
    "ai_shielded": "C  ai_shielded",
}
ARMS = ("baseline", "ai_unshielded", "ai_shielded")


def _mpl():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams.update({
        "figure.facecolor": CANVAS, "savefig.facecolor": CANVAS,
        "axes.facecolor": CANVAS, "axes.edgecolor": INK,
        "axes.labelcolor": INK, "text.color": INK,
        "xtick.color": INK, "ytick.color": INK,
        "grid.color": GRID, "font.size": 9,
        "axes.titlesize": 10, "axes.titleweight": "bold",
        "savefig.bbox": "tight", "savefig.dpi": 150,
    })
    return plt


# --- terminal tables --------------------------------------------------------

def _fmt(x, nd=1):
    if x is None:
        return "-"
    if isinstance(x, float):
        return ("%%.%df" % nd) % x
    return str(x)


def _table(rows, headers, out=sys.stdout):
    widths = [len(h) for h in headers]
    srows = []
    for r in rows:
        sr = [str(c) for c in r]
        srows.append(sr)
        for i, c in enumerate(sr):
            widths[i] = max(widths[i], len(c))
    line = "  ".join(h.ljust(widths[i]) for i, h in enumerate(headers))
    print(line, file=out)
    print("  ".join("-" * w for w in widths), file=out)
    for sr in srows:
        print("  ".join(c.ljust(widths[i]) for i, c in enumerate(sr)), file=out)


def print_tables(res, out=sys.stdout):
    by_arm = res["by_arm"]
    policies = res["policies"]

    print("\n" + "=" * 78, file=out)
    print("GridSentinel  seed=%s  scenarios=%d  (%d per family)"
          % (res["seed"], res["n_scenarios"], res["n_per_family"]), file=out)
    print("=" * 78, file=out)

    lem = res.get("lemma", {})
    print("\nsensitivity-floor lemma: proved=%s  worst margin=%.4f pu"
          % (lem.get("proved"), lem.get("worst_margin_pu", float("nan"))),
          file=out)

    print("\n-- HEAD TO HEAD (all scenarios, per policy x arm) "
          + "-" * 27, file=out)
    rows = []
    for pol in policies:
        for arm in ARMS:
            d = by_arm.get("%s|%s" % (pol, arm))
            if d is None:
                continue
            rows.append([
                pol, ARM_LABEL[arm],
                "%d/%d" % (d["false_trips"], d["n_benign"]),
                "%d/%d" % (d["missed"], d["n_internal"]),
                _fmt(100.0 * d["dependability"] if d["dependability"] is not None else None),
                _fmt(d["median_latency_ms"]),
                _fmt(d["p95_latency_ms"]),
                d["baseline_only_episodes"],
                d["pre_inception_trips"],
            ])
    _table(rows, ["policy", "arm", "false trips", "missed", "depend%",
                  "med ms", "p95 ms", "disowned", "pre-inception"], out)
    pre = sum(by_arm[k]["pre_inception_trips"] for k in by_arm)
    if pre:
        print("   !! 'pre-inception' counts trips at t < EVENT_MS, i.e. on the "
              "HEALTHY pre-fault load\n      point.  These are not protection "
              "operations.  A non-zero column means the arm's\n      "
              "dependability and latency figures are contaminated and should "
              "not be read as\n      protection performance.", file=out)

    print("\n-- FALSE TRIPS BY FAMILY (internal_truth = False) "
          + "-" * 28, file=out)
    fams = [f for f in res["families"]]
    rows = []
    for pol in policies:
        for arm in ARMS:
            cells = []
            tot = 0
            for f in fams:
                d = res["by_family"].get("%s|%s|%s" % (pol, arm, f))
                if d is None or d["n_benign"] == 0:
                    cells.append(".")
                    continue
                cells.append("%d/%d" % (d["false_trips"], d["n_benign"]))
                tot += d["false_trips"]
            rows.append([pol, ARM_LABEL[arm]] + cells + [str(tot)])
    _table(rows, ["policy", "arm"] + fams + ["TOTAL"], out)

    hif = [f for f in fams if "hif" in f or "arcing" in f]
    print("\n-- HIGH-IMPEDANCE ARCING FAMILY (dependability + speed) "
          + "-" * 22, file=out)
    rows = []
    for f in hif:
        for pol in policies:
            for arm in ARMS:
                d = res["by_family"].get("%s|%s|%s" % (pol, arm, f))
                if d is None or not d["n_internal"]:
                    continue
                rows.append([f, pol, ARM_LABEL[arm],
                             "%d/%d" % (d["correct_trips"], d["n_internal"]),
                             _fmt(100.0 * d["dependability"]),
                             _fmt(d["median_latency_ms"]),
                             _fmt(d["p95_latency_ms"])])
    _table(rows, ["family", "policy", "arm", "detected", "reach%",
                  "med ms", "p95 ms"], out)

    print("\n-- SHIELD VETOES BY REASON (arm C only) " + "-" * 38, file=out)
    reasons = sorted({r for k, d in by_arm.items() if d["arm"] == "ai_shielded"
                      for r in d["vetoes"]})
    rows = []
    for pol in policies:
        d = by_arm.get("%s|ai_shielded" % pol)
        if d is None:
            continue
        rows.append([pol] + [str(d["vetoes"].get(r, 0)) for r in reasons]
                    + [str(d["grants"]), str(d["baseline_only_episodes"])])
    _table(rows, ["policy"] + [r.replace("veto:", "") for r in reasons]
           + ["grants", "disowned"], out)

    # Honest, explicit callout of every arm-C false trip, ATTRIBUTED.
    # A false trip that arrives via `baseline` is the incumbent relay
    # mis-operating and reaching the coil through invariant I6 (the shield is
    # forbidden to inhibit it).  A false trip via `ai+shield` is the shield
    # itself granting an accelerated trip on a healthy line, which is the
    # thing the design claims is impossible.
    print("\n-- ARM C FALSE-TRIP ATTRIBUTION " + "-" * 46, file=out)
    rows = []
    for pol in policies:
        a = by_arm.get("%s|baseline" % pol)
        c = by_arm.get("%s|ai_shielded" % pol)
        if c is None:
            continue
        granted = [b for b in c["false_trip_scenarios"]
                   if b["source"] == "ai+shield"]
        passed = [b for b in c["false_trip_scenarios"]
                  if b["source"] == "baseline"]
        rows.append([pol, a["false_trips"] if a else "-", c["false_trips"],
                     (c["false_trips"] - a["false_trips"]) if a else "-",
                     len(passed), len(granted),
                     c.get("shield_grants_on_benign", 0)])
    _table(rows, ["policy", "arm A", "arm C", "C - A",
                  "via baseline (I6)", "GRANTED BY SHIELD",
                  "shield granted on benign (any t)"], out)
    print("   The last column counts benign/attack episodes where the shield "
          "granted at ANY time in the\n   400 ms horizon, including after the "
          "baseline had already fired.  It is the strict test of\n   the "
          "safety claim; the previous column is the subset that actually "
          "reached the coil first.", file=out)

    strict = []
    for pol in policies:
        c = by_arm.get("%s|ai_shielded" % pol)
        if c:
            for b in c.get("shield_grant_on_benign_scenarios", []):
                strict.append((pol, b))
    if strict:
        print("\n!! THE SHIELD GRANTED ON %d NON-INTERNAL EPISODES "
              "(strict test):" % len(strict), file=out)
        seen = {}
        for pol, b in strict:
            seen.setdefault((pol, b["family"]), []).append(b)
        for (pol, fam), bs in sorted(seen.items()):
            print("   policy=%-16s family=%-26s %d episodes, e.g. %s at t=%s"
                  % (pol, fam, len(bs), bs[0]["scenario"], bs[0]["t"]),
                  file=out)

    granted_all, passed_all = [], []
    for pol in policies:
        c = by_arm.get("%s|ai_shielded" % pol)
        if not c:
            continue
        for b in c["false_trip_scenarios"]:
            (granted_all if b["source"] == "ai+shield"
             else passed_all).append((pol, b))
    print("", file=out)
    if granted_all:
        print("!! THE SHIELD GRANTED %d FALSE TRIPS -- the headline safety "
              "claim is FALSIFIED:" % len(granted_all), file=out)
        seen = {}
        for pol, b in granted_all:
            seen.setdefault((pol, b["family"]), []).append(b)
        for (pol, fam), bs in sorted(seen.items()):
            print("   policy=%-16s family=%-24s %d episodes, "
                  "e.g. %s at t=%s" % (pol, fam, len(bs), bs[0]["scenario"],
                                       bs[0]["t"]), file=out)
    else:
        print("shield-granted false trips: 0 across every policy and family.",
              file=out)
    if passed_all:
        seen = {}
        for pol, b in passed_all:
            seen.setdefault((pol, b["family"], b["element"]), []).append(b)
        print("\n   (arm C also inherits these BASELINE mis-operations "
              "through I6; they are arm A's, not the shield's:)", file=out)
        for (pol, fam, el), bs in sorted(seen.items(),
                                         key=lambda kv: str(kv[0])):
            print("      policy=%-16s family=%-24s element=%-6s %d episodes"
                  % (pol, fam, el, len(bs)), file=out)
    print("", file=out)


# --- figures ----------------------------------------------------------------

def fig_false_trips(res, path):
    plt = _mpl()
    fams = res["families"]
    policies = res["policies"]
    fig, axes = plt.subplots(1, len(policies),
                             figsize=(3.0 * len(policies), 3.6), sharey=True)
    if len(policies) == 1:
        axes = [axes]
    width = 0.26
    for ax, pol in zip(axes, policies):
        for j, arm in enumerate(ARMS):
            vals, xs = [], []
            for i, f in enumerate(fams):
                d = res["by_family"].get("%s|%s|%s" % (pol, arm, f))
                if d is None or d["n_benign"] == 0:
                    continue
                xs.append(i + (j - 1) * width)
                vals.append(d["false_trips"])
            ax.bar(xs, vals, width, color=ARM_COLOR[arm],
                   label=ARM_LABEL[arm], edgecolor=INK, linewidth=0.4)
        ax.set_title(pol)
        ax.set_xticks(range(len(fams)))
        ax.set_xticklabels(fams, rotation=60, ha="right", fontsize=7)
        ax.grid(axis="y", lw=0.5, alpha=0.6)
        ax.set_axisbelow(True)
    axes[0].set_ylabel("false trips (internal_truth = False)")
    axes[-1].legend(fontsize=7, frameon=False)
    fig.suptitle("False trips by arm and scenario family "
                 "(arm C must be zero everywhere)", fontsize=10,
                 fontweight="bold")
    fig.savefig(path)
    plt.close(fig)
    return path


def fig_latency_cdf(res, path, policy="honest"):
    """Two panels: the full distribution, and the sub-cycle region where the
    AI's benefit actually lives (a few late backup operations otherwise
    compress the interesting 0-40 ms band into nothing)."""
    plt = _mpl()
    fig, (ax, axz) = plt.subplots(1, 2, figsize=(9.2, 3.9))
    curves = {}
    for arm in ("baseline", "ai_shielded"):
        lat = sorted(e["latency_ms"] for e in res["episodes"]
                     if e["policy"] == policy and e["arm"] == arm
                     and e["internal_truth"] and e["trip"])
        if lat:
            curves[arm] = lat
    for a, zoom in ((ax, False), (axz, True)):
        for arm, lat in curves.items():
            n = len(lat)
            ys = [(i + 1) / float(n) for i in range(n)]
            a.step([0] + lat, [0] + ys, where="post", lw=2.0,
                   color=ARM_COLOR[arm],
                   label="%s  (n=%d, med %.0f ms)"
                         % (ARM_LABEL[arm], n, lat[n // 2]))
        a.set_xlabel("trip latency after fault inception (ms)")
        a.set_ylim(0, 1.02)
        a.grid(lw=0.5, alpha=0.6)
        a.set_axisbelow(True)
        if zoom:
            a.set_xlim(0, 40)
            a.set_title("zoom: sub-cycle region (0-40 ms)")
        else:
            a.set_title("full distribution")
            a.set_ylabel("fraction of genuine internal faults cleared")
            a.legend(fontsize=8, frameon=False, loc="lower right")
    fig.suptitle("Trip-latency CDF on genuine internal faults (policy: %s)"
                 % policy, fontsize=10, fontweight="bold")
    fig.savefig(path)
    plt.close(fig)
    return path


def fig_hif_reach(res, path):
    """Detection reach on the high-impedance arcing family vs fault resistance
    is not recorded per-episode as rf, so we show detection rate by family for
    the internal families, which is what 'reach' means operationally here."""
    plt = _mpl()
    fams = [f for f in res["families"]
            if any(e["family"] == f and e["internal_truth"]
                   for e in res["episodes"])]
    policies = res["policies"]
    fig, ax = plt.subplots(figsize=(1.9 * max(len(fams), 3) + 2.0, 3.8))
    n_groups = len(fams) * len(policies)
    labels = []
    width = 0.26
    x = 0
    for f in fams:
        for pol in policies:
            for j, arm in enumerate(ARMS):
                d = res["by_family"].get("%s|%s|%s" % (pol, arm, f))
                if d is None or not d["n_internal"]:
                    continue
                ax.bar(x + (j - 1) * width, 100.0 * d["dependability"], width,
                       color=ARM_COLOR[arm],
                       label=ARM_LABEL[arm] if x == 0 and f == fams[0] else None,
                       edgecolor=INK, linewidth=0.4)
            labels.append("%s\n%s" % (f, pol))
            x += 1
    ax.set_xticks(range(len(labels)))
    ax.set_xticklabels(labels, fontsize=6.5, rotation=45, ha="right")
    ax.set_ylabel("detected (% of genuine internal faults)")
    ax.set_ylim(0, 105)
    ax.axhline(100, color=INK, lw=0.6, ls=":")
    ax.set_title("Detection reach on genuine internal faults, "
                 "by family and policy")
    ax.grid(axis="y", lw=0.5, alpha=0.6)
    ax.set_axisbelow(True)
    ax.legend(fontsize=8, frameon=False, loc="lower left")
    fig.savefig(path)
    plt.close(fig)
    return path


def fig_veto_breakdown(res, path):
    plt = _mpl()
    policies = res["policies"]
    reasons = sorted({r for k, d in res["by_arm"].items()
                      if d["arm"] == "ai_shielded" for r in d["vetoes"]})
    if not reasons:
        return None
    fig, ax = plt.subplots(figsize=(6.4, 3.6))
    bottoms = [0.0] * len(policies)
    cmap = ["#0072B2", "#E69F00", "#CC79A7", "#009E73", "#56B4E9",
            "#D55E00", "#F0E442", "#666666"]
    for i, r in enumerate(reasons):
        vals = [res["by_arm"].get("%s|ai_shielded" % p, {}).get("vetoes", {})
                .get(r, 0) for p in policies]
        ax.bar(range(len(policies)), vals, 0.6, bottom=bottoms,
               color=cmap[i % len(cmap)], label=r.replace("veto:", ""),
               edgecolor=INK, linewidth=0.4)
        bottoms = [b + v for b, v in zip(bottoms, vals)]
    ax.set_xticks(range(len(policies)))
    ax.set_xticklabels(policies)
    ax.set_ylabel("shield vetoes (arm C, whole catalogue)")
    ax.set_title("Why the shield said no, by reason and policy")
    ax.legend(fontsize=7, frameon=False, ncol=2)
    ax.grid(axis="y", lw=0.5, alpha=0.6)
    ax.set_axisbelow(True)
    fig.savefig(path)
    plt.close(fig)
    return path


def render(res, out_dir="out"):
    if not os.path.isdir(out_dir):
        os.makedirs(out_dir)
    print_tables(res)
    made = []
    for fn, name in ((fig_false_trips, "false_trips.png"),
                     (fig_latency_cdf, "latency_cdf.png"),
                     (fig_hif_reach, "hif_reach.png"),
                     (fig_veto_breakdown, "veto_breakdown.png")):
        p = fn(res, os.path.join(out_dir, name))
        if p:
            made.append(p)
    print("figures:", ", ".join(os.path.basename(p) for p in made))
    return made


def main(argv=None):
    argv = argv or sys.argv[1:]
    path = argv[0] if argv else os.path.join("out", "results.json")
    with open(path) as fh:
        res = json.load(fh)
    render(res, out_dir=os.path.dirname(os.path.abspath(path)))


if __name__ == "__main__":
    main()
