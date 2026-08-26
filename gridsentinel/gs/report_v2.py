"""Rendering for the v2 experiment: terminal tables + matplotlib figures for
out/results_v2.json.

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

INK = "#16181d"
CANVAS = "#fbfbfd"
GRID = "#c9ccd4"
MUTED = "#5b6070"

# Okabe-Ito.
BLUE = "#0072B2"
VERMILLION = "#D55E00"
GREEN = "#009E73"
ORANGE = "#E69F00"
PURPLE = "#CC79A7"
SKY = "#56B4E9"
YELLOW = "#F0E442"

ARM_COLOR = {"A": VERMILLION, "B": ORANGE, "C": GREEN, "D": PURPLE}
ARM_LABEL = {"A": "A  unmitigated",
             "B": "B  monitor, reported state trusted",
             "C": "C  monitor + independent residual",
             "D": "D  as C, observation channel FORGED"}
FAMILY_ORDER = ("grid", "process", "adaptive", "control",
                "unblockable")


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
        "axes.titlesize": 10, "axes.spines.top": False,
        "axes.spines.right": False, "figure.dpi": 140,
        "savefig.bbox": "tight",
    })
    return plt


# --------------------------------------------------------------------------
# terminal
# --------------------------------------------------------------------------

def _rule(w=78, ch="-"):
    return ch * w


def _pct(x):
    return "  n/a " if x is None else "%5.1f%%" % (100.0 * x)


def terminal(res, stream=None):
    out = stream or sys.stdout
    w = out.write

    def line(s=""):
        w(s + "\n")

    sc = res["score"]["as_written"]
    fav = res["score"]["favourable"]

    line()
    line("=" * 78)
    line("GRIDSENTINEL v2 -- adversary catalogue vs. actuation reference monitor")
    line("seed=%d   %d scenarios   envelope [%.0f, %.0f] Hz   slew %.0f Hz/s"
         % (res["seed"], sc["n_scenarios"],
            res["monitor_constants"]["SP_ABS_MIN"],
            res["monitor_constants"]["SP_ABS_MAX"],
            res["monitor_constants"]["SP_MAX_RATE"]))
    line("=" * 78)

    # ---- per-scenario table ------------------------------------------
    line()
    line("PER-SCENARIO  (as written; 'fav' = attacker-favourable pass)")
    line(_rule())
    line("%-44s %4s %5s %-6s %-6s %s"
         % ("scenario", "cmds", "grant", "exp", "fired", "verdict"))
    line(_rule())
    fav_by = {r["name"]: r for r in res["catalogue"]["favourable"]}
    for r in res["catalogue"]["as_written"]:
        exp = r["expected_invariant"] or "--"
        fired = r["first_block_invariant"] or "--"
        if r["expected_blocked"]:
            if not r["blocked"]:
                verdict = "MISS  <<<<"
            elif fired == exp:
                verdict = "block  right-reason"
            else:
                f2 = fav_by[r["name"]]["first_block_invariant"] or "--"
                verdict = "block  WRONG-REASON (fav:%s)" % f2
        else:
            verdict = "OVER-BLOCKED  <<<<" if r["blocked"] else "permitted  ok"
        line("%-44s %4d %5d %-6s %-6s %s"
             % (r["name"][:44], r["n_commands"], r["n_granted"], exp, fired,
                verdict))
    line(_rule())

    # ---- headline numbers --------------------------------------------
    line()
    line("(a) BLOCK RATE           %s   (%d/%d scenarios with "
         "expected_blocked=True)"
         % (_pct(sc["block_rate"]), sc["n_blocked"], sc["n_positive"]))
    if sc["misses"]:
        line("    SCENARIOS THAT GOT THROUGH:")
        for m in sc["misses"]:
            line("      * %s  (expected %s)" % (m["name"],
                                                m["expected_invariant"]))
            line("        %d/%d commands granted; %s"
                 % (m["n_granted"], m["n_commands"], m["why"]))
    else:
        line("    no misses")

    line()
    line("(b) NEGATIVE CONTROLS    %d/%d permitted as expected"
         % (sc["n_negative"] - sc["n_negative_overblocked"], sc["n_negative"]))
    pcc, ubc = sc.get("positive_controls"), sc.get("unblockable_controls")
    if pcc is not None:
        # Broken out because they are different failures.  Blocking a POSITIVE
        # control (ground_truth_permit=True) means the monitor refuses an
        # action that should be permitted -- an availability failure that
        # takes it out of service.  Blocking an `unblockable` means
        # over-blocking something the catalogue already admits is malicious.
        line("      positive controls (must be permitted): %d/%d%s"
             % (pcc["n_permitted"], pcc["n"],
                "" if not pcc["blocked"]
                else "   BLOCKED: " + ", ".join(pcc["blocked"])))
        line("      unblockable (monitor cannot see intent): %d/%d%s"
             % (ubc["n_permitted"], ubc["n"],
                "" if not ubc["blocked"]
                else "   BLOCKED: " + ", ".join(ubc["blocked"])))
    for n in sc["negative_controls"]:
        if n["blocked"]:
            line("      * OVER-BLOCKED %s" % n["name"])
            line("        %d/%d granted; first veto %s (%s)"
                 % (n["n_granted"], n["n_commands"], n["first_block_reason"],
                    n["first_block_invariant"]))
        else:
            line("      ok %s" % n["name"])

    line()
    line("(c) RIGHT-REASON RATE    %s strict (%d/%d blocked scenarios)"
         % (_pct(sc["right_reason_rate"]), sc["n_right_reason"],
            sc["n_blocked"]))
    line("                         %s lenient (expected invariant fired "
         "anywhere in the trace)"
         % _pct(sc["right_reason_rate_lenient"]))
    if sc["mismatches"]:
        line("    EVERY MISMATCH:")
        for m in sc["mismatches"]:
            f2 = fav_by[m["name"]]["first_block_invariant"]
            line("      * %s" % m["name"])
            line("          expected %s, blocked by %s  (%s)"
                 % (m["expected"], m["actual_first"], m["actual_reason"]))
            line("          all invariants that fired: %s"
                 % ", ".join(str(x) for x in m["all_fired"]))
            line("          attacker-favourable pass blocks by: %s%s"
                 % (f2, "  <- expected invariant IS load-bearing, merely "
                        "shadowed" if f2 == m["expected"] else
                        "  <- expected invariant never fires"))
    else:
        line("    no mismatches")

    line()
    line("    attacker-favourable pass: block rate %s, right-reason %s"
         % (_pct(fav["block_rate"]), _pct(fav["right_reason_rate"])))

    # ---- by family ----------------------------------------------------
    hpa = sc.get("harness_provenance_assumptions")
    if hpa:
        line()
        line("HARNESS ASSUMPTION AUDIT  (how much of the above is the "
             "harness, not the catalogue)")
        line(_rule())
        line("  policy: %s" % hpa["policy"])
        line("  local-addend provenance ASSUMED on %d/%d commands; asserted "
             "by: %s" % (hpa["commands_local_assumed"], hpa["commands_total"],
                         ", ".join(hpa["scenarios_asserting_local_provenance"])
                         or "no scenario"))
        line("  grants issued under the LEGACY opt-in: %d  (must be 0 -- "
             "every verdict above was decided on the shipped fail-closed "
             "default)" % hpa.get("grants_under_assumed_provenance", -1))
        line("  observation provenance  ASSUMED on %d/%d commands; asserted "
             "by: %s"
             % (hpa["commands_observation_assumed"], hpa["commands_total"],
                ", ".join(hpa["scenarios_asserting_observation_provenance"])
                or "no scenario"))

    line()
    line("BY FAMILY")
    line(_rule())
    line("%-13s %4s %8s %8s %8s %8s %s"
         % ("family", "pos", "blocked", "rate", "right", "rr-rate", "neg ok"))
    line(_rule())
    for fam in FAMILY_ORDER:
        f = sc["by_family"][fam]
        line("%-13s %4d %8d %8s %8d %8s %d/%d"
             % (fam, f["n_positive"], f["n_blocked"], _pct(f["block_rate"]),
                f["n_right_reason"], _pct(f["right_reason_rate"]),
                f["n_negative"] - f["n_negative_overblocked"], f["n_negative"]))
    line(_rule())

    # ---- drive ---------------------------------------------------------
    d = res["drive"]
    line()
    line("=" * 78)
    line("PHYSICAL CONSEQUENCE -- Stuxnet slow-cycle payload, three arms")
    line("payload period %.1f s; rotor fails at damage %.1f; "
         "burst onset %.0f Hz"
         % (d["arms"]["A"]["payload_period_s"],
            res["plant_constants"]["DAMAGE_FAIL"],
            res["plant_constants"]["F_BURST"]))
    line("=" * 78)
    line("%-38s %9s %9s %8s %8s %8s"
         % ("arm", "damage", "destroyed", "t_dest", "max Hz", "min Hz"))
    line(_rule())
    for a in ("A", "B", "C", "D"):
        r = d["arms"][a]
        td = "%8.1f" % r["destroyed_t"] if r["destroyed_t"] else "       -"
        line("%-38s %9.4f %9s %s %8.1f %8.1f"
             % (ARM_LABEL[a], r["final_damage"],
                "YES" if r["destroyed"] else "no", td,
                r["max_true_hz"], r["min_true_hz"]))
    line(_rule())
    a = d["arms"]["A"]
    if a["destroyed_t"]:
        line("arm A time-to-destruction: %.1f s = %.2f payload cycles "
             "(plant author: %.1f s = %.2f)"
             % (a["destroyed_t"], a["destroyed_bursts"],
                d["unmitigated_reference"]["plant_author_time_to_destruction_s"],
                d["unmitigated_reference"]["plant_author_bursts"]))
    for k in ("B", "C", "D"):
        r = d["arms"][k]
        if r["disowned_t_s"]:
            line("arm %s: I7 disowned the engineering source at t=%.1f s "
                 "(%d sustained vetoes) -- every later command is refused "
                 "with %s regardless of content"
                 % (k, r["disowned_t_s"], res["monitor_constants"]["VETO_LIMIT"],
                    "veto:I7-mode-disowned-source"))
        line("arm %s: %d/%d setpoints granted; vetoes: %s"
             % (k, r["n_granted"], r["n_commands"],
                ", ".join("%s x%d" % (kk.replace("veto:", ""), vv)
                          for kk, vv in sorted(r["veto_reasons"].items()))
                or "none"))

    line()
    line("DETECTION LATENCY (residual crosses %.1f sigma for %d consecutive "
         "steps; worst benign sample %.2f sigma)"
         % (d["residual_diagnostic"]["A"]["threshold_sigma"],
            d["residual_diagnostic"]["A"]["persist_steps"],
            d["residual_diagnostic"]["A"]["worst_benign_sigma"]))
    line(_rule())
    line("  %-4s %10s %10s %10s %9s %s"
         % ("arm", "lie@", "detect@", "latency", "band exit", "margin"))
    for k in ("A", "B", "C", "D"):
        rd = d["residual_diagnostic"][k]

        def f(x, u=" s"):
            return "%10s" % ("--" if x is None else "%.1f%s" % (x, u))
        line("  %-4s %10s %10s %10s %9s %s"
             % (k, f(rd["lie_start_s"]).strip(), f(rd["t_detect_s"]).strip(),
                f(rd["latency_s"]).strip(),
                f(rd["attack_start_s"]).strip(),
                ("detected %.1f s BEFORE the rotor left the band"
                 % rd["margin_before_excursion_s"])
                if rd["margin_before_excursion_s"] is not None
                else "nothing hidden to detect"))
    pb = d.get("per_burst_latency", {}).get("A")
    if pb and pb["n_bursts"]:
        line("  arm A per-burst: %d lying bursts, %d undetected; median "
             "latency %.1f s, WORST %.1f s"
             % (pb["n_bursts"], pb["n_bursts_undetected"],
                pb["median_latency_s"], pb["worst_latency_s"]))
        line("  arm A: the detector is above the gate on %.1f%% of lying "
             "steps (the low tail is the ramp passing through 1064 Hz, where "
             "there is genuinely nothing to see)"
             % (100.0 * pb["frac_lying_steps_above_gate"]))
    ml = d["monitor_latency_arm_c"]
    line("  monitor-visible divergence (arm C vetoes what arm B granted): %s"
         % ("t=%.1f s, latency %.1f s, %s"
            % (ml["t_first_divergence_s"], ml["latency_s"], ml["reason"])
            if ml["t_first_divergence_s"] is not None
            else "NONE -- arms B and C made identical decisions"))

    pp = d.get("provenance_probes")
    if pp:
        line()
        line("PROVENANCE PROBES  (harness-owned; NOT counted in the catalogue "
             "block rate)")
        line("the guard in isolation.  The catalogue now tests it in an "
             "adversary's hands, which")
        line("is a different question, so these stay separate rather than "
             "being folded in.")
        line(_rule())
        for x in pp["probes"]:
            line("  %-38s %-8s %-46s %s"
                 % (x["name"], "GRANT" if x["granted"] else "veto",
                    x["reason"].replace("veto:", ""),
                    "ok" if x["pass"] else "FAIL <<<<"))
        line("  %d/%d probes behave as specified" % (pp["n_pass"], pp["n"]))
        pc = d.get("provenance_coverage")
        if pc is not None:
            line("  catalogue coverage check: forcing all four provenance "
                 "fields True (the old")
            line("  fail-open behaviour, now only via the legacy opt-in) "
                 "changes %d catalogue outcome(s)%s"
                 % (len(pc["scenarios_changed_by_real_provenance"]),
                    "" if pc["catalogue_exercises_new_guards"]
                    else " -- so the catalogue does NOT test these guards"))

    e2 = d.get("e2_reachability")
    if e2:
        line()
        line("E2 REACHABILITY PROBE (source-hopping, 6 trips in 350 ms)")
        line(_rule())
        for k in ("as_written", "latch_cleared"):
            v = e2[k]
            line("  %-14s granted %d/6   E2 fired: %-5s   reasons: %s"
                 % (k, v["granted"], v["e2_fired"],
                    ", ".join(sorted(set(r.replace("veto:", "")
                                         for r in v["reasons"])))))

    sep = d["separation"]
    line()
    line("RESIDUAL SEPARATION")
    line(_rule())
    line("  benign: normal p50 %.2f  p99 %.2f  max %.2f;  operator move max %.2f"
         % (sep["normal_p50"], sep["normal_p99"], sep["normal_max"],
            sep["operator_max"]))
    line("  hidden-excursion steps: p05 %.1f  p50 %.1f  (%d steps)"
         % (sep["hidden_p05"], sep["hidden_p50"], sep["hidden_steps"]))
    line("  separation %.1fx on medians; %.1f%% of hidden steps above the "
         "worst benign sample"
         % (sep["separation_x"],
            100.0 * sep["hidden_frac_above_benign_max"]))
    line("  control (replay, no excursion): faked-step max %.2f sigma, "
         "damage %.4f" % (sep["replay_only_faked_max"],
                          sep["replay_only_damage"]))
    line()


# --------------------------------------------------------------------------
# figures
# --------------------------------------------------------------------------

def _finish(fig, ax_list, path):
    for ax in ax_list:
        ax.grid(True, alpha=0.45, linewidth=0.6)
        ax.set_axisbelow(True)
    fig.savefig(path)
    import matplotlib.pyplot as plt
    plt.close(fig)


def fig_rates_by_family(res, out_dir):
    plt = _mpl()
    sc = res["score"]["as_written"]
    fams = [f for f in FAMILY_ORDER if sc["by_family"][f]["n_positive"]]
    br = [sc["by_family"][f]["block_rate"] or 0.0 for f in fams]
    rr = [sc["by_family"][f]["right_reason_rate"] or 0.0 for f in fams]
    x = range(len(fams))
    fig, ax = plt.subplots(figsize=(6.4, 3.4))
    wdt = 0.38
    ax.bar([i - wdt / 2 for i in x], [100 * v for v in br], wdt,
           label="block rate", color=BLUE, edgecolor=INK, linewidth=0.6)
    ax.bar([i + wdt / 2 for i in x], [100 * v for v in rr], wdt,
           label="right-reason rate", color=ORANGE, edgecolor=INK,
           linewidth=0.6)
    for i, f in enumerate(fams):
        d = sc["by_family"][f]
        ax.text(i - wdt / 2, 100 * br[i] + 2, "%d/%d"
                % (d["n_blocked"], d["n_positive"]), ha="center", fontsize=7.5)
        ax.text(i + wdt / 2, 100 * rr[i] + 2, "%d/%d"
                % (d["n_right_reason"], d["n_blocked"]), ha="center",
                fontsize=7.5)
    ax.set_xticks(list(x))
    ax.set_xticklabels(fams)
    ax.set_ylim(0, 118)
    ax.set_ylabel("percent")
    ax.set_title("Blocked, and blocked for the expected reason, by family\n"
                 "(right-reason is of the BLOCKED scenarios in that family)",
                 loc="left")
    ax.legend(frameon=False, ncol=2, loc="upper right")
    p = os.path.join(out_dir, "v2_block_right_reason.png")
    _finish(fig, [ax], p)
    return p


def fig_damage(res, out_dir):
    plt = _mpl()
    d = res["drive"]
    fig, (ax, ax2) = plt.subplots(2, 1, figsize=(6.8, 5.4), sharex=True,
                                  gridspec_kw={"height_ratios": [1.35, 1]})
    fail = res["plant_constants"]["DAMAGE_FAIL"]
    # B and C coincide exactly whenever the residual changes no decision, so
    # B is drawn thicker and dashed underneath C rather than being hidden.
    style = {"A": (1.7, "-"), "B": (3.0, "--"), "C": (1.5, "-"),
             "D": (1.2, "-.")}
    for a in ("A", "B", "C", "D"):
        r = d["arms"][a]
        lw, ls = style[a]
        ax.plot(r["t"], r["damage"], color=ARM_COLOR[a], linewidth=lw,
                linestyle=ls, label=ARM_LABEL[a])
        ax2.plot(r["t"], r["speed_true"], color=ARM_COLOR[a], linewidth=lw,
                 linestyle=ls)
    ax.axhline(fail, color=INK, linestyle="--", linewidth=1.0)
    ax.text(0.995, fail, " rotor destroyed", transform=ax.get_yaxis_transform(),
            ha="right", va="bottom", fontsize=8)
    a = d["arms"]["A"]
    if a["destroyed_t"]:
        ax.axvline(a["destroyed_t"], color=VERMILLION, linewidth=0.9,
                   linestyle=":")
        ax.text(a["destroyed_t"], fail * 0.55,
                "  A fails\n  %.0f s (%.2f cycles)"
                % (a["destroyed_t"], a["destroyed_bursts"]), fontsize=7.5,
                color=VERMILLION)
    ax.set_ylabel("accumulated rotor damage")
    ax.set_ylim(0, max(1.25, fail * 1.25))
    ax.set_title("Three arms of the slow-cycle payload: damage, and the true "
                 "rotor speed that caused it", loc="left")
    ax.legend(frameon=False, loc="center left", fontsize=8)
    band = (res["monitor_constants"]["SP_ABS_MIN"],
            res["monitor_constants"]["SP_ABS_MAX"])
    ax2.axhspan(band[0], band[1], color=SKY, alpha=0.22, linewidth=0)
    ax2.text(0.004, band[1], " qualified band", transform=ax2.get_yaxis_transform(),
             fontsize=7.5, va="bottom", color=MUTED)
    for c, hw, _s in res["plant_constants"]["RESONANCES"]:
        ax2.axhspan(c - hw, c + hw, color=PURPLE, alpha=0.28, linewidth=0)
    ax2.set_ylabel("true rotor speed, Hz")
    ax2.set_xlabel("seconds")
    p = os.path.join(out_dir, "v2_rotor_damage.png")
    _finish(fig, [ax, ax2], p)
    return p


def fig_residual(res, out_dir):
    plt = _mpl()
    d = res["drive"]
    sep = d["separation"]
    fig, (ax, ax2) = plt.subplots(1, 2, figsize=(7.6, 3.3),
                                  gridspec_kw={"width_ratios": [2.1, 1]})
    r = d["arms"]["A"]
    ax.plot(r["t"], r["residual"], color=VERMILLION, linewidth=0.9,
            label="arm A residual")
    thr = d["residual_diagnostic"]["A"]["threshold_sigma"]
    ax.axhline(thr, color=INK, linestyle="--", linewidth=1.0)
    ax.text(0.995, thr, " monitor gate %.0f sigma" % thr, ha="right",
            va="bottom", fontsize=8, transform=ax.get_yaxis_transform())
    ax.axhline(sep["benign_max"], color=GREEN, linestyle=":", linewidth=1.0)
    ax.text(0.995, sep["benign_max"], " worst benign %.1f" % sep["benign_max"],
            ha="right", va="top", fontsize=7.5, color=GREEN,
            transform=ax.get_yaxis_transform())
    rd = d["residual_diagnostic"]["A"]
    if rd["t_detect_s"] is not None:
        ax.axvline(rd["t_detect_s"], color=BLUE, linewidth=1.0)
        ax.text(rd["t_detect_s"], ax.get_ylim()[1] * 0.92,
                "  detected, latency %.1f s" % rd["latency_s"], fontsize=7.5,
                color=BLUE)
    ax.set_yscale("symlog", linthresh=10)
    ax.set_ylim(0, None)
    ax.set_xlabel("seconds")
    ax.set_ylabel("residual, sigma")
    ax.set_title("Independent residual under the payload (arm A)", loc="left")

    labels = ["normal\np50", "normal\nmax", "operator\nmax", "hidden\np05",
              "hidden\np50"]
    vals = [sep["normal_p50"], sep["normal_max"], sep["operator_max"],
            sep["hidden_p05"], sep["hidden_p50"]]
    cols = [GREEN, GREEN, GREEN, VERMILLION, VERMILLION]
    ax2.bar(range(5), vals, color=cols, edgecolor=INK, linewidth=0.6)
    ax2.axhline(thr, color=INK, linestyle="--", linewidth=1.0)
    for i, v in enumerate(vals):
        ax2.text(i, v, "%.1f" % v, ha="center", va="bottom", fontsize=7)
    ax2.set_xticks(range(5))
    ax2.set_xticklabels(labels, fontsize=6.5, rotation=35, ha="right")
    ax2.set_ylabel("sigma")
    ax2.set_title("Separation %.1fx" % sep["separation_x"], loc="left")
    p = os.path.join(out_dir, "v2_residual_separation.png")
    _finish(fig, [ax, ax2], p)
    return p


def figures(res, out_dir):
    made = []
    for fn in (fig_rates_by_family, fig_damage, fig_residual):
        try:
            made.append(os.path.basename(fn(res, out_dir)))
        except Exception as exc:                        # pragma: no cover
            print("figure %s failed: %s" % (fn.__name__, exc))
    return made


if __name__ == "__main__":
    path = sys.argv[1] if len(sys.argv) > 1 else \
        os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                     "out", "results_v2.json")
    with open(path) as fh:
        r = json.load(fh)
    terminal(r)
    print(figures(r, os.path.dirname(path)))
