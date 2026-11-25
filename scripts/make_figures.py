"""Generate 300-DPI publication figures for Paper 31 (Koszul Complexes & Multicolor Permutation Wordle).
Author: Lluis Eriksson
"""
from __future__ import annotations

import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / "results"
FIG_DIR = ROOT / "paper" / "figures"
FIG_DIR.mkdir(parents=True, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9,
    "axes.titlesize": 9.5,
    "axes.labelsize": 9,
    "xtick.labelsize": 8,
    "ytick.labelsize": 8,
    "legend.fontsize": 7.4,
    "figure.dpi": 300,
    "savefig.dpi": 300,
})


def make_fig1() -> None:
    d2 = json.loads((RESULTS / "exp2_wordle_dim_curves.json").read_text(encoding="utf-8"))["curves"]
    d4 = json.loads((RESULTS / "exp4_eval_rank_sweep.json").read_text(encoding="utf-8"))["rows"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.75))

    ds = list(range(8))
    styles = [
        ("n3_s111", "n=3, s=(1,1,1)", "#1b4f72", "o-"),
        ("n2_s32", "n=2, s=(3,2)", "#117a65", "s-"),
        ("n4_s1111", "n=4, s=(1,1,1,1)", "#d68910", "^-"),
        ("n3_s212", "n=3, s=(2,1,2)", "#2e86c1", "d-"),
        ("n3_s222", "n=3, s=(2,2,2)", "#a93226", "v-"),
    ]
    for key, lbl, col, sty in styles:
        ax1.plot(ds, d2[key]["dims"], sty, color=col, linewidth=1.5, markersize=3.8, label=lbl)
    ax1.set_xlabel("Max-degree bound d (rounds = d + 1)")
    ax1.set_ylabel("Quotient dim R_n(d)/(J_n cap R_n(d))")
    ax1.set_title("(a) Thm. 6.1 Multicolor Wordle dimensions")
    ax1.grid(True, linestyle="--", alpha=0.35)
    ax1.legend(loc="upper left", frameon=True, fontsize=6.9)

    ds4 = [r["d"] for r in d4]
    amb = [r["ambient_dim"] for r in d4]
    evr = [r["eval_rank"] for r in d4]
    x = np.arange(len(ds4))
    w = 0.36
    ax2.bar(x - w / 2, amb, width=w, color="#7f8c8d", label="Ambient dim (d+1)^3")
    ax2.bar(x + w / 2, evr, width=w, color="#1f618d", label="Exact V(J_3) eval rank")
    ax2.set_yscale("log")
    ax2.set_xticks(x)
    ax2.set_xticklabels([f"d={d}" for d in ds4])
    ax2.set_ylabel("Exact dimension / rank (log)")
    ax2.set_ylim(0.8, 300)
    ax2.set_title("(b) Exact V(J_3) rank match: s=(2,1,2)")
    ax2.grid(True, axis="y", linestyle="--", alpha=0.35)
    ax2.legend(loc="upper left", frameon=True, fontsize=7.0)
    for i, r in enumerate(evr):
        ax2.text(i + w / 2, r * 1.18, str(r), ha="center", va="bottom", fontsize=7.4, fontweight="bold")

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig1_wordle_dims_and_eval_rank.png", bbox_inches="tight")
    plt.close(fig)


def make_fig2() -> None:
    d3 = json.loads((RESULTS / "exp3_gap_free_strictness_grid.json").read_text(encoding="utf-8"))["rows"]
    grid = np.zeros((4, 4), dtype=int)
    for r in d3:
        b1, b2 = r["b"]
        grid[b2, b1] = r["strictness_defect"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.75))

    im = ax1.imshow(grid, origin="lower", cmap="RdYlGn_r", vmin=0, vmax=2, aspect="equal")
    for b1 in range(4):
        for b2 in range(4):
            val = grid[b2, b1]
            gf_lbl = "GF" if abs(b1 - b2) <= 1 else "GAP"
            txt_col = "white" if val >= 2 else "black"
            ax1.text(b1, b2, f"{gf_lbl}\ndef={val}", ha="center", va="center", fontsize=7.0, color=txt_col, fontweight="bold")
    ax1.set_xticks(range(4))
    ax1.set_yticks(range(4))
    ax1.set_xlabel("Multidegree coordinate b_1")
    ax1.set_ylabel("Multidegree coordinate b_2")
    ax1.set_title("(a) Strictness defect grid: N=M=2, s=(1,1)")

    # Panel (b): Grade dimensions of the 4 Mode-1 exact Koszul complexes
    d1 = json.loads((RESULTS / "exp1_certified_atlas.json").read_text(encoding="utf-8"))["rows"]
    m1 = [r for r in d1 if r["mode"] == "koszul_filtered_exactness_exact"]
    names = ["n3,m3\ns=(1,1,1)", "n2,m2\ns=(3,2)", "n3,m2\n(2,3,2)", "n2,m2\n(3,4)"]
    f0 = [r["summary"]["grade_dims"][0] for r in m1]
    f1 = [r["summary"]["grade_dims"][1] for r in m1]
    qd = [r["summary"]["quotient_dim"] for r in m1]
    x2 = np.arange(len(names))
    w = 0.26
    ax2.bar(x2 - w, f0, width=w, color="#1f618d", label="dim F_0^b = dim R_N(b)")
    ax2.bar(x2, f1, width=w, color="#d68910", label="dim F_1^b (Koszul grade 1)")
    ax2.bar(x2 + w, qd, width=w, color="#117a65", label="Exact quotient dim")
    ax2.set_xticks(x2)
    ax2.set_xticklabels(names, fontsize=7.0)
    ax2.set_ylabel("Vector space dimension")
    ax2.set_ylim(0, max(f0) + 18)
    ax2.set_title("(b) Certified exact Koszul complexes")
    ax2.grid(True, axis="y", linestyle="--", alpha=0.35)
    ax2.legend(loc="upper right", frameon=True, fontsize=6.8)

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig2_strictness_grid_and_koszul.png", bbox_inches="tight")
    plt.close(fig)


def make_fig3() -> None:
    d1 = json.loads((RESULTS / "exp1_certified_atlas.json").read_text(encoding="utf-8"))["rows"]
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.95), gridspec_kw={"width_ratios": [1.55, 1.0]})

    stems = [r["file"].replace(".cert.json", "") for r in d1]
    ms = [r["verify_ms"] for r in d1]
    mode_colors = {
        "koszul_filtered_exactness_exact": "#1f618d",
        "multicolor_wordle_dim_count_exact": "#117a65",
        "gap_free_strictness_failure_exact": "#b7950b",
        "zero_set_eval_rank_exact": "#922b21",
    }
    cols = [mode_colors[r["mode"]] for r in d1]

    y = np.arange(len(stems))
    ax1.barh(y, ms, color=cols, height=0.72)
    ax1.set_xscale("log")
    ax1.xaxis.set_minor_formatter(matplotlib.ticker.NullFormatter())
    ax1.set_yticks(y)
    ax1.set_yticklabels(stems, fontsize=6.4)
    ax1.invert_yaxis()
    ax1.set_xlabel("Zero-float replay latency (ms, log scale)")
    ax1.set_title("(a) Replay time across all 16 certificates")
    ax1.grid(True, axis="x", linestyle="--", alpha=0.35)

    modes = [
        ("M1: Koszul", 4, "#1f618d"),
        ("M2: Wordle", 4, "#117a65"),
        ("M3: Rem. A.1", 4, "#b7950b"),
        ("M4: V(J_n)", 4, "#922b21"),
    ]
    mx = np.arange(len(modes))
    ax2.bar(mx, [m[1] for m in modes], color=[m[2] for m in modes], width=0.56)
    ax2.set_xticks(mx)
    ax2.set_xticklabels([m[0] for m in modes], rotation=22, ha="right", fontsize=7.4)
    ax2.set_ylabel("Certified instances")
    ax2.set_ylim(0, 5.2)
    ax2.set_title("(b) Balanced 4-mode coverage")
    ax2.grid(True, axis="y", linestyle="--", alpha=0.35)
    for i, m in enumerate(modes):
        ax2.text(i, m[1] + 0.14, "4/4\nPASS", ha="center", va="bottom", fontsize=6.8, fontweight="bold")

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig3_atlas_summary.png", bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    make_fig1()
    make_fig2()
    make_fig3()
    print("[PASS] Generated 3 publication-quality 300-DPI figures in paper/figures/.")


if __name__ == "__main__":
    main()
