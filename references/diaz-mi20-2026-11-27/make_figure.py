#!/usr/bin/env python3
import json
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

with open("/home/marcio/Projects/mi20-subquadratic-lee/staircase_results.json") as f:
    data = json.load(f)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9.5,
    "axes.edgecolor": "#334155",
    "axes.linewidth": 0.8,
    "grid.color": "#cbd5e1",
    "grid.linestyle": "--",
    "grid.linewidth": 0.55,
    "legend.frameon": True,
    "legend.facecolor": "#ffffff",
    "legend.edgecolor": "#cbd5e1",
})

fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.2, 3.85), dpi=300)

styles = {
    "5/4": dict(color="#1d4ed8", marker="o", ls="-",  lw=1.8, ms=5.5, label=r"$p = 5/4$"),
    "4/3": dict(color="#0f766e", marker="^", ls="-.", lw=1.7, ms=5.5, label=r"$p = 4/3$ (Holden benchmark)"),
    "3/2": dict(color="#b91c1c", marker="s", ls="--", lw=1.7, ms=5.2, label=r"$p = 3/2$"),
}

# Panel (a): Step gains
ns = [3, 4, 5, 6, 7, 8]
for key in ["5/4", "4/3", "3/2"]:
    rows = {r["n"]: r for r in data[key]}
    deltas = [rows[n]["delta"] for n in ns]
    ax1.semilogy(ns, deltas, **styles[key])

ax1.set_title(r"(a) Strictly Positive Step Gains $\Delta_n = C_{p,2}(n) - C_{p,2}(n-1)$",
              fontsize=9.8, fontweight="bold", color="#0f172a", pad=8)
ax1.set_xlabel(r"Matrix dimension $n$", fontsize=9.5)
ax1.set_ylabel(r"Step gain $\Delta_n$ (log scale)", fontsize=9.5)
ax1.set_xticks(ns)
ax1.set_ylim(1.2e-9, 1.8e-4)
ax1.grid(True, which="major", alpha=0.7)
ax1.legend(loc="upper right", fontsize=8.2)
ax1.text(3.08, 2.7e-9,
         "For $p \\geq 2$ (Qiu 2026): $\\Delta_n \\equiv 0$ for all $n \\geq 3$\n"
         "For $1 < p < 2$: $\\Delta_n > 0$ for every $n \\geq 2$ (Thm. 1)",
         fontsize=7.8, color="#334155",
         bbox=dict(boxstyle="round,pad=0.35", facecolor="#f8fafc", edgecolor="#cbd5e1", lw=0.7))

# Panel (b): Eigenvalue cascade at n = 8 with crisp, non-overlapping labels
ks = [1, 2, 3, 4]
for key in ["5/4", "4/3", "3/2"]:
    r8 = [r for r in data[key] if r["n"] == 8][0]
    ax2.semilogy(ks, r8["evA"], **styles[key])

halo = dict(boxstyle="round,pad=0.14", facecolor="#ffffff", edgecolor="none", alpha=0.88)
ann_pos = {
    ("5/4", 1): (14, 11, "left"),
    ("5/4", 2): (8,  10, "left"),
    ("5/4", 3): (-2, 9,  "center"),
    ("4/3", 1): (14, -4, "left"),
    ("4/3", 2): (10, -5, "left"),
    ("4/3", 3): (-10,-9, "right"),
    ("3/2", 1): (-8, -14,"right"),
    ("3/2", 2): (-4, -14,"center"),
    ("3/2", 3): (-2, -14,"center"),
}
for key in ["5/4", "4/3", "3/2"]:
    r8 = [r for r in data[key] if r["n"] == 8][0]
    evs = r8["evA"]
    for idx in [1, 2, 3]:
        dx, dy, ha = ann_pos[(key, idx)]
        ax2.annotate(f"{evs[idx]:.2e}", (ks[idx], evs[idx]),
                     textcoords="offset points", xytext=(dx, dy),
                     ha=ha, fontsize=7.3, color=styles[key]["color"], bbox=halo)

ax2.set_title(r"(b) Eigenvalue Cascade of $|A|, |B|$ at $n = 8$ (rank $4$)",
              fontsize=9.8, fontweight="bold", color="#0f172a", pad=8)
ax2.set_xlabel(r"Eigenvalue index $k$ (normalized by $\lambda_1$)", fontsize=9.5)
ax2.set_ylabel(r"$\lambda_k(|A|) / \lambda_1(|A|)$", fontsize=9.5)
ax2.set_xticks(ks)
ax2.set_xticklabels([r"$\lambda_1$", r"$\lambda_2$", r"$\lambda_3$", r"$\lambda_4$"])
ax2.set_xlim(0.82, 4.35)
ax2.set_ylim(2.2e-6, 2.8)
ax2.grid(True, which="major", alpha=0.7)
ax2.legend(loc="upper right", fontsize=8.0)

plt.tight_layout(pad=1.2)
fig.savefig("/home/marcio/Projects/mi20-subquadratic-lee/fig1_staircase_cascade.pdf", bbox_inches="tight")
fig.savefig("/home/marcio/Projects/mi20-subquadratic-lee/fig1_staircase_cascade.png", dpi=250, bbox_inches="tight")
print("Regenerated clean fig1_staircase_cascade.pdf and .png")
