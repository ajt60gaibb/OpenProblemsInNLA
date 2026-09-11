#!/usr/bin/env python3
"""Finite diagnostics for MF-05/MF-07; the manuscript is the universal proof.

Checks the exact damping identity, its real/complex norm inequality, and
all-threshold comparison bounds for ill-conditioned diagonal similarities.
No joint-spectral-radius value is inferred from a finite random search.
"""
from __future__ import annotations
import argparse
import datetime as dt
import json
import math
from pathlib import Path
import numpy as np
import sympy as sp

if not __debug__:
    raise RuntimeError("Run this verifier without -O: assertions are part of the checks")


def norm2(a: np.ndarray) -> float:
    return float(np.linalg.norm(a, 2))


def exact_damping_identity() -> dict:
    sizes = [2, 1, 2]
    ids = [j for j, size in enumerate(sizes) for _ in range(size)]
    x = sp.Matrix(5, 5, lambda i, j: sp.Rational((i + 2) * (j + 3) - 7, i + j + 1)
                  if ids[i] >= ids[j] else 0)
    hs = [sp.Rational(12), sp.Rational(4), sp.Rational(1)]
    h = sp.diag(*[hs[i] for i in ids])
    y = x
    for cut in range(2):
        t = hs[cut + 1] / hs[cut]
        s = sp.diag(*[1 if block <= cut else -1 for block in ids])
        y = (1 + t) * y / 2 + (1 - t) * s * y * s / 2
    assert y == h * x * h.inv()
    return {"arithmetic": "exact SymPy rational", "identity_passed": True,
            "block_sizes": sizes, "block_scalars": [str(h) for h in hs]}


def random_damping(rng: np.random.Generator, count: int) -> dict:
    max_ratio = 0.0
    max_identity_error = 0.0
    for trial in range(count):
        d = int(rng.integers(2, 15))
        cuts = rng.random(d - 1) < 0.5
        ids = np.r_[0, np.cumsum(cuts)]
        blocks = int(ids[-1]) + 1
        logh = np.r_[np.cumsum(rng.uniform(0, 12, max(0, blocks - 1)))[::-1], 0.0]
        # The preceding reverse cumulative list is decreasing; a single block gives [0].
        x = rng.standard_normal((d, d))
        if trial % 2:
            x = x + 1j * rng.standard_normal((d, d))
        x = np.where(ids[:, None] >= ids[None, :], x, 0)
        y = x * np.exp(logh[ids, None] - logh[None, ids])
        z = x.copy()
        for cut in range(blocks - 1):
            t = math.exp(logh[cut + 1] - logh[cut])
            signs = np.where(ids <= cut, 1.0, -1.0)
            z = ((1 + t) / 2) * z + ((1 - t) / 2) * (signs[:, None] * z * signs[None, :])
        ratio = norm2(y) / norm2(x)
        err = norm2(y - z) / max(1.0, norm2(y))
        assert ratio <= 1 + 2e-12, (trial, ratio)
        assert err <= 2e-12, (trial, err)
        max_ratio = max(max_ratio, ratio)
        max_identity_error = max(max_identity_error, err)
    return {"trials": count, "real_and_complex": True,
            "maximum_norm_ratio": max_ratio,
            "maximum_relative_identity_error": max_identity_error}


def finite_horizon(rng: np.random.Generator, count: int) -> dict:
    worst = {"truncation_bound_ratio": 0.0, "new_error_bound_ratio": 0.0,
             "damping_product_ratio": 0.0, "new_product_bound_ratio": 0.0,
             "similarity_identity_relative_error": 0.0}
    wide_cases = 0
    for trial in range(count):
        d = int(rng.integers(2, 11))
        n = int(rng.integers(1, 61))
        logs = rng.choice([0.0, math.log(1.2), math.log(2), math.log(100),
                           math.log(1e6), math.log(1e12)], d - 1)
        logd = np.r_[np.cumsum(logs[::-1])[::-1], 0.0]
        scale = np.exp(logd[:, None] - logd[None, :])
        family = []
        for _ in range(3):
            raw = rng.standard_normal((d, d)) / d
            if trial % 2:
                raw = raw + 1j * rng.standard_normal((d, d)) / d
            # Large old-coordinate lower entries; small upper entries.
            b = np.where(np.arange(d)[:, None] < np.arange(d)[None, :], raw / scale, raw)
            family.append(b)
        ortho, _ = np.linalg.qr(rng.standard_normal((d, d)))
        metric = (ortho * np.linspace(1, d, d)) @ ortho.T
        imetric = np.linalg.inv(metric)
        a = max(norm2(metric @ b @ imetric) for b in family)
        family = [b / a for b in family]
        afamily = [b * scale for b in family]
        L = max(0.5, *(norm2(a) for a in afamily))
        # Include s=1, arbitrary thresholds, and the former horizon-specific choice.
        if trial % 3 == 0:
            s = 1.0
        elif trial % 3 == 1:
            s = math.exp(rng.uniform(0.0, math.log(1e9)))
        else:
            s = d * d * L * n   # a=1 after normalization
        u = 1.0 + d*d*L/s
        wide = logs > math.log(s)
        ids = np.r_[0, np.cumsum(wide)]
        if np.any(wide):
            wide_cases += 1
        newlogs = np.minimum(logs, math.log(s))
        logdp = np.r_[np.cumsum(newlogs[::-1])[::-1], 0.0]
        logh = logd - logdp
        hscale = np.exp(logh[:, None] - logh[None, :])
        mask = ids[:, None] < ids[None, :]
        cs, cps, eps, bps = [], [], [], []
        for b in family:
            e = np.where(mask, b, 0)
            c = b - e
            ep = e * hscale
            cp = c * hscale
            bp = b * hscale
            ratio_e = norm2(metric @ e @ imetric) / (d*d*L/s)
            ratio_ep = norm2(ep) / (d*L/s)
            assert ratio_e <= 1 + 2e-11, (trial, "old perturbation", ratio_e)
            assert ratio_ep <= 1 + 2e-11, (trial, "new perturbation", ratio_ep)
            worst["truncation_bound_ratio"] = max(worst["truncation_bound_ratio"], ratio_e)
            worst["new_error_bound_ratio"] = max(worst["new_error_bound_ratio"], ratio_ep)
            cs.append(c); cps.append(cp); eps.append(ep); bps.append(bp)
        word = rng.integers(0, len(family), n)
        pc = np.eye(d, dtype=family[0].dtype)
        pcp = pc.copy(); pbp = pc.copy(); pa = pc.copy()
        for length, index in enumerate(word, 1):
            pc = cs[index] @ pc
            pcp = cps[index] @ pcp
            pbp = bps[index] @ pbp
            pa = afamily[index] @ pa
            assert math.log(max(norm2(pc), np.finfo(float).tiny)) <= math.log(d) + length*math.log(u) + 2e-10
            damping = norm2(pcp) / max(norm2(pc), np.finfo(float).tiny)
            assert damping <= 1 + 2e-10, (trial, length, damping)
            worst["damping_product_ratio"] = max(worst["damping_product_ratio"], damping)
        ratio_final = math.exp(math.log(max(norm2(pbp), np.finfo(float).tiny)) - math.log(d) - n*math.log1p(2*d*d*L/s))
        assert ratio_final <= 1 + 2e-10
        worst["new_product_bound_ratio"] = max(worst["new_product_bound_ratio"], ratio_final)
        reconstruct = pbp * np.exp(logdp[:, None] - logdp[None, :])
        err = norm2(reconstruct - pa) / max(1.0, norm2(pa))
        assert err <= 2e-9, (trial, err)
        worst["similarity_identity_relative_error"] = max(worst["similarity_identity_relative_error"], err)
    return {"trials": count, "wide_gap_trials": wide_cases,
            "dimensions": "2 through 10", "horizons": "1 through 60", "thresholds": "1; log-uniform on [1, 1e9]; d^2 L n",
            "real_and_complex": True, "worst_diagnostic_ratios": worst}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=260911507)
    parser.add_argument("--damping-trials", type=int, default=10000)
    parser.add_argument("--horizon-trials", type=int, default=1000)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("triangular_comparison_checks.json"))
    args = parser.parse_args()
    if args.damping_trials < 1 or args.horizon_trials < 1:
        parser.error("trial counts must be positive")
    started_utc = dt.datetime.now(dt.timezone.utc).isoformat()
    rng = np.random.default_rng(args.seed)
    result = {"status": "all diagnostics passed; not a substitute for proof", "seed": args.seed,
              "exact_check": exact_damping_identity(),
              "damping": random_damping(rng, args.damping_trials),
              "quantitative_comparison": finite_horizon(rng, args.horizon_trials)}
    result["started_utc"] = started_utc
    result["completed_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
