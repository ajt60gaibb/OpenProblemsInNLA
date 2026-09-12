# [IE-04] A robust rare-event counterexample to the uniform exponential GEPP tail

### Affected entry

`linear-systems-and-elimination/IE-04/README.md`: the displayed smoothed inequality, quantified over every `x >= 1` and universal positive constants `c1,c2`.

### Correction or result

Proposed status: **Solution claimed (negative resolution; review requested).**

The submitted theorem proves, for real standard Gaussian `G`, every `n >= 2`, and either `C = 0` or `C = I_n`,

$$
\Pr\!\left\{\rho_{\mathrm{PP}}(C+G)>\frac12(3/2)^{n-1}\right\}
\geq 2^{-n^2(n^2+n+5)}\geq2^{-3n^4}.
$$

For arbitrary proposed `c1,c2 > 0`, set `x_n = (3/2)^(n-1)/(2*n^c1)`. Eventually `x_n >= 1` and `c2*x_n > n^2*(n^2+n+5)`, contradicting the requested upper bound.

The counterexample uses the deterministic center `Abar = I_n` and `sigma = 1`. This center is nonsingular and has spectral norm one. The high-growth matrix around which the rare event is defined is an event center, not the deterministic center of the smoothed model. The norm restriction is therefore respected. The additional case `C = 0` is not needed to satisfy the model assumptions. All elimination is in exact arithmetic, and the proof guarantees strictly largest pivots throughout the full perturbation box.

This gives a complete negative answer to the displayed unrestricted all-`x` bound. It does not settle a different tail with a restricted range of `x`, an optimal high-probability polynomial growth bound, or an expectation estimate.

### Evidence

`solution.pdf` / `solution.md` supplies the full analytic proof. Equation (3) defines the input pattern; Sections 3--4 prove the quantitative whole-box robustness and Gaussian probability lower bound; Section 5 contradicts every possible pair of constants.

Run `python verify_bounds.py` for supporting exact scalar checks and whole-box interval certificates. The default verifies orders 2 through 16 with strictly outward-rounded dyadic arithmetic. The finite computations supplement the dimension-uniform proof; they are not claimed to establish the theorem by themselves. The JSON certificate and passing transcript are supplied.

Source context: D. A. Spielman and S.-H. Teng, *Smoothed Analysis of Algorithms and Heuristics: Progress and Open Questions* (2006), Section P6, Conjecture 16, author-PDF page 52. DOI: `10.1017/CBO9780511721571.010`. Author PDF: https://www.cs.yale.edu/homes/spielman/PAPERS/focmSmoothed.pdf .

The prior interrupted work preserved an outline. This complete version was finished during recovery with substantial AI assistance. No external human review, proof-assistant certification, or novelty/priority claim is made. The accompanying eligibility audit records the inspected issue and PR material.

### Rating implications, if any

No rating change is requested before review. Following acceptance, append the negative resolution without replacing or deleting the original all-`x` target. Preserve its permanent ID and historical ratings. A revised, weaker conjecture should be clearly distinguished from the statement refuted here.
