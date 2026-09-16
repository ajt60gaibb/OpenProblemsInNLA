# IE-04 — Exponential smoothed tail bounds for partial pivoting

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Solved  
**Last checked:** 2026-09-11  

**Rating rationale:** Extreme reflects a uniform tail bound over adversarial matrix centers, beyond current average-case analysis; broad impact is justified by explaining the stability of a standard dense solver.

## Resolution — 11 September 2026

**Solved negatively.** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, gives a counterexample to the displayed universal exponential tail. The [complete proof's theorem, equation (2), and robustness lemma](solution.md) show that, for every $`n\ge2`$,

```math
\Pr\!\left\{\rho_{\mathrm{PP}}(I_n+G)>\tfrac12(3/2)^{n-1}\right\}
\ge 2^{-n^2(n^2+n+5)}.
```

For any proposed $`c_1,c_2>0`$, take $`\bar A=I_n`$, $`\sigma=1`$ and $`x=(3/2)^{n-1}/(2n^{c_1})`$. Sufficiently large $`n`$ give an admissible $`x\ge1`$ and violate the proposed upper bound. This covers the exact real Gaussian model and every proposed universal pair; the event has strict pivot choices and nonsingular matrices. The conclusion uses the unrestricted range of $`x`$ and does not address a different tail restricted to smaller $`x`$.

[Proof PDF](solution.pdf) · [Standalone source](solution.tex) · [Independent complete-proof review](../../references/stepaniants-ie04-2026-09-11/verification/IE-04-independent-review.md) · [Submission and verification record](../../references/stepaniants-ie04-2026-09-11/README.md). AI assistance and automated-review limits are disclosed. The permanent ID, original statement, and historical ratings below are retained.

## Context and notation

All elimination in this problem is in exact arithmetic. Write $`\|A\|_{\max}=\max_{ij}|a_{ij}|`$. A pivoting path creates successive active Schur complements $`S_1=A,S_2,\ldots,S_n`$, with row/column permutations as appropriate. Its element-growth factor is

```math
\rho(A)=\frac{\max_{1\leq j\leq n}\|S_j\|_{\max}}{\|A\|_{\max}}.
```

Partial pivoting chooses a largest-magnitude entry in the active first column; complete pivoting chooses one anywhere in the active matrix. If ties occur, a universal statement includes every admissible tie choice; a supremum includes all admissible paths. These conventions remove implementation-dependent ambiguity. Matrices are nonsingular unless otherwise stated.

## Problem statement

Do universal constants $`c_1,c_2>0`$ exist such that, for every $`n\geq1`$, deterministic $`\bar A\in\mathbb R^{n\times n}`$ with $`\|\bar A\|_2\leq1`$, $`0<\sigma\leq1`$, and $`x\geq1`$, the matrix $`A=\bar A+\sigma G`$, with independent standard normal entries in $`G`$, satisfies

```math
\Pr\!\left\{\rho_{\mathrm{PP}}(A)>x(n/\sigma)^{c_1}\right\}
\leq 2^{-c_2x}?
```

This is a uniform smoothed-analysis question: the deterministic center may itself be a worst-case input. Almost surely the perturbed matrix is nonsingular and the pivot choices have no ties. Numerical evidence or estimates only at $`\bar A=0`$ do not settle the quantifier over deterministic centers. The tail estimate would quantify the rarity of substantial growth after small Gaussian input perturbations.

## References

Spielman and Teng, [*Smoothed Analysis of Algorithms and Heuristics: Progress and Open Questions*](https://www.cs.yale.edu/homes/spielman/PAPERS/focmSmoothed.pdf), §P6, Conjecture 16, p. 52 of the author PDF; in *Foundations of Computational Mathematics, Santander 2005* (2006), 274–342, [chapter DOI](https://doi.org/10.1017/CBO9780511721571.010). Huang and Tikhomirov, [*Average-case analysis of the Gaussian elimination with partial pivoting*](https://doi.org/10.1007/s00440-024-01276-2), PTRF 189 (2024), introduction.

## Earlier status check — 2026-09-08

Searches for `Exponential Stability of GEPP solved` and `Gaussian elimination smoothed analysis 2025 2026` found the average-case theorem, not this exponential tail bound. The 2026 Peca-Medlin butterfly paper also distinguishes average-case results from the still-unavailable full smoothed analysis. Randomizing the pivot rule is a different model.

## Audit update — 2026-09-10

The linked Spielman–Teng chapter was checked against the [author bibliography](https://www.cs.yale.edu/homes/spielman/SmoothedAnalysis/surveys.html): its title has been corrected in the reference, with Conjecture 16 unchanged. [Huang–Tikhomirov](https://link.springer.com/article/10.1007/s00440-024-01276-2) explicitly discusses the obstruction to extending its Gaussian result to arbitrary centers. Searches for exponential GEPP tails and subsequent smoothed-analysis results found no theorem with the displayed uniform quantifiers.
