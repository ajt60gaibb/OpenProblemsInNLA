# IE-04 — Exponential smoothed tail bounds for partial pivoting

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Lean verified  
**Last checked:** 2026-09-15  

**Rating rationale:** Extreme reflects a uniform tail bound over adversarial matrix centers, beyond current average-case analysis; broad impact is justified by explaining the stability of a standard dense solver.

## Resolution — 11 September 2026

**Solved negatively.** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, gives a counterexample to the displayed universal exponential tail. The [complete proof's theorem, equation (2), and robustness lemma](solution.md) show that, for every $`n\ge2`$,

```math
\Pr\!\left\{\rho_{\mathrm{PP}}(I_n+G)>\tfrac12(3/2)^{n-1}\right\}
\ge 2^{-n^2(n^2+n+5)}.
```

For any proposed $`c_1,c_2>0`$, take $`\bar A=I_n`$, $`\sigma=1`$ and $`x=(3/2)^{n-1}/(2n^{c_1})`$. Sufficiently large $`n`$ give an admissible $`x\ge1`$ and violate the proposed upper bound. This covers the exact real Gaussian model and every proposed universal pair; the event has strict pivot choices and nonsingular matrices. The conclusion uses the unrestricted range of $`x`$ and does not address a different tail restricted to smaller $`x`$.

[Proof PDF](solution.pdf) · [Standalone source](solution.tex) · [Independent complete-proof review](../../references/stepaniants-ie04-2026-09-11/verification/IE-04-independent-review.md) · [Submission and verification record](../../references/stepaniants-ie04-2026-09-11/README.md). AI assistance and automated-review limits are disclosed. The permanent ID, original statement, and historical ratings below are retained.

## Lean proof and verification evidence — 15 September 2026

**Formalization: George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. The [immutable complete proof](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/026b3e5534a4d6e15ebffb85318c2ff031df32bf/linear-systems-and-elimination/IE-04/lean) verifies the full negative answer through 21 checked declarations, ending with `NLA.IE04.counterexample` and `NLA.IE04.not_uniformExponentialTail`. It covers arbitrary positive real $`c_1,c_2`$, actual Gaussian product measures, the full nonsingular perturbation box and every admissible partial-pivoting tie rule. The center $`I_n`$ and noise scale one are admissible witnesses; all original quantifiers are retained.

[Canonical non-root Linux run 35034399633](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35034399633/job/104600154206) accepted these exact proof bytes with Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. LeanCert checks the consumed scalar certificate $`e^{-2}>1/8`$ in kernel mode. Comparator, independent default-kernel replay and the required rejection and sandbox controls passed; only `propext`, `Classical.choice` and `Quot.sound` occur in the exported proofs.

[Project and reproduction instructions](lean/README.md) · [Original runtime evidence](lean/verification/linux-2026-09-15) · [Both independent final referee reports](lean/reviews/final) · [Formalization manifest](lean/formalization.yaml). Substantial AI assistance and scoped AI-agent review are disclosed. The checked proof revision is distinct from later documentation commits, whose publication workflow must run separately. No external human peer review or official Tau Ceti endorsement is asserted.

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
