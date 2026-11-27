# MI-20 — Sharp subquadratic Lee constants for sums of matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-11-27

**Rating rationale:** Determining a sharp two-parameter function after the proposed formula failed is challenging; matrix-sum bounds affect norm estimates used across NLA.

## Structural non-attainment and exact 2×2 collapse — 27 November 2026

**Author:** Marcio Diaz (Space AI). [Preprint PDF](../../references/diaz-mi20-2026-11-27/mi20_subquadratic_lee_whitepaper.pdf) · [Zenodo DOI 10.5281/zenodo.24591861](https://doi.org/10.5281/zenodo.24591861) · [Submission and reproduction scripts](../../references/diaz-mi20-2026-11-27/README.md).

The manuscript proves four structural results for every $`1 < p < 2`$ and every $`m \ge 2`$: (i) the finite-dimensional optimal constants form a strictly increasing infinite sequence $`1 = C_{p,m}(1) < C_{p,m}(2) < \cdots < C_{p,m}(n) < C_{p,m}(n+1) < \cdots < C_{p,m}(\infty)`$ over both $`\mathbb{C}`$ and $`\mathbb{R}`$ (Theorem 1, settling Qiu's dimensional-growth conjecture and transferring via Xing Li's Theorem 1.1 to concave-function Lee constants in Corollary 1); (ii) on any infinite-dimensional separable Hilbert space $`\mathcal{H}`$, no tuple in $`(\mathcal{S}_p(\mathcal{H}))^m`$ containing any finite-rank operator can attain $`C_{p,m}(\infty)`$ (Theorem 2); (iii) universal $`2\times 2`$ collapse $`C_{p,m}(2) = C_{p,m}^{\mathbb{R}}(2) = C_{p,2}(2)`$ for all $`m \ge 2`$ and all $`p > 1`$, with exact closed form $`C_{3/2,m}(2) = ((107 + 51\sqrt{17})/256)^{1/6}`$ and monic cubic evaluation $`z^3 - z^2 - 4z + 2 = 0`$ at $`p = 4/3`$ giving $`C_{4/3,m}(2) \approx 1.0183023754`$ (Theorem 3); and (iv) explicit small-integer $`2\times 3`$ pairs at $`p \in \{3/2, 4/3, 5/4\}`$ strictly surpassing $`C_{p,m}(2)`$, verified without floating-point arithmetic by pure Python standard-library rational certificates (Theorem 4). Proposition 5 shows that kernel lifting extends to all $`p \ge 2`$, forcing $`\ker(S) \cap \operatorname{ran}(H) \neq \{0\}`$ at every superquadratic finite-dimensional maximizer and pinpointing Lemma 2 as the mechanism of the $`p = 2`$ phase transition.

Status remains **Open**: these theorems resolve finite-dimensional and finite-rank non-attainment but do not determine an explicit formula for $`C_p(m) = C_{p,m}(\infty)`$ across $`1 < p < 2`$ and $`m \ge 2`$. Author submission with exact zero-float rational and symbolic verification scripts and informal AI-assisted proof audit; no external human peer review or Lean formalization was performed.

## Reviewed continuation — 13 September 2026

Sidney Holden (Center for Computational Biology, Flatiron Institute, Simons Foundation) supplies the uniform bound $`C_{4/3}(2)\le(861/800)^{1/4}`$ and interpolated two-summand bounds in the [corrected fourth-round report](../../references/holden-continuations-2026-09-13/MI-20/report.pdf), interval certificate and interpolation sections. Exact rational certificates cover a full parameter interval in every matrix order; numerical optimizers are not the proof. The independent review identified and corrected the conjugation in the cyclic-reduction construction before accepting the publication version.

Status remains **Open**: the bounds do not match, and the exact function for every $`m\ge2`$ and $`1< p<2`$ remains undetermined. The positive power-system characterization is a reduction, not an evaluation of that function.

The [independent informal Codex AI-agent review](../../references/holden-continuations-2026-09-13/verification/MI-20/review.md) records its accepted scope and checks. [Submission, original package, reproduction and verified affiliation](../../references/holden-continuations-2026-09-13/README.md). This is not external human peer review or formal verification; no Lean verification was performed.


## Audited dual and projective reductions — 12 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Submission and verified affiliation](../../references/holden-matrix-2026-09-12/README.md).

[Sections 1–4](../../references/holden-matrix-2026-09-12/MI-20/result.md) give the known positive dual formulation (Qiu, Proposition 3.1), a fixed-dimension binary projection reduction, and an all-summands projective dilation preserving the supremum over dimensions. These lemmas do not determine $`C_p(m)`$ for the requested parameter range; the target remains Open.

A separate [independent Codex AI-agent audit](../../references/holden-matrix-2026-09-12/verification/MI-20-MI-27-review.md) passed this limited scope. This is informal automated review; no complete resolution, historical novelty, external human peer review or formal verification is claimed. No Lean verification was performed.

## Problem statement

For a complex square matrix $`X`$, write $`|X|=(X^*X)^{1/2}`$ and $`\|X\|_p=(\mathop{\mathrm{tr}}\nolimits|X|^p)^{1/p}`$. For every integer $`m\ge2`$ and real $`1< p<2`$, determine exactly the dimension-independent constant

```math
C_p(m)=\sup_{n\ge1}\ \sup_{A_1,\ldots,A_m\in\mathbb C^{n\times n},\,\sum_j|A_j|\ne0}
\frac{\|\sum_{j=1}^m A_j\|_p}{\|\sum_{j=1}^m|A_j|\|_p}.
```

Thus the requested answer is the optimal constant, as a function of both $`p`$ and $`m`$, in the corresponding Schatten norm inequality. An upper bound alone does not settle the problem. All matrix orders are included in the same supremum.

These constants quantify the loss when replacing a matrix sum by the sum of its positive semidefinite moduli, an operation common in norm estimates for matrix computations. This is distinct from constants comparing the arithmetic and symmetric moduli of one matrix (catalog MI-09).

## References

1. X. Li, *Sharp Concave-Function Transfer for Lee-Type Schatten Norm Inequalities*, arXiv:2608.25989v1 (2026), §1, equations defining the linear constants, and §4, Problem 4.2. [Full text](https://arxiv.org/html/2608.25989).
2. Q. Tang and S. Zhang, *Generalizing Lee's conjecture on the sum of absolute values of matrices*, Linear Algebra Appl. 731 (2026), 196–204, original candidate and endpoint results. [Preprint](https://arxiv.org/abs/2510.16846).
3. H. Qiu, *Sharp quasi-reverse Minkowski inequality for Schatten norms* (2026), the two-matrix sharp result for $`p\ge2`$ and counterexamples in the subquadratic interval. [Preprint](https://arxiv.org/abs/2608.17565).

Status check (2026-09-10): Li's current v1, dated August 26, explicitly retains this problem after proving equality of the sharp linear and concave-function constants. Its §4 records failure of the Tang–Zhang candidate throughout $`1< p<2`$. Searches for the exact title, “Lee sharp Schatten constants”, and “Tang Zhang conjecture” with 2025/2026 found no later determination of this entire function. This is a bounded literature check, not a guarantee against an unindexed solution.
