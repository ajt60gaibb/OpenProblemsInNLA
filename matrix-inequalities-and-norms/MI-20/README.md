# MI-20 — Sharp subquadratic Lee constants for sums of matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-11-27

**Rating rationale:** Determining a sharp two-parameter function after the proposed formula failed is challenging; matrix-sum bounds affect norm estimates used across NLA.

## Universal quadratic upper bound, infinite-tree extremizers, zero-float enclosures, and Lean 4 formalization — 27 November 2026

**Author:** Marcio Díaz (Space Research AI). [Version 3 PDF](../../references/diaz-mi20-v3-2026-11-27/mi20_subquadratic_lee_whitepaper.pdf) · [Zenodo DOI 10.5281/zenodo.24608035](https://doi.org/10.5281/zenodo.24608035) · [GitHub repository](https://github.com/spaceresearchai/mi20-subquadratic-lee) · [Submission, Lean 4 project, and zero-float certificates](../../references/diaz-mi20-v3-2026-11-27/README.md).

Expanding the structural non-attainment manuscript below (and fixing the singular-vector direction slip in Theorem 2, Step 1), Version 3 proves a fixed-dimension unitary-free PSD/POVM reformulation via Same-Dimension Lemma 2' (Theorem 5), formalizes Holden's complex-interpolation log-convexity at fixed finite dimension $`n`$ (Theorem 6), proves a concentration-compactness dichotomy ruling out mass splitting in $`(\mathcal{S}_p(\ell^2))^m`$ (Theorem 7), establishes the exact two-term $`p \to 1^+`$ quadratic law in dimension $`2`$ (Proposition 8), and shows unconditionally that any attaining tuple in $`(\mathcal{S}_p(\mathcal{H}))^m`$ satisfies $`\ker(S) \cap \overline{\mathop{\mathrm{ran}}\nolimits(H)} = \{0\}`$, onto-isometric polar factors $`U_k U_k^* = I_{\overline{\mathop{\mathrm{ran}}\nolimits(H)}}`$, and $`0 \in \sigma(H^{-1/2}|A_k|H^{-1/2})`$ (Theorem 8).

On Holden's positive power system $`(D + H_j)^{2\kappa-1} = \Lambda D^{1/2} G_j^{\kappa-1} D^{1/2}`$ ($`\kappa = \frac{p}{2(p-1)}`$, $`\Phi_j = G_j^\kappa - D G_j^{\kappa-1} D`$), Theorem 9 proves the commutator identity $`[D, \Phi_j] = 0`$ for each summand individually, a Power-Variance Lemma, and a Top-Eigenspace Spectral Dichotomy on $`E_{\max} = \ker(D - d_{\max}I)`$. Theorem 10 deduces the universal pure-algebraic upper bound $`\sigma_+(\Lambda) = h_+(\Lambda)^{\kappa-1}(h_+(\Lambda) - 1) \le (m-1)\frac{(\kappa-1)^{\kappa-1}}{\kappa^\kappa}`$ for all $`1 < p < 2`$ and $`m \ge 2`$, giving closed-form radical caps $`\Lambda \le \frac{13+16\sqrt{2}}{4} < \frac{891}{100}`$ ($`p = 4/3, m = 2`$) and $`\Lambda \le \frac{49\sqrt{3}}{18} < \frac{472}{100}`$ ($`p = 3/2, m = 2`$), the first dimension-free non-asymptotic quadratic bound $`\ln C_{p,m}(\infty) \le \frac{m^2-1}{2p^2}(p-1)^2`$, and the sharp asymptotic Lambert-$`W`$ constant $`K_m = \frac{c_m^2 + 2c_m}{2}`$ ($`c_m = W_0((m-1)/e)`$, $`K_2 \approx 0.317236`$).

Theorem 11 constructs self-similar infinite-tree extremizers on $`\ell^2(\mathcal{T}_s)`$ whose depth-2 ($`42\times 42`$) truncations yield zero-float certified lower bounds $`C_{4/3,2}(\infty) > 1.0183715755`$ and $`C_{3/2,2}(\infty) > 1.03643716806`$. Theorem 12 proves an unconditional Two-State Pinch 2-letter reduction whose zero-float exact rational $`LDL^\top`$ four-corner SOS certificates yield $`C_{4/3,2}(\infty) \le (17209/16000)^{1/4} \approx 1.0183777756`$ and $`C_{3/2,2}(\infty) \le (5567/5000)^{1/3} \approx 1.0364548918`$, tightening the best known certified upper bound across every $`1 < p < 2`$ at $`m = 2`$ when combined with Theorems 6 and 10. Theorems 1, 3 ($`1 < p < 2`$ and $`p = 3/2`$), 4 ($`p = 3/2`$), 5, 6 (from $`p_0 = 1`$), 9, and 10 (28 top-level theorems across 10 modules, 12,206 lines) are formalized in Lean 4.33.1 + Mathlib with zero `sorry` and standard axioms only, and all numerical bounds in Theorems 4, 11, and 12 are checked without floats by `python3 -B -S verify_all_exact_certificates.py`.

Status remains **Open**: proving exact global optimality and evaluating the infinite-tree fixed point across all $`1 < p < 2`$ and $`m \ge 2`$ remain open. The [audit and reproduction notes](../../references/diaz-mi20-v3-2026-11-27/README.md#audit-notes) record the Lean-verified vs. paper-only scope; no external human peer review or catalog-side independent Lean Comparator run has yet been performed.

## Structural non-attainment and exact 2×2 collapse — 27 November 2026

**Author:** Marcio Diaz (Space AI). [Preprint PDF](../../references/diaz-mi20-2026-11-27/mi20_subquadratic_lee_whitepaper.pdf) · [Zenodo DOI 10.5281/zenodo.24591861](https://doi.org/10.5281/zenodo.24591861) · [Submission and reproduction scripts](../../references/diaz-mi20-2026-11-27/README.md).

For every $`1 < p < 2`$ and $`m \ge 2`$, the optimal constants increase
strictly with matrix dimension over both the real and complex fields
(Theorem 1). This confirms the dimensional growth suggested in Qiu's §5.
Corollary 1 transfers the result to concave-function Lee constants using
Xing Li's Theorem 1.1. On an infinite-dimensional separable Hilbert space,
every summand of an attaining tuple would have to have infinite rank
(Theorem 2).

Theorem 3 determines the same $`2\times 2`$ constant over both fields
for every $`p > 1`$ and $`m \ge 2`$. It is independent of the number of
summands and gives $`C_{3/2,m}(2) = ((107 + 51\sqrt{17})/256)^{1/6}`$
and $`C_{4/3,m}(2) \approx 1.0183023754`$. Theorem 4 supplies explicit
integer $`2\times 3`$ witnesses above the $`2\times 2`$ optimum for
$`p \in \{3/2, 4/3, 5/4\}`$, with exact rational certificates.
Proposition 5 gives a rank obstruction for a finite tuple attaining the
dimension-independent constant at $`p \ge 2`$.

The dimension-independent constant $`C_p(m) = C_{p,m}(\infty)`$
remains undetermined across the requested range. The
[audit and reproduction notes](../../references/diaz-mi20-2026-11-27/README.md#audit-notes)
record the scope of the informal review.

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
