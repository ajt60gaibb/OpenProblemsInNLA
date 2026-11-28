# MI-20 — Sharp subquadratic Lee constants for sums of matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-11-28

**Rating rationale:** Determining a sharp two-parameter function after the proposed formula failed is challenging; matrix-sum bounds affect norm estimates used across NLA.

## Spectral-pencil trace-class proofs, Bogomolny identities, Hirota solitons, zero-float multi-summand enclosures, BCH record, and 73-theorem Lean 4 formalization — 28 November 2026

**Author:** Marcio Díaz (Space Research AI). [Version 5 PDF](../../references/diaz-mi20-v5-2026-11-28/mi20_subquadratic_lee_whitepaper.pdf) · [Zenodo DOI 10.5281/zenodo.24621394](https://doi.org/10.5281/zenodo.24621394) · [GitHub repository](https://github.com/spaceresearchai/mi20-subquadratic-lee) · [Submission, Lean 4 project, and zero-float certificates](../../references/diaz-mi20-v5-2026-11-28/README.md).

Expanding the structural non-attainment manuscript below (and fixing the singular-vector direction slip in Theorem 2, Step 1), Version 5 develops a complete 22-theorem structural, variational, integrable-operator, and formally verified framework for Problem MI-20. Theorems 5–8 prove fixed-dimension unitary-free PSD/POVM reformulations via Same-Dimension Lemma 2' (Theorem 5), formalize Holden's complex-interpolation log-convexity at fixed finite dimension $`n`$ (Theorem 6), establish a concentration-compactness dichotomy ruling out mass splitting in $`(\mathcal{S}_p(\ell^2))^m`$ (Theorem 7) and the exact two-term $`p \to 1^+`$ quadratic law in dimension $`2`$ (Proposition 8), and prove unconditionally that any attaining tuple in $`(\mathcal{S}_p(\mathcal{H}))^m`$ satisfies $`\ker(S) \cap \overline{\mathop{\mathrm{ran}}\nolimits(H)} = \{0\}`$, onto-isometric polar factors $`U_k U_k^* = I_{\overline{\mathop{\mathrm{ran}}\nolimits(H)}}`$, and $`0 \in \sigma(H^{-1/2}|A_k|H^{-1/2})`$ (Theorem 8).

On Holden's positive power system $`(D + H_j)^{2\kappa-1} = \Lambda D^{1/2} G_j^{\kappa-1} D^{1/2}`$ ($`\kappa = \frac{p}{2(p-1)}`$, $`\Phi_j = G_j^\kappa - D G_j^{\kappa-1} D`$), Theorems 9 and 10–10C (all Lean 4 verified) establish the commutator identity $`[D, \Phi_j] = 0`$, the Power-Variance Lemma, the Top-Eigenspace Spectral Dichotomy, and four progressively sharper pure-algebraic universal upper bounds across all $`1 < p < 2`$ and $`m \ge 2`$: the dimension-free quadratic log bound $`\ln C_{p,m}(\infty) \le \frac{m^2-1}{2p^2}(p-1)^2`$, the Frobenius-exact one-line bound, the $`C^\infty`$-flat super-exponential collapse law $`0 < C_{p,2}(\infty) - C_{p,2}(2) = O\bigl((1+\sqrt{2})^{-\frac{2(p-1)}{2-p}}\bigr)`$ (pinning $`C_{1.95,2}(\infty)`$ to 14 digits and beating Holden by $`471\times`$ at $`p = 7/4`$), and a two-line Bessel bound at $`p = 4/3`$. Theorems 11–13 deliver zero-float certified $`42\times 42`$ self-similar tree lower bounds ($`C_{4/3,2}(\infty) > 1.0183715755`$, $`C_{3/2,2}(\infty) > 1.03643716806`$), Two-State Pinch convex-trapezoid upper bounds ($`C_{4/3,2}(\infty) \le (21511/20000)^{1/4} \approx 1.0183748167`$, $`52.1\times`$ tighter than Holden; $`C_{3/2,2}(\infty) \le (890677/800000)^{1/3} \approx 1.0364382131`$, $`7{,}795\times`$ tighter, gap $`1.05\times 10^{-6}`$), and the exact $`p \to 1^+`$ Baker–Campbell–Hausdorff (BCH) operator limit $`\mathop{\mathrm{Dexp}}\nolimits_{-M_j}[U_j^2] = 4a_L e^{-M_j} - 2\Phi_{\lim,j}`$.

New in Version 5, Theorems 14–16 establish the Quantitative Power-Variance Lemma, the Universal Spectral-Gap Operator Inequality $`\Phi \preceq D^\kappa(I-D)`$ (with infinite-dimensional Weyl-sequence proof), exact rational 2-vector spectral-gap certificates, Action-Ray Convexity, exact Action-Functional and Bogomolny/SOS identities at $`p \in \{4/3, 3/2\}`$ with Universal Vacuum Positivity $`\mathcal{W}_\Lambda \ge 0`$ across $`1 < p \le 2`$, and a 12-line pure-algebraic Spectral-Pencil Trace-Class Theorem proving $`\rho_{2\kappa}(s) < 1/2`$ and unconditional $`(\mathcal{S}_p(\ell^2))^m`$ attainment of $`\Lambda_{\mathrm{tree}}(\infty)`$ for all $`m \ge 2`$ at $`p \in \{4/3, 3/2\}`$ (alongside Single-Root GNS Limit and Polar Reconstruction). Theorem 17 proves a 3-line Grassmann Single-Block Master Trace Reduction and supplies four unconditional continuous-interval zero-float Bernstein multi-summand world records (Suite 5, `0/1` exact residuals): $`C_{4/3,3}(\infty) \le 1.0320685149`$ ($`4.26\times`$ tighter than V4 Thm 10C), $`C_{4/3,4}(\infty) \le 1.0430768362`$ ($`4.06\times`$), $`C_{3/2,3}(\infty) \le 1.0633400433`$ ($`5.91\times`$ tighter than V4 Thm 10B), and $`C_{3/2,4}(\infty) \le 1.0850902727`$ ($`4.36\times`$). Theorems 18–22 construct the exact Universal Hirota $`\tau`$-function soliton on $`L^2(\mathbb{R})`$ (17–22 digit benchmarks and negative PSLQ transcendence evidence); prove the 5th Universal Quadratic Moment Identity ($`C_{5/4,2}(\infty) \le 1.0125295904`$, $`2.55\times`$ tighter than Holden) and elementary analytic $`2\times 2`$ Master Trace proofs across $`p = 4/3, 3/2`$ and BCH for all $`m \ge 2`$; tighten the $`\mathcal{S}_{4/3}`$ tree contraction $`4\times`$ to $`\rho_4(s) < 1/8`$ via a Third-Root Hyperbolic Spectral Pencil; establish exact BCH Bogomolny SOS, a universal a priori norm cap $`\|V\|_{\mathrm{op}} \le 13.412`$, and the sharp unconditional BCH record $`K_2^{\mathrm{BCH}} < 0.3145`$ ($`348.4\times`$ larger breach of Theorem 10 than Theorem 19(b)'s Furuta-free $`0.31722794`$, certified by 35-digit outward-rounded `mpmath.iv`); and prove the Second-Order Sylvester Inertia Law, the $`m = 2`$ Euler–Betti root identity, zero-float full-V4-enclosure non-compact top-band exact splitting $`P_{\mathrm{top}} = P_1 \oplus P_2`$ (Suite 6), and explicit irreducible $`\mathbb{Z}/2N\mathbb{Z}`$-ring and $`\mathbb{Z}`$-lattice total-vanishing counterexamples with universal second-order refutation $`n_+(H_{\mathrm{full}}|_{\mathbb{S}^{6N}}) \ge 2N^2 + N - 1`$.

The accompanying Lean 4.33.1 + Mathlib formalization comprises 13 proof modules (15 `.lean` files, 23,947 lines, 73 audited top-level theorems across Theorems 1, 3–6, 9–10C, 14–17, 19, 20, and 22) with zero `sorry`, zero warnings, and standard axioms only. All numerical rational/interval bounds in Theorems 4, 11, 12, 17, and 22(c) are checked without floats in 84.9 s by `python3 -B -S verify_all_exact_certificates.py` (Suites 1–6), complemented by standalone pure-`mpmath` BCH verifiers `verify_bch_theorems_iv.py` and `verify_bch_closed_form.py`.

Status remains **Open**: proving exact global optimality of the infinite-tree fixed point for $`s \ge 3`$ across $`1 < p < 2`$ and $`m \ge 2`$, evaluating $`C_{p,m}(\infty)`$ in closed form, and ruling out total spectral vanishing for exact global maximizers remain open. The [audit and reproduction notes](../../references/diaz-mi20-v5-2026-11-28/README.md#audit-notes) record the Lean-verified vs. paper-only scope; no external human peer review or catalog-side independent Lean Comparator run has yet been performed.

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
