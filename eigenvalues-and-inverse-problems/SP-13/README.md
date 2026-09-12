# SP-13 — Trace-norm-small perturbations preserve Hermitian spectral distributions

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Non-Hermitian perturbations and spectral distributions  
**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solved
**Last checked:** 2026-09-11

**Historical ratings:** The difficulty and importance describe the original open question.

**Rating rationale:** Removing all spectral-norm bounds requires control of nonnormal spectra under potentially large perturbations. The result would extend spectral analysis of discretization matrices and preconditioners with unbounded coefficients.

## Resolution

**Solved affirmatively, 11 September 2026.** The [Theorem in Section 1, proved in Sections 2-5](solution.md) establishes the complete displayed conjecture: arbitrary complex perturbations with trace norm $o(n)$ preserve the prescribed Hermitian spectral distribution, without spectral-norm bounds on either sequence and without normality of the perturbed matrices. [Proof PDF](solution.pdf) · [Standalone TeX](solution.tex).

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

The proof applies the published dimension-independent weak-type triangular-truncation estimate of Randrianantoanina, Theorem 4.8, printed page 23 ([DOI](https://doi.org/10.4064/cm91-1-2)), to a Schur decomposition. Elementary singular-value counting and Hermitian rank-perturbation estimates then prove convergence for every original compactly supported continuous test function. The published weak-type theorem and the Barbarino-Serra-Capizzano conjecture retain their original attribution.

The full argument passed a separate [independent Codex-agent mathematical review](../../references/stepaniants-sp13-2026-09-11/verification/SP-13-independent-review.md) and a [coordinating-agent audit](../../references/stepaniants-sp13-2026-09-11/verification/SP-13-root-math-review.md). It was developed with substantial ChatGPT/Codex assistance. This is informal automated-agent review, not external human peer review or Lean/formal verification. The [submission record](../../references/stepaniants-sp13-2026-09-11/README.md) preserves the exact source, primary-source checks and bounded public eligibility audit. The original statement and the preceding partial-results history are retained below.

## Statement

For a sequence $A_n\in\mathbb C^{n\times n}$ and a measurable function $f:[0,1]\to\mathbb R$, write $\{A_n\}\sim_\lambda f$ if

$$
\lim_{n\to\infty}\frac1n\sum_{j=1}^n F(\lambda_j(A_n))
=\int_0^1 F(f(t))\,dt
\qquad\text{for every }F\in C_c(\mathbb C),
$$

where $C_c(\mathbb C)$ denotes the continuous complex-valued functions of compact support, and eigenvalues are counted with algebraic multiplicity. Define the trace norm by $\|E\|_*:=\sum_j\sigma_j(E)$.

**Conjecture (Barbarino–Serra-Capizzano).** For every Hermitian sequence $H_n=H_n^*$ with $\{H_n\}\sim_\lambda f$, and every sequence $E_n\in\mathbb C^{n\times n}$ satisfying $\|E_n\|_*/n\to0$, one has

$$\{H_n+E_n\}\sim_\lambda f.$$

Neither sequence is assumed uniformly bounded in spectral norm; $H_n+E_n$ need not be normal. The unit interval is a distributional normalization of the source's general finite-measure symbol domain.

## Known cases and numerical significance

The conclusion is proved if $\|E_n\|_F=o(\sqrt n)$, and also if $\|E_n\|_*=o(n)$ and $\sup_n\|E_n\|_2<\infty$. Here $\|\cdot\|_F$ and $\|\cdot\|_2$ denote Frobenius and spectral norms. The conjecture retains the trace-norm assumption while removing the latter uniform bound. It concerns the limiting empirical distribution, not individual-eigenvalue matching.

Spectral symbols describe large matrix sequences arising in PDE discretization and preconditioning. The source's equivalent GLT and diagonal formulations are grouped with this target rather than assigned separate IDs.

## References and status check

- G. Barbarino and S. Serra-Capizzano, *Non-Hermitian perturbations of Hermitian matrix-sequences and applications to the spectral analysis of the numerical approximation of partial differential equations*, Numerical Linear Algebra with Applications 27 (2020), e2286. [DOI](https://doi.org/10.1002/nla.2286); [author PDF](https://giovannibarbarino.github.io/doc/articles/NHperturbation.pdf). Conjecture 1 in §6, printed p.29; Theorem 1 and Corollary 3 give the stated partial results.
- G. Barbarino, *Conjectures on Perturbations of Hermitian Sequences*, [arXiv:1808.05555v1](https://arxiv.org/abs/1808.05555v1), Conjecture 1 and Lemma 4.2. This supplies equivalent versions of the same target.
- G. Barbarino and C. Garoni, *GLT sequences and normal matrices*, Electronic Journal of Linear Algebra 41 (2025), 1–20. [Theorem 3.2](https://journals.uwyo.edu/index.php/ela/article/download/8929/6949/23285) requires smaller perturbations when the sum is not normal, so it does not settle this conjecture.

On 2026-09-11, checked these primary statements, the authors' publication lists, and targeted title, trace-norm, spectral-distribution, proof and counterexample searches. No full resolution was located. The surviving evidence is a bounded literature check; the 2025 normal-sequence theorem is not presented as a new proof of openness.
