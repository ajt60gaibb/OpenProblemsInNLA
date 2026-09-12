# MF-22 — Polynomial conditioning of the cubic C1 spline Schrödinger Toeplitz family

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Block Toeplitz systems and discretization stability  
**Difficulty:** hard  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-09-11

**Rating rationale:** Historical ratings retained. The fixed explicit band structure makes this a hard asymptotic question, but available symbol criteria leave the relevant regime undecided; its immediate importance is to specialists in structured discretization stability.

\pagestyle{plain}

## Resolution: affirmative, 11 September 2026

**George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology**, proves that for every fixed $\rho>0$ there are $K_\rho>0$ and $n_\rho$ such that

$$
\kappa_2(H_n(\rho))\le K_\rho n\qquad(n\ge n_\rho).
$$

Thus the original question is answered affirmatively with exponent $\alpha_\rho=1$. The result includes eventual invertibility, the parameter $\rho=\sqrt{10}$, and the exact uncorrected Toeplitz boundary entries. The original ID, full statement, and historical ratings are retained below.

The precise locator is the **Theorem in Section 1, proved in Sections 2–4** of the [complete manuscript](solution.md). [Proof PDF](solution.pdf) · [Standalone TeX](solution.tex). The proof derives a four-state recurrence, excludes all numerator cancellation, and bounds its finite Green matrix to obtain a linear inverse bound.

A separate [independent Codex-agent mathematical review](../../references/stepaniants-mf22-2026-09-11/verification/MF-22-independent-review.md) returned **PASS** for the complete target. The [submission record](../../references/stepaniants-mf22-2026-09-11/README.md) documents substantial ChatGPT/Codex assistance, exact symbolic checks, the public branch/fork audit, and verification limits. This is independent automated-agent review, not external human peer review or formal proof certification. The source authors retain credit for the family, the root classification and the question.

## Statement

Define real $2\times2$ matrices by

$$
\begin{aligned}
B_{-1}&=\frac3{40}\begin{pmatrix}-1&0\\-5&0\end{pmatrix},&
B_0&=\frac3{40}\begin{pmatrix}0&-5\\16&-5\end{pmatrix},\\
B_1&=\frac3{40}\begin{pmatrix}-5&16\\-5&0\end{pmatrix},&
B_2&=\frac3{40}\begin{pmatrix}0&-5\\0&-1\end{pmatrix},\\
C_{-1}&=\frac1{80}\begin{pmatrix}1&0\\7&0\end{pmatrix},&
C_0&=\frac1{80}\begin{pmatrix}24&7\\0&25\end{pmatrix},\\
C_1&=\frac1{80}\begin{pmatrix}-25&0\\-7&-24\end{pmatrix},&
C_2&=\frac1{80}\begin{pmatrix}0&-7\\0&-1\end{pmatrix}.
\end{aligned}
$$

Set $B_k=C_k=0$ for all other integer indices. For a real parameter $\rho>0$ and $n\ge1$, form the $2n\times2n$ complex block Toeplitz matrix

$$
H_n(\rho)=\bigl(iB_{j-k}-\rho C_{j-k}\bigr)_{j,k=0}^{n-1},
\qquad i^2=-1.
$$

Use the spectral condition number $\kappa_2(H)=\|H\|_2\|H^{-1}\|_2$ for nonsingular $H$ and $\kappa_2(H)=+\infty$ for singular $H$.

**Question (explicit asymptotic formulation of the source’s polynomial-growth question).** For every fixed $\rho>0$, do there exist constants $K_\rho>0$, $\alpha_\rho\ge0$, and $n_\rho\in\mathbb N$, independent of $n$, such that

$$
\kappa_2(H_n(\rho))\le K_\rho n^{\alpha_\rho}
\qquad\text{for every }n\ge n_\rho?
$$

The parameter remains fixed as $n\to\infty$; no uniform-in-$\rho$ bound or particular exponent is asserted. Eventual invertibility is part of the question. This is the exact pure Toeplitz family denoted $\widetilde{\mathbf S}_n^{(3,1)}(\rho)$ in the source; $n$ here counts its $2\times2$ blocks. It has no additional corner corrections.

## Numerical significance

These matrices arise from cubic splines with $C^1$ continuity in time for a space-time Schrödinger discretization. The source proves a determinant-root classification of the associated polynomial symbol but expressly leaves polynomial growth of these condition numbers open. The linear bound recorded above explains the numerical stability seen for this intermediate spline regularity.

## References and status check

- M. Bogoya, A. Böttcher, M. Ferrari, S. M. Grudsky and S. Serra-Capizzano, *Condition numbers of block Toeplitz matrices and stability of space-time IgA approximations for the wave and Schrödinger equations*, [arXiv:2608.24151v1](https://arxiv.org/abs/2608.24151v1), 25 August 2026. [Full text](https://arxiv.org/html/2608.24151v1): equation (5.22) gives $B_k$; §5.3, equation (5.32) and the following coefficient display give the family and $C_k$; the paragraph after Figure 9 and Remark 4.3 state the unresolved polynomial-growth issue.
- M. Ferrari and S. Gómez, *A matrix-based approach to the stability of a space-time isogeometric method for the linear Schrödinger equation*, [arXiv:2506.18859v2](https://arxiv.org/abs/2506.18859v2) (5 May 2026), abstract and introduction. Its analyzed method uses splines of maximal regularity, a different case from cubic $C^1$ splines.

On 2026-09-10, checked the complete August 2026 source, its version history, and targeted identifier/title/correction searches. Only v1 was listed, and no later proof or counterexample was found. This short, bounded follow-up search does not establish exhaustive openness. The source's more general claim involving only determinant-root counts is not needed for this particular, explicitly stated family.

The 2026-09-11 submission audit checked five public repositories and all 30 public branch heads, where MF-22 remained Open, and found no prior full solution in the checked documents or discussions. The [dated audit](../../references/stepaniants-mf22-2026-09-11/verification/network-check.json) records the scope and its limits. The source still listed only v1.
