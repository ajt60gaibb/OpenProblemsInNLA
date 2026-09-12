# IE-05 — Exact extremizers for partial pivoting on orthogonal matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-09-11  

**Rating rationale (historical):** Challenging reflects a global extremal problem with pivot-path constraints in every dimension; specialist impact concerns sharp constants on the orthogonal subclass.

## Negative resolution - 2026-09-11

**Solved.** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, gives an exact order-eight counterexample in the [complete proof](solution.md), **Theorem and Sections 1-4**. Let $\widetilde L=L_8+e_8e_2^T$, changing only its $(8,2)$ entry from $-1$ to $0$, and take its positive-diagonal QR factor $\widetilde Q$. Under the stipulated first-available-row tie rule,

$$
\rho_{\mathrm{PP}}(\widetilde Q)=\frac{5272}{63}
>\sqrt{\frac{17948132}{2601}}
=\rho_{\mathrm{PP}}(Q_8).
$$

The proof prints exact integer-column descriptions of both orthogonal matrices and verifies all active Schur-complement maxima. This disproves the universal extremizer equality. It does not determine the true orthogonal supremum or refute the separate asymptotic leading-constant conjecture. [Proof PDF](solution.pdf) · [Standalone TeX](solution.tex).

A separate [Codex-agent mathematical review](../../references/stepaniants-ie05-2026-09-11/independent-review.md) returned **PASS**, with independently written rational checks of both QR conventions, all pivot ties, all 408 active entries and the positive squared growth gap. Substantial ChatGPT/Codex assistance is disclosed; this is automated-agent review, not external human peer review or formal certification. [Authorship, reproducible certificates, source checks and public-branch audit](../../references/stepaniants-ie05-2026-09-11/README.md). The original ID, path, statement, historical ratings and earlier checks below are retained. Peca-Medlin retains credit for the conjecture and cited element-growth analysis.

## Context and notation

All elimination in this problem is in exact arithmetic. Write $\|A\|_{\max}=\max_{ij}|a_{ij}|$. A pivoting path creates successive active Schur complements $S_1=A,S_2,\ldots,S_n$, with row/column permutations as appropriate. Its element-growth factor is

$$
\rho(A)=\frac{\max_{1\leq j\leq n}\|S_j\|_{\max}}{\|A\|_{\max}}.
$$

Partial pivoting chooses a largest-magnitude entry in the active first column; complete pivoting chooses one anywhere in the active matrix. If ties occur, a universal statement includes every admissible tie choice; a supremum includes all admissible paths. These conventions remove implementation-dependent ambiguity. Matrices are nonsingular unless otherwise stated.

## Problem statement

Let $L_n$ be the real unit lower triangular matrix whose entries strictly below the diagonal are all $-1$. Define $Q_n$ by the unique QR factorization $L_n=Q_nR_n$ with positive diagonal in $R_n$. For $Q_n$, use partial pivoting with the first available row chosen in a tie. Is it true that, for every $n\geq2$,

$$
\sup_{Q\in O(n)}\rho_{\mathrm{PP}}(Q)
=\rho_{\mathrm{PP}}(Q_n),
\qquad O(n)=\{Q\in\mathbb R^{n\times n}:Q^TQ=I\}?
$$

The supremum on the left includes all admissible partial-pivoting paths. The candidate is fully specified by $L_n$, rather than by an approximate numerical optimizer. This asks for the sharp extremizer, beyond the established exponential order of orthogonal growth.

## Reference

Peca-Medlin, [*Growth factors of orthogonal matrices and local behavior of Gaussian elimination with partial and complete pivoting*](https://arxiv.org/html/2308.16146v2), published in SIAM J. Matrix Anal. Appl. (2024), §3.2 and Appendix B. The paper conjectures this equality and establishes $\rho_{\mathrm{PP}}(Q_n)=2^{n-1}(1+o(1))/\sqrt3$.

## Earlier status check — 2026-09-08

Searches for `GEPP orthogonal conjecture 2026` and the exact paper title found no proof of the extremal equality. The 2026 butterfly paper still identifies orthogonal partial-pivoting growth as open. The August Shah–Urschel results concern different growth questions and pivot strategies; their exponential examples do not establish this exact supremum.

## Audit update — 2026-09-10

Rechecked [Peca-Medlin's manuscript](https://arxiv.org/html/2308.16146v2), §3.2 and Appendix B, and its [SIAM publication](https://doi.org/10.1137/23M1597733), SIAM J. Matrix Anal. Appl. 45 (2024), 1599–1620. The candidate extremizers remain supported by the stated construction and experiments, without a general optimality proof. Searches for subsequent orthogonal GEPP extremizer results found no resolution.
