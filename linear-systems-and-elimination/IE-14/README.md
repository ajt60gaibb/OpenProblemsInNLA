# IE-14 — Sharp growth for cyclic tridiagonal matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved
**Last checked:** 2026-09-11

<!-- colbrook-recovered -->
## Independently reviewed resolution - 2026-09-11

**Sharp growth classification.** Theorem 1 and Sections 2-4 prove $c_n=F_{n+1}+1$ for every $n\ge4$, with $F_0=0,F_1=1$. The bound covers complex cyclic tridiagonal matrices, every active entry and every permitted GEPP tie path in the original ordering. A rational matrix with both cyclic corners nonzero attains it at every order.

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. [Complete manuscript](../../references/colbrook-recovered-2026-09-11/manuscripts/IE-14.pdf), [independent proof review](../../references/colbrook-recovered-2026-09-11/verification/reviews/IE-14-review.md), and [submission record](../../references/colbrook-recovered-2026-09-11/README.md). The supplied notes were reconstructed with substantial AI assistance. This is independent agent verification, not external human peer review or formal proof-assistant certification; no novelty or priority claim is made.

The difficulty, importance and rating rationale below are historical assessments of the original open target. Original statements, references and dated audits are preserved.
<!-- /colbrook-recovered -->

**Rating rationale:** Challenging reflects an all-orders extremal problem in which the two corner entries change elimination fill; specialist impact is a precise stability bound for cyclic tridiagonal systems.

## Problem statement

For each $n\ge4$, let $\mathcal C_n$ consist of the nonsingular matrices $A\in\mathbb C^{n\times n}$ whose only permitted nonzero positions satisfy

$$|i-j|\le1\quad\text{or}\quad(i,j)\in\{(1,n),(n,1)\},$$

with $a_{1n}\ne0$ and $a_{n1}\ne0$. This is the cyclic tridiagonal pattern called *quasi-tridiagonal* in the source. No symmetry or diagonal dominance is assumed.

Apply Gaussian elimination with partial pivoting (GEPP) in exact arithmetic. At each stage select a largest-modulus entry in the active first column, interchange its row with the active first row, and form the trailing Schur complement. For an admissible path $\pi$, let $S_1=A,\ldots,S_n$ denote the active matrices. Define

$$
\rho(A,\pi)=\frac{\max_{1\le k\le n}\|S_k\|_{\max}}{\|A\|_{\max}},
\qquad \|M\|_{\max}=\max_{i,j}|m_{ij}|,
$$
$$c_n=\sup_{A\in\mathcal C_n}\ \sup_{\pi\text{ permitted by GEPP}}\rho(A,\pi).$$

Determine $c_n$ for every $n\ge4$, with matching upper bounds and examples approaching each supremum. All admissible tie choices are included. The given ordering is fixed before the stated GEPP run; preliminary row or column reorderings are not permitted. All sizes constitute one extremal problem.

Ordinary tridiagonal inputs have growth at most two. This question isolates the effect of the two corner entries on partial-pivoting stability. Unlike the fixed-bandwidth problem IE-13, the corner offsets grow with $n$.

## Reference

N. J. Higham, [*Accuracy and Stability of Numerical Algorithms*, second edition](https://doi.org/10.1137/1.9780898718027), SIAM (2002), Problem 9.15(b), p. 193; Theorem 9.11, p. 173, supplies the ordinary tridiagonal comparison.

## Earlier status check — 2026-09-08

The book's sparsity pattern was checked directly. Its wording omits the field; this entry adopts $\mathbb C$ from the adjacent Theorem 9.11. Searches for `quasi-tridiagonal growth factor`, `quasi-tridiagonal partial pivoting`, and `Gaussian elimination cyclic tridiagonal growth` found no solution of this exact extremal question. A [2017 cyclic-reduction paper](https://doi.org/10.1007/s10910-017-0761-9) uses a different matrix pattern and algorithm. Shah–Urschel's [August 31, 2026 revision](https://arxiv.org/html/2608.19189v4), Theorems 2.2–2.3, does not determine this extremum. No recent explicit reaffirmation of the question's openness was found; absence of a located resolution is the limit of this check.

## Audit update — 2026-09-10

Rechecked Higham's [Problem 9.15(b)](https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf), p. 193, against the two-corner pattern displayed here. Searches for cyclic/quasi-tridiagonal pivot growth and later elimination bounds found no exact solution. The [August 2026 general complete-pivoting results](https://arxiv.org/html/2608.19189v4) address a different pivot rule and do not provide this pattern's sharp partial-pivoting bound; current openness rests on the historical question and this limited search.
