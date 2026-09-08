# Iterative methods, eigenvalue computation, and elimination

> Legacy source map and screening notes. Admitted statements have moved to category/problem folders. Follow the links below or [browse the new index](../../CATALOG.md). Shared notation and uncounted material are retained here as the historical source record.

Status checks below were performed on **2026-09-08**. “No resolution found” means that the cited later papers and the recorded searches did not identify one; it is not a proof that no unpublished solution exists. Difficulty and importance are editorial judgments. Entries are individual mathematical questions, not dimension-by-dimension expansions of a general question.

## Conventions for elimination problems

All elimination in these statements is in exact arithmetic. Write $\|A\|_{\max}=\max_{ij}|a_{ij}|$. A pivoting path creates successive active Schur complements $S_1=A,S_2,\ldots,S_n$, with row/column permutations as appropriate. Its element-growth factor is

$$
\rho(A)=\frac{\max_{1\leq j\leq n}\|S_j\|_{\max}}{\|A\|_{\max}}.
$$

Partial pivoting chooses a largest-magnitude entry in the active first column; complete pivoting chooses one anywhere in the active matrix. If ties occur, a universal statement includes every admissible tie choice; a supremum includes all admissible paths. These conventions remove implementation-dependent ambiguity. Matrices are nonsingular unless otherwise stated.

<a id="ie-01"></a>

## Removed IE-01 — Forsythe's conjecture beyond restart length two

**Status: resolved; removed from the open count on 2026-09-08.**

Colbrook, Stepaniants, and Townsend,
[*A Complete Resolution of Forsythe's Conjecture for Restarted Conjugate Gradients*](https://arxiv.org/abs/2609.04659),
September 4, 2026, [Theorem 1.1](https://arxiv.org/html/2609.04659v1),
proves convergence for restart length $s=3$ and supplies counterexamples for
every $s\ge4$. This settles the full range formerly admitted as IE-01.
The earlier screen missed this paper. The ID remains reserved, and the old
statement and exports are preserved in Git history.


<a id="ie-02"></a>

## IE-02 — Is the ideal GMRES bound sharp for every Jordan block?

[Open the problem folder](../../linear-systems-and-elimination/IE-02/README.md) · [PDF](../../linear-systems-and-elimination/IE-02/problem.pdf) · [LaTeX](../../linear-systems-and-elimination/IE-02/problem.tex)


<a id="ie-03"></a>

## IE-03 — Cryer's Hadamard complete-pivoting conjecture

[Open the problem folder](../../linear-systems-and-elimination/IE-03/README.md) · [PDF](../../linear-systems-and-elimination/IE-03/problem.pdf) · [LaTeX](../../linear-systems-and-elimination/IE-03/problem.tex)


<a id="ie-04"></a>

## IE-04 — Exponential smoothed tail bounds for partial pivoting

[Open the problem folder](../../linear-systems-and-elimination/IE-04/README.md) · [PDF](../../linear-systems-and-elimination/IE-04/problem.pdf) · [LaTeX](../../linear-systems-and-elimination/IE-04/problem.tex)


<a id="ie-05"></a>

## IE-05 — Exact extremizers for partial pivoting on orthogonal matrices

[Open the problem folder](../../linear-systems-and-elimination/IE-05/README.md) · [PDF](../../linear-systems-and-elimination/IE-05/problem.pdf) · [LaTeX](../../linear-systems-and-elimination/IE-05/problem.tex)


<a id="ie-06"></a>

## IE-06 — The square-root upper bound for Gaussian partial-pivoting growth

[Open the problem folder](../../linear-systems-and-elimination/IE-06/README.md) · [PDF](../../linear-systems-and-elimination/IE-06/problem.pdf) · [LaTeX](../../linear-systems-and-elimination/IE-06/problem.tex)


<a id="ie-07"></a>

## IE-07 — Deterministic regularization of the nonsymmetric eigenproblem

[Open the problem folder](../../eigenvalues-and-inverse-problems/IE-07/README.md) · [PDF](../../eigenvalues-and-inverse-problems/IE-07/problem.pdf) · [LaTeX](../../eigenvalues-and-inverse-problems/IE-07/problem.tex)


<a id="ie-08"></a>

## IE-08 — A cubic-time Schur algorithm using logarithmic precision

[Open the problem folder](../../eigenvalues-and-inverse-problems/IE-08/README.md) · [PDF](../../eigenvalues-and-inverse-problems/IE-08/problem.pdf) · [LaTeX](../../eigenvalues-and-inverse-problems/IE-08/problem.tex)


<a id="ie-10"></a>

## IE-10 — Conditioning of a random Krylov compression of a cyclic shift

[Open the problem folder](../../eigenvalues-and-inverse-problems/IE-10/README.md) · [PDF](../../eigenvalues-and-inverse-problems/IE-10/problem.pdf) · [LaTeX](../../eigenvalues-and-inverse-problems/IE-10/problem.tex)


<a id="ie-11"></a>

## IE-11 — The exact fifth complete-pivoting growth factor

[Open the problem folder](../../linear-systems-and-elimination/IE-11/README.md) · [PDF](../../linear-systems-and-elimination/IE-11/problem.pdf) · [LaTeX](../../linear-systems-and-elimination/IE-11/problem.tex)


<a id="ie-12"></a>

## IE-12 — Near-quadratic solution cost at a prescribed backward error

[Open the problem folder](../../linear-systems-and-elimination/IE-12/README.md) · [PDF](../../linear-systems-and-elimination/IE-12/problem.pdf) · [LaTeX](../../linear-systems-and-elimination/IE-12/problem.tex)


## Uncounted candidate IE-09 — Stable selected bidiagonal singular vectors

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** withheld; ID reserved. A source-faithful, nonvacuous precision/cost model needs further work. The provisional formulation below is not an admitted open problem.

Let $B\in\mathbb R^{n\times n}$ be upper bidiagonal, let $1\leq\ell\leq r\leq n$, and put $k=r-\ell+1$. At a fixed working precision with unit roundoff $u$, construct a floating-point algorithm using $O(nk)$ operations that returns the selected singular values and associated approximately normalized vectors $(\widehat\sigma_i,u_i,v_i)$, $\ell\leq i\leq r$, with

$$
|\widehat\sigma_i-\sigma_i(B)|\leq Cnu\|B\|_2,
\quad
\max\{\|Bv_i-\widehat\sigma_i u_i\|_2,
\|B^Tu_i-\widehat\sigma_i v_i\|_2\}\leq Cnu\|B\|_2,
$$
$$
\max\{|u_i^Tu_j|,|v_i^Tv_j|\}\leq Cnu\quad(i\ne j),
$$

for a universal $C$, all $nu$ sufficiently small, and all inputs including clustered and zero singular values. The intended cost must have a specified uniform dependence on precision; allowing an arbitrary constant depending on fixed $u$ makes the complexity target vacuous when $nu$ is restricted. Vector normalization should likewise mean $|\|u_i\|_2^2-1|,|\|v_i\|_2^2-1|\leq Cnu$, rather than exact normalization of floating-point outputs. Singular values are indexed in descending order, and overflow and underflow are excluded.

**References:** Großer and Lang, [*The bidiagonal MRRR algorithm*](https://www.netlib.org/lapack/lawnspdf/lawn166.pdf), §4. Marques, Demmel, and Vasconcelos, [*Bidiagonal SVD Computation via an Associated Tridiagonal Eigenproblem*](https://icl.utk.edu/files/publications/2018/icl-utk-1040-2018.pdf), introduction and discussion of clusters. Amsel et al., [2026 survey](https://arxiv.org/html/2602.05394v3#S3.SS4), Problem 3.8.

**Status check:** Searches for `bidiagonal MRRR 2026 algorithm` found proposed methods but no unconditional theorem satisfying the stated bounds. **Formulation note:** the survey prints only one residual equation. Both are needed for the intended selected-SVD task; one-sided residuals alone do not define approximate singular triples.

**Admission obstacle:** An unrestricted constant depending on $u$ together with $nu\leq c$ bounds $n$ and permits even cubic work to be described as $O(nk)$. Uniform $O(nk)$ or an explicit $\operatorname{polylog}(1/u)$ allowance requires checking the source’s intended computational model. Until then, the original numerical challenge is preserved without claiming a precise admitted theorem target.

## Removed or withheld questions — not included in the count

- **Polynomial worst-case complete/rook pivoting growth:** excluded. Shah and Urschel, [*Entry growth in Gaussian elimination*](https://arxiv.org/abs/2608.19189), August 2026, Theorems 1.6–1.7, give quasipolynomial lower bounds. This is a recent preprint resolution claim, not an independently certified proof by this catalog.
- **Forsythe conjecture, all restart lengths:** the September 2026 [complete resolution](https://arxiv.org/abs/2609.04659) supersedes the earlier restart-two-only exclusion. Former [IE-01](#ie-01) is also removed.
- **Power-law-spectrum CG versus randomized coordinate descent, Simons Problem 2.4:** withheld following Chen et al., [*Iteris: Agentic Research Loops for Computational Mathematics*](https://arxiv.org/html/2606.02484v1#S4.SS2), June 2026, Theorem 1 and Appendix 6. It claims a fixed-parameter phase diagram; its rate bounds are expressly not sharp. Counting the original question without checking this claim would be misleading.
- **Higham's complex symmetric positive-definite growth bound:** excluded. Zhang, [*Sharp condition-number bounds for growth factors of Higham matrices in Gaussian elimination*](https://arxiv.org/abs/2604.23024), April 2026, identifies Drury's 2013 bound and develops a strict, quantitative refinement.
- **Broad GMRES convergence explanations, unspecified block-Lanczos rounding analyses, and unspecified MRRR input conditions:** retained only as source leads, not admitted as precise problems. The relevant source is [Amsel et al., §§2.5–2.6 and §3.4](https://arxiv.org/html/2602.05394v3). Additional work is needed to turn each into a quantifiable target without inventing a new problem or restating a known theorem.
