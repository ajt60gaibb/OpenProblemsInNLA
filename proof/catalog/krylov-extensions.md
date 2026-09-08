# Sparse solvers and eigenvalue algorithms

> Legacy source map and screening notes. Admitted statements have moved to category/problem folders. Follow the links below or [browse the new index](../../CATALOG.md). Shared notation and uncounted material are retained here as the historical source record.

The status checks in this chapter were performed on **2026-09-08**, including
the August 21 version of the Simons workshop report. No resolution found means
that the bounded searches described below found none. Ratings are editorial.
All norms are Euclidean vector norms or their induced matrix norms.

<a id="ke-01"></a>

## KE-01 — Exploit spectral outliers without losing input sparsity

[Open the problem folder](../../linear-systems-and-elimination/KE-01/README.md) · [PDF](../../linear-systems-and-elimination/KE-01/problem.pdf) · [LaTeX](../../linear-systems-and-elimination/KE-01/problem.tex)


<a id="ke-02"></a>

## KE-02 — Construct a separating diagonal perturbation in nearly linear time

[Open the problem folder](../../eigenvalues-and-inverse-problems/KE-02/README.md) · [PDF](../../eigenvalues-and-inverse-problems/KE-02/problem.pdf) · [LaTeX](../../eigenvalues-and-inverse-problems/KE-02/problem.tex)


<a id="ke-03"></a>

## KE-03 — Find a near-largest nonnormal eigenvalue using few matrix-vector products

[Open the problem folder](../../eigenvalues-and-inverse-problems/KE-03/README.md) · [PDF](../../eigenvalues-and-inverse-problems/KE-03/problem.pdf) · [LaTeX](../../eigenvalues-and-inverse-problems/KE-03/problem.tex)


## Additional leads — uncounted

- **Algebraic multigrid, workshop Problem 2.3:** the target approximate inverse
  is precise, but the report does not specify which multigrid hierarchy,
  smoother, or construction algorithm is to satisfy it. Replacing the method
  requirement by an unrestricted approximate-inverse algorithm risks changing
  the question; no entry is admitted from that replacement.
- **Finite-precision CG, workshop Problems 2.15–2.19:** the n-step precision
  question is promising, but a sharp formulation needs fixed recurrences,
  rounding and breakdown conventions, and input conditioning assumptions.
  The broad comparison and block-analysis requests are not additional entries.
- **SVD without condition-number dependence:** Sobczyk's §5, question 2,
  explicitly asks to remove the dependence in Theorem 1.2. That theorem gives
  both an exact factorization with approximate isometries and a weaker
  backward-approximation consequence. The intended retained accuracy guarantee
  needs clarification before this is admitted as a general algorithm-existence
  question. Searches for `Sobczyk SVD condition number` and `deterministic SVD
  condition 2026 complexity` found no later general resolution.
