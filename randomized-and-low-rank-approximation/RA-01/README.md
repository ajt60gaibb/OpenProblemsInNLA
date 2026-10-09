# RA-01 — Optimal pivot count for RPCholesky trace approximation

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because a uniform near-optimal pivot count must exploit adaptive residual structure; community impact is efficient kernel and PSD matrix approximation.  
**Topic:** randomized low-rank approximation; kernel matrices  
**Last checked:** 2026-09-13  
**Status:** Partially resolved  

## Further partial result - 29 September 2026

[*Iterated-logarithmic pivot bounds for randomly pivoted Cholesky*](RA-01.pdf),
submitted manuscript, 29 September 2026.

Theorems 1.1 and 1.2 (pp. 3-4) give sufficient pivot counts for the original
coordinate, exact-arithmetic RPCholesky law on every finite complex Hermitian
positive-semidefinite input, without a spectral-decay or eigenvector assumption:

```math
\mathbb E\mathop{\mathrm{tr}}\nolimits(R_k)\le(1+\varepsilon)\tau_r(A),
\qquad
k=\min\{n,K_j(r,\varepsilon)\},\qquad j\in\{2,4\},
```

where, for absolute constants $`C_2,C_4`$ and $`0<\varepsilon\le1`$,

```math
K_2(r,\varepsilon)\le C_2r\bigl(\varepsilon^{-1}+\Lambda_2(r)\bigr),
\qquad
K_4(r,\varepsilon)\le C_4r\bigl(\varepsilon^{-1}+\Lambda_4(r)\bigr).
```

Here $`\Lambda_1(r)=\log(e+r)`$ and
$`\Lambda_{j+1}(r)=\log(e+\Lambda_j(r))`$ regularize the iterated logarithms
at small ranks. Explicit finite-rank counts appear in equations (18) and (44);
rank one has $`K_j(1,\varepsilon)=\lceil\varepsilon^{-1}\rceil`$, and zero
rank-$`r`$ tails terminate in at most $`r`$ positive pivots. Thus the reported
unrestricted counts are $`O(r/\varepsilon+r\log\log r)`$ and, more sharply,
$`O(r/\varepsilon+r\log\log\log\log r)`$ in large-rank notation.

Proposition 8.1 (pp. 19-21) also gives explicit robustness bounds for two-sided
multiplicative approximations to the pivot probabilities, with exact Schur
updates. **The unrestricted $`O(r/\varepsilon)`$ target remains open:** the
fourfold iterated-logarithmic rank term is still unbounded. The prior
tail-envelope result below addresses a different, restricted spectral scope.

The manuscript discloses assistance from OpenAI Codex/ChatGPT and Claude in
the mathematical development, exposition, experiments and proof review.
This submission records a manuscript result; it does not assert formal
verification or external human peer review.

## Partial resolution - 13 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute,
Simons Foundation. [Submission and verified affiliation](../../references/holden-ra01-2026-09-13/README.md).

[Theorems 4.1, 5.1 and 6.1](../../references/holden-ra01-2026-09-13/report.pdf)
prove the displayed pivot-count guarantee for the original exact-arithmetic
RPCholesky law under these additional tail assumptions. With
$`a=\lambda_{r+1}(A)>0`$, for every tail index $`1\le j\le n-r`$:

- $`\lambda_{r+j}(A)\le a2^{-(j-1)}`$ gives $`C=3`$.
- $`\lambda_{r+j}(A)\le a/j^2`$ gives $`C=4`$.
- $`\lambda_{r+j}(A)\le a/j^p`$ for a fixed $`p>1`$ gives an explicit finite $`C_p`$ depending only on $`p`$.

Leading eigenvalues and complex eigenvectors are unrestricted; zero tails and
the dimension cap are handled by exact termination. These are tail-normalized
hypotheses after rank $`r`$, not automatic consequences of global spectral decay.
**The unrestricted RA-01 target remains open:** no universal constant for all
PSD inputs, or counterexample to all such constants, is established.
Theorem 7.1 rules out an auxiliary continuous-time count bound with unit
tail-rate coefficient; Proposition 8.1 shows a limitation of the determinant
upper comparison. Neither is a counterexample to RA-01.

The stated partial results passed a separate
[independent Codex AI-agent informal mathematical audit](../../references/holden-ra01-2026-09-13/independent-review.md).
[Proof source](../../references/holden-ra01-2026-09-13/report.tex).
Exact finite checks and optional floating diagnostics passed; these do not
replace the general proof. AI assistance in review and submission preparation
is disclosed. No Lean verification, external human peer review or historical
novelty claim is asserted. The original statement and prior-source credit
are retained below.

## Context and notation

For a Hermitian positive-semidefinite $`A\in\mathbb C^{n\times n}`$, define
the exact-arithmetic RPCholesky residuals by $`R_0=A`$. Conditional on
$`R_t\ne0`$, select $`j`$ with probability $`(R_t)_{jj}/\mathop{\mathrm{tr}}\nolimits(R_t)`$
and set

```math
R_{t+1}=R_t-\frac{R_t(:,j)R_t(j,:)}{(R_t)_{jj}}.
```

If $`R_t=0`$, keep all subsequent residuals zero. Eigenvalues are ordered
$`\lambda_1(A)\geq\cdots\geq\lambda_n(A)\geq0`$, and
$`\tau_r(A)=\sum_{j>r}\lambda_j(A)`$. This is the pivot rule in Chen,
Epperly, Tropp, and Webber, [*Randomly pivoted Cholesky: Practical
approximation of a kernel matrix with few entry evaluations*](https://doi.org/10.1002/cpa.22234),
Algorithm 1; their Lemma 5.5 gives the current comparison
$`\mathbb E\mathop{\mathrm{tr}}\nolimits(R_r)\leq2^r\tau_r(A)`$.

## Problem statement

Does there exist a universal constant $`C\geq1`$ such that, for every
$`n\geq1`$, every Hermitian positive-semidefinite $`A\in\mathbb C^{n\times n}`$,
every integer $`1\leq r\leq n`$, and every $`0<\varepsilon<1`$, RPCholesky
satisfies

```math
\mathbb E\mathop{\mathrm{tr}}\nolimits(R_k)\leq(1+\varepsilon)\tau_r(A),
\qquad k=\min\{n,\lceil Cr/\varepsilon\rceil\}?
```

The expectation is over the algorithm's adaptive pivots. The constant must
be independent of dimension, spectrum, rank, and tolerance. The target
concerns this fixed pivoting rule.

## References

Epperly, [*A new analysis of the randomly pivoted Cholesky
algorithm*](https://arxiv.org/html/2608.20633v1), §1.2, conjecture immediately
after Eq. (1.5), and Corollary 1.3. Earlier motivation appears in
Epperly, [*Make the Most of What You Have*](https://tropp.caltech.edu/dissertations/Epp25-Making-Most.pdf),
Caltech dissertation (2025), §11.1, p. 181.

## Status check

The August 2026 paper proves the larger bound
$`k\geq r/\varepsilon+2r\sqrt{\log r}+r\log(1/\varepsilon)+2.3r`$
and explicitly conjectures the displayed improvement. Searches for the
paper's title, `RPCholesky optimal r epsilon`, and `RPCholesky conjecture`
found no subsequent resolution. The arXiv record listed only v1, posted
August 21, 2026. The weaker dissertation Conjecture 11.1 is therefore
excluded as resolved by this later preprint.

## Audit — 2026-09-10

Rechecked the [August 2026 conjecture after (1.5)](https://arxiv.org/html/2608.20633v1) and its current arXiv record, still v1. Optimal-pivot and RPCholesky follow-up searches found no resolution. The proved extra rank-dependent term does not establish the uniform $`O(r/\varepsilon)`$ target.
