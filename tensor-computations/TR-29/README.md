# TR-29 — Exact partially symmetric rank of products of generalized W tensors

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-11-02

**Rating rationale:** Matching constructive upper bounds by sharp lower bounds for arbitrary products requires substantial new decomposition arguments. The exact partially symmetric rank of this particular family chiefly interests specialists in tensor rank and multipartite entanglement. These ratings are historical and refer to the original question, which is resolved below.

## Resolution — 2 November 2026

**Resolved affirmatively.** Wenqi Zhu (University of Oxford) and Ping Nie
(University of Waterloo).

For every $`k\ge2`$ and all $`d_1,\ldots,d_k\ge3`$,

```math
R(W_{d_1}\otimes\cdots\otimes W_{d_k})=2^{k-1}(d_1+\cdots+d_k-2k+2).
```

In particular $`R(W_3\otimes W_3\otimes W_3)=20`$. This is Theorem 1.1,
stated on p. 2 of the 16-page paper
[*The Exact Partially Symmetric Rank of Products of W-States*](https://github.com/erenup/w-tensor-product-rank/blob/b60a62dd7fc4595fa82dafdd56649e462440b38f/paper/main.pdf)
at the immutable
[revision `b60a62d`](https://github.com/erenup/w-tensor-product-rank/tree/b60a62dd7fc4595fa82dafdd56649e462440b38f),
made public on 2 November 2026. The paper proves the lower bound for every
decomposition in Sections 2–7, completing it at the end of Section 7 (p. 7).
The matching upper bound is Theorem 1.1 of Canino, Casarotti and Santarsiero
(reference 3 below).

**Comparison with the target.** The paper works over $`\mathbb C`$ with the
polynomial $`\prod_{i=1}^k x_i^{d_i-1}y_i`$. Its partially symmetric rank is
the least $`r`$ with

```math
\prod_{i=1}^k x_i^{d_i-1}y_i=\sum_{\ell=1}^{r}c_\ell\prod_{i=1}^k(a_{i\ell}x_i+b_{i\ell}y_i)^{d_i},
\qquad c_\ell,a_{i\ell},b_{i\ell}\in\mathbb C,
```

with the blocks $`(x_i,y_i)`$ and the degrees $`d_i`$ fixed. The standard
isomorphism of
$`\mathop{\mathrm{Sym}}\nolimits^{d_1}(\mathbb C^2)\otimes\cdots\otimes\mathop{\mathrm{Sym}}\nolimits^{d_k}(\mathbb C^2)`$
with multihomogeneous polynomials of multidegree $`(d_1,\ldots,d_k)`$ sends
$`T_{\mathbf d}`$ to $`d_1\cdots d_k\prod_i x_i^{d_i-1}y_i`$. It sends each term
$`(v_{1,\ell})^{\otimes d_1}\otimes\cdots\otimes(v_{k,\ell})^{\otimes d_k}`$,
with $`v_{i,\ell}=(a_{i\ell},b_{i\ell})`$, to
$`\prod_i(a_{i\ell}x_i+b_{i\ell}y_i)^{d_i}`$. Over $`\mathbb C`$ the nonzero
scalars $`d_1\cdots d_k`$ and $`c_\ell`$ are absorbed into the vectors
$`v_{1,\ell}`$, so the paper's rank equals the minimum $`s`$ in the problem
statement below. Theorem 1.1 assumes exactly $`k\ge2`$ and $`d_i\ge3`$, as the
target does, and so covers its full range. It concerns the rank with the blocks
fixed, not the border rank or the rank after grouping modes from different
blocks. For $`k=2`$ it overlaps, and agrees with, the two-factor partial
resolution below.

**Extension.** Theorem 8.1 (p. 8) determines the exact rank of every product
of binary monomials $`\prod_i x_i^{a_i}y_i^{b_i}`$ with $`a_i\ge b_i\ge1`$,
with an explicit matching decomposition; with every $`b_i=1`$ it gives the
displayed formula for all $`k\ge1`$ and $`d_i\ge2`$ (Remark 8.1, p. 13).

**Proof and verification scope.** Both rank formulas are proved in the
written paper. A Lean formalization at the same revision proves only an
algebraic core of seven universal targets, recorded in its
[formal scope](https://github.com/erenup/w-tensor-product-rank/blob/b60a62dd7fc4595fa82dafdd56649e462440b38f/lean/SCOPE.md): the one-coordinate moment lower bound, a
geometric-series inverse, the formal Laurent leading term with a nonzero
series determinant, the anti-diagonal block determinant, the bilinear Gram
assembly, the Gram count under explicit hypotheses, and finite parameter
avoidance. The reduction of an arbitrary decomposition to moment conditions,
the test functions and their cross-block cancellations, the identification of
each block with its formal expansion, the multivariate moment theorem and both
rank formulas are proved in the text only. No Lean theorem states a rank
formula, so this is not a Lean verification of the target. The
[verification record](https://github.com/erenup/w-tensor-product-rank/blob/b60a62dd7fc4595fa82dafdd56649e462440b38f/VERIFICATION.md) also describes exact checks of
finite instances.

**Review.** Solved by several independent informal AI-agent audits of the
complete written proof, all accepting it with minor corrections, which are
incorporated in the paper. The complete argument was also checked by coauthor
Wenqi Zhu (University of Oxford). Haibin Chen (Qufu Normal University), a
specialist in tensor decompositions who was not involved in the work, reviewed
the proof and found it correct. The [review record](https://github.com/erenup/w-tensor-product-rank/blob/b60a62dd7fc4595fa82dafdd56649e462440b38f/verification/reviews/README.md) contains the audit reports. The paper discloses its use of AI tools. The catalogue did not rerun the Lean or exact checks.

The retained partial-result and literature records below predate this
resolution.

## Partial resolution — the two-factor case k = 2, 13 September 2026

**Author:** Maximilian Behr. [Submission record](../../references/behr-tr29-2026-09-13/README.md).

[Theorem 1.1, proved in Sections 3–4](../../references/behr-tr29-2026-09-13/manuscript/TR29_two_factor_rank.pdf) settles every tuple with $`k=2`$:

```math
R(W_{d_1}\otimes W_{d_2})=2(d_1+d_2-2)\qquad\text{for all }d_1,d_2\ge2 .
```

The lower bound combines a peeling lemma — a point set supporting $`x^py\otimes u^qv`$ lies on no curve of bidegree $`(1,q)`$ or $`(p,1)`$, so its Hilbert function is maximal there — with the catalecticant–Sylvester inequality of Wang–Seigal applied to this unbalanced pair of bidegrees, where the catalecticant has rank four. The matching upper bound is Gałązka's decomposition (also Canino–Casarotti–Santarsiero, Theorem 1.1). Previously equality was known for $`d_1=2`$ or $`d_2=2`$, for $`(3,3)`$, and for $`(4,4)`$ in an unpublished 2021 note of Gałązka. Corollary 5.4 of the same manuscript also determines $`R(x^ay^b\otimes u^cv^d)=(a+1)(c+1)-(a-b)(c-d)`$ for all $`a\ge b\ge1`$, $`c\ge d\ge1`$.

**The case $`k\ge3`$ remains open** (for example $`R(W_3\otimes W_3\otimes W_3)`$, with upper bound 20), so the entry stays Partially resolved.

The argument passed two separate [independent AI-agent informal audits](../../references/behr-tr29-2026-09-13/verification/independent-review.md), with exact rational checks and exhaustive finite-field black-box searches that were rerun. AI assistance is disclosed; no external human peer review or formal verification is claimed. No Lean verification was performed.

## Problem statement

For an integer $`d\geq3`$, put

```math
W_d=\sum_{j=1}^{d}
e_1^{\otimes(j-1)}\otimes e_2\otimes
e_1^{\otimes(d-j)}\in\mathop{\mathrm{Sym}}\nolimits^d(\mathbb C^2).
```

Given any $`k\geq2`$ and $`d_1,\ldots,d_k\geq3`$, set
$`T_{\mathbf d}=W_{d_1}\otimes\cdots\otimes W_{d_k}`$.
Determine the exact smallest integer $`s`$ such that

```math
T_{\mathbf d}=\sum_{\ell=1}^{s}
(v_{1,\ell})^{\otimes d_1}\otimes\cdots\otimes
(v_{k,\ell})^{\otimes d_k},
\qquad v_{j,\ell}\in\mathbb C^2.
```

This minimum is the partially symmetric rank with the $`k`$ blocks of orders $`d_1,\ldots,d_k`$ fixed. It is not the border rank and not the rank obtained after grouping modes from different blocks. The harmless nonzero scalar relating the displayed $`W_d`$ to the polynomial $`x^{d-1}y`$ can be absorbed into a decomposition.

## Why it matters

These explicit tensors are benchmarks for the difference between exact, border, and symmetry-constrained tensor decompositions. They already demonstrate that decomposing two copies together can cost fewer terms than multiplying their individual ranks. Determining their exact ranks would quantify that saving beyond small examples.

## References and status check

1. A. Oneto and E. Ventura, *Ranks of tensors: geometry and applications*, [2025 survey](https://doi.org/10.1007/s40574-025-00472-9), Question 12, following Theorems 4.4–4.5.
2. E. Ballico, A. Bernardi, M. Christandl, and F. Gesmundo, *On the partially symmetric rank of tensor products of W-states and other symmetric tensors*, [arXiv:1803.01623](https://arxiv.org/abs/1803.01623), §§3–4; Rendiconti Lincei **30** (2019), 93–124.
3. S. Canino, A. Casarotti, and P. Santarsiero, *A new bound on the rank of tensor product of W-states*, [arXiv:2512.05828v1](https://arxiv.org/html/2512.05828v1), Theorem 1.1 and its following discussion.

### Status check — 2026-09-10

Checked the 2025 source question and Canino–Casarotti–Santarsiero v1, Theorem 1.1 and the ensuing sharpness discussion, with targeted W-product-rank searches through 2026. The December 2025 paper gives the upper bound $`2^{k-1}(d_1+\cdots+d_k-2k+2)`$ and explicit decompositions. Equality is known for $`k=2,d_1=d_2=3`$, where the rank is eight, so a nontrivial parameter case is resolved. The construction alone does not prove minimality for other tuples. No general exact formula was located.
