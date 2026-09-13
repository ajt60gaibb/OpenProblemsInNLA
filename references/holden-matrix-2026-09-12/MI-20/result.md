# MI-20: dual and projective normal forms

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation.

**Date:** 12 September 2026. [Submission, verified affiliation and independent review](../README.md).

**Classification: USEFUL REDUCTION / LEMMA.** The exact sharp function C_p(m) is not determined. The dual formulation is known; the projective formulations below are included with proofs because they give an auditable search space and explain why rank-one-only searches are insufficient.

## Exact target

For every integer m>=2 and every real 1<p<2, determine

```math
C_p(m)=\sup_{n\ge1}\sup_{A_j\in\mathbb C^{n\times n},\ \sum_j|A_j|\ne0}
\frac{\|\sum_jA_j\|_p}{\|\sum_j|A_j|\|_p}.
\tag{1}
```

The supremum is taken jointly over all matrix orders. The following reductions preserve that supremum and the number of summands.

## 1. Positive dual formulation (known ingredient)

For q=p/(p-1),

```math
C_p(m)=\sup_{n,R,X_1,\ldots,X_m}
\frac{\sum_j\|RX_j\|_1}{\|R\|_q\|S\|_p},
\quad R\ge0,\quad X_j\ge0,\quad S=\sum_jX_j\ne0,\quad R\ne0.
\tag{2}
```

This equivalence appears in Qiu, Proposition 3.1, and is not claimed as new. For completeness, choose unitaries U_j with Re tr(U_j X_j R)=||X_j R||_1. The matrices A_j=U_jX_j satisfy |A_j|=X_j; Schatten duality bounds the resulting sum of traces by ||R||_q ||sum A_j||_p. This proves the dual supremum is at most (1). Conversely, write A_j=U_jX_j and a dual matrix Z=VR, extending the polar isometries to unitaries. Then

```math
|\mathop{\mathrm{tr}}\nolimits(Z^*\sum_j A_j)|
\le\sum_j\|X_jR\|_1.
```

Taking the supremum over ||Z||_q=1 proves the reverse inequality. Only finite-dimensional Schatten duality and the trace-norm variational identity are used.

## 2. Fixed-dimension binary projection reduction

For m=2, fixed S>=0 and fixed R>=0, the maximum over X,Y>=0 with X+Y=S of

```math
\|RX\|_1+\|RY\|_1
```

is attained at

```math
X=S^{1/2}PS^{1/2},\qquad Y=S^{1/2}(I-P)S^{1/2}
\tag{3}
```

for some orthogonal projection P. Here singular S is allowed.

**Proof.** On the support of S write X=S^(1/2) K S^(1/2), with 0<=K<=I; extend K arbitrarily as a contraction on ker S. The objective is a convex function of K, being a sum of norms of affine functions. Decompose K as a convex combination of nested spectral projections and the zero projection, exactly as in the proof in `../MI-27/result.md`. Convexity shows its objective is no larger than the largest objective of one of those projections. The denominator in (2) is fixed in this argument. Conversely every P in (3) is feasible. This proves the statement.

No rank-one conclusion follows: in dimension n a maximizing P can have any rank from 0 to n. In particular the complementary modulus may have rank greater than one.

## 3. All-m projective dilation, preserving the dimension-free supremum

In (2), without changing the supremum, restrict to tuples of the form

```math
X_j=S^{1/2}P_jS^{1/2},\qquad
P_jP_k=0\ (j\ne k),\qquad \sum_jP_j=I.
\tag{4}
```

The matrix dimension is still allowed to vary. For a given n-dimensional tuple the construction below uses dimension mn; it does not assert a dimension-preserving reduction for m>2.

**Proof.** For any feasible tuple let E be the support projection of S. On E put K_j=S^(-1/2)X_jS^(-1/2), using the inverse restricted to E. Extend by setting K_1=I on E-perp and K_j=0 there for j>1. Then K_j>=0, sum K_j=I_n, and X_j=S^(1/2)K_jS^(1/2).

Define an isometry W from C^n to the direct sum of m copies of C^n by

```math
Wv=(K_1^{1/2}v,\ldots,K_m^{1/2}v).
```

Let P_j be the coordinate projections of that direct sum and put

```math
\widetilde S=WSW^*,\qquad\widetilde R=WRW^*.
```

Since W*W=I, we have W*P_jW=K_j and \widetilde S^(1/2)=W S^(1/2) W*. Thus

```math
\widetilde S^{1/2}P_j\widetilde S^{1/2}=WX_jW^*.
```

Isometric embedding adds only zero singular values. Therefore

```math
\|\widetilde R\|_q=\|R\|_q,\quad
\|\widetilde S\|_p=\|S\|_p,\quad
\|\widetilde R\,\widetilde S^{1/2}P_j\widetilde S^{1/2}\|_1=\|RX_j\|_1.
```

Every ratio in (2) is reproduced by a tuple (4). The reverse inclusion is immediate because every tuple (4) is feasible in (2). This proves equality of the dimension-free suprema, including singular S and R.

## 4. Basic consistency relations

Padding by zero summands gives C_p(m+1)>=C_p(m). Tensor products give

```math
C_p(mk)\ge C_p(m)C_p(k).
\tag{5}
```

Indeed use all mk matrices A_i tensor B_j. Their sum and the sum of their moduli are the corresponding tensor products; Schatten p-norms multiply. Taking independently approximating sequences for the two suprema proves (5). These observations do not determine the sharp constants.

## Experiments and unresolved obstruction

`search.py` parametrizes X_j=L_j L_j^T and diagonal positive R, optimizing the dual quotient in real dimensions 2,3,4,6 at p=6/5, m=2. All seeds, factors, weights and objective values from this checkpoint are saved in `experiments/`. They are numerical evidence only. These searches did not recover a higher-dimensional improvement over the best dimension-two value; local failure does not give an upper bound.

The prior handoff's claim of improved dimension-four/six ratios had no retained matrices, p, seeds, or objective values. It is not promoted into a result here. No statement is made that the present searches reproduce that claim.

The unresolved step is a sharp, dimension-independent upper bound for (2) or (4), together with matching examples for every p,m. Restricting the optimizing ranks, fixing a maximal dimension, or transplanting the p>=2 formula would not solve the stated target.

## Sources

Canonical target: https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-20/README.md

README blob observed: `1a563704ee014e136f630bfb9732d268ffbac53d`.

H. Qiu, *Sharp Quasi-Reverse Minkowski Inequality for Schatten Norms*, arXiv:2608.17565v2, Proposition 3.1 and Section 5: https://arxiv.org/html/2608.17565

X. Li, *Sharp Concave-Function Transfer for Lee-Type Schatten Norm Inequalities*, arXiv:2608.25989v1, remaining constant problem: https://arxiv.org/html/2608.25989
