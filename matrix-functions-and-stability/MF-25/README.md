# MF-25 — Maximum degree of real polynomials with a multiplication budget

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Real coefficient-space density and sharp degree exclusions must both be established for arbitrary budgets. The result would give a benchmark for designing low-cost matrix-function approximations.  
**Status:** Open  
**Last checked:** 2026-11-27  

## Problem statement


For a nonnegative integer $`r`$, let $`\Pi_r`$ be the set of real polynomials
of degree exactly $`r`$. For a nonnegative integer $`m`$, let
$`\Pi_{2^m}^*`$ be the real polynomials computable from $`1,x`$ by a
straight-line program with at most $`m`$ nonscalar multiplications.
Each multiplication forms the product of two previously available
polynomials, while arbitrary real linear combinations are free.
This is the same arithmetic model as in [MF-01](../MF-01/README.md)
and [MF-14](../MF-14/README.md), except that MF-14 uses complex
coefficients and fixes the multiplication budget to seven.
Substituting a square matrix $`X`$ for $`x`$ gives an evaluation
scheme valid for matrices of arbitrary size.

Identify each polynomial of degree at most $`r`$ with its monomial
coefficient vector in $`\mathbb R^{r+1}`$. The bar denotes Euclidean closure
in this coefficient space. Define

```math
d(m)=\max\left\{
r\in\mathbb N:\Pi_r\subseteq
\overline{\Pi_{2^m}^*\cap\Pi_r}
\right\}.
```

The inclusion at degree $`r`$ means that for every $`p\in\Pi_r`$ and every
$`\varepsilon>0`$ there exists a $`q\in\Pi_{2^m}^*\cap\Pi_r`$ whose
coefficient vector is within Euclidean distance $`\varepsilon`$ of that
of $`p`$. Thus every real polynomial of degree $`d(m)`$ can be
approximated arbitrarily closely in its coefficients by polynomials of
the same degree that admit evaluation with at most $`m`$ nonscalar
multiplications.

The classical Paterson--Stockmeyer algorithm provides a constructive
lower bound, while the dimension formula
$`\dim(\Pi_{2^m}^*)=m^2`$ for $`m>2`$
(Jarlebring and Lorentzon, Theorem 4.2) provides an upper bound.
Together, these give

```math
\left\lfloor\frac{(m+2)^2}{4}\right\rfloor
\leq d(m)\leq m^2-1,\qquad m>2.
```

The lower bound follows from exact polynomial evaluation using the
Paterson--Stockmeyer scheme; the upper bound follows since the space
of polynomials of degree exactly $`r`$ has dimension $`r+1`$. The general problem is to determine $`d(m)`$, 
and we propose the following.

**Conjecture.** For every integer $`m\geq4`$,

```math
\boxed{d(m)=m^2-m.}
```


## Why it matters

Matrix products typically dominate the cost of evaluating a polynomial
of a large dense matrix. The conjecture would identify the greatest
degree at which any real polynomial approximant, for example one used
to approximate the matrix exponential, can be perturbed arbitrarily
little in its coefficients and evaluated within a prescribed product
budget. 

## Related problems

[MF-01](../MF-01/README.md) studies optimal approximation of the sign
function under a fixed multiplication budget. In contrast, the present
problem concerns the maximum polynomial degree achievable with a given
number of multiplications.

[MF-14](../MF-14/README.md) concerns polynomial evaluation with seven
matrix multiplications. Webb (2026) established that the maximum degree
in the complex, full-space Zariski-closure model is 47. Since real
Euclidean density within a fixed-degree polynomial space implies
complex Zariski density in the full coefficient space, this result
provides the upper bound

```math
d(7)\leq47.
```

This improves the general dimension bound $`d(7)\leq48`$, but does not
establish the conjectured equality $`d(7)=42`$. The sense of approximability the current conjecture 
leads to is different from that of [MF-14](../MF-14/README.md), since higher order coefficients are here enforced to zero; which 
is may improve practical usefulness.

See also [Webb's degree-47 proof](../../references/webb-mf14-degree47-2026-09-17/proof.pdf).

## References and status evidence

E. Jarlebring and G. Lorentzon, *The Polynomial Set Associated with a Fixed
Number of Matrix-Matrix Multiplications*, SIAM Journal on Applied Algebra
and Geometry 10(3), 549–581 (2026).
[DOI: 10.1137/25M1779036](https://doi.org/10.1137/25M1779036).

M. S. Paterson and L. J. Stockmeyer, *On the Number of Nonscalar
Multiplications Necessary to Evaluate Polynomials*, SIAM Journal on
Computing 2(1), 60–66 (1973).
[DOI: 10.1137/0202007](https://doi.org/10.1137/0202007).

**Rigorous results.** Theorem 4.2 of Jarlebring and Lorentzon proves
the dimension formula $`\dim(\Pi_{2^m}^*)=m^2`$ for $`m>2`$.
Section 5.1 gives an exact four-product construction with real
coefficients for every real polynomial of degree 12 and identifies
12 as the optimal degree for coverage. In particular, the exact
construction gives the density inclusion at degree 12 in the
formulation above.

**Numerical and empirical evidence.** The following results support the conjecture:

- **$`d(5)=20`$:** Real evaluation schemes for several degree-20 polynomials were obtained using homotopy continuation, together with a combinatorial analysis of zero patterns in the evaluation schemes (Jarlebring and Lorentzon, §5, Conjecture 5.1). These findings are consistent with the earlier work of Sastre et al. (2025, §4), who developed a five-multiplication evaluation scheme for degree-20 polynomials, where realness of coefficients were not studied.
- **$`d(6)=30`$:** A real evaluation scheme for a degree-30 polynomial was obtained using an iteratively regularized Newton method, together with a combinatorial analysis of zero patterns in the evaluation schemes (Jarlebring and Lorentzon, §5, Conjecture 5.2).

These results provide numerical support for the conjectured degrees but do not establish Euclidean density or optimality. The numerical experiments and evaluation schemes are available in the [accompanying software repository](https://github.com/GustafLorentzon/polynomial-set-paper).



**Relation to the published conjectures.** The conjecture above
generalizes the small-budget observations in Jarlebring and Lorentzon,
which states separate conjectures for five, six, and seven products.
It also uses a different notion of closure: Section 2.2 specifies
Zariski closure, and (5.1) takes the closure of the full output set
before testing coverage at a given degree. Here the approximating
outputs must have exactly the target degree and converge in real
Euclidean coefficient space.

## Audit — 2026-11-27

Checked the published SIAGA article's model and closure convention,
Theorem 4.2, the constructions and conjectures in §5, and the concluding
discussion. Also checked the local MF-14 resolution, §4 of Sastre et al.'s
degree-20 construction, and §6 of Alonso et al.'s preprint on stable
evaluation. A targeted search by the SIAGA title and by the five-,
six-, and seven-product degree claims located related constructions and
the complex MF-14 result.

This bounded check located no proof or counterexample for the stated
all-budget real, same-degree Euclidean conjecture.

[Sastre et al., §4](https://wseas.com/journals/mathematics/2025/b385106-036%282025%29.pdf) ·
[Alonso et al., §6](https://arxiv.org/html/2603.23143#S6).
