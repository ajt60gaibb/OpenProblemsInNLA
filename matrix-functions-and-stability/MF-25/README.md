# MF-25 — Maximum degree of real polynomials with a multiplication budget

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Real coefficient-space density and sharp degree exclusions must both be established for arbitrary budgets. The result would give a benchmark for designing low-cost matrix-function approximations.  
**Status:** Partially resolved  
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

For positive integers $`a,b`$ with $`a+b=m+2`$, the Paterson--Stockmeyer
scheme evaluates any polynomial of degree $`ab`$ using $`a-1`$ products
to compute powers through $`x^a`$ and $`b-1`$ products in Horner evaluation
in $`x^a`$. The leading block is scalar. Taking balanced $`a,b`$ gives
the lower bound. For the upper bound, the degree-$`r`$ coefficient space
has dimension $`r+1`$ and its nonzero-leading-coefficient locus is Zariski
dense in it. The general problem is to determine $`d(m)`$.


**Conjecture 1.** For every integer $`m\geq 4`$,

```math
d(m)=m^2-m.
```

Even if Conjecture 1 does not hold, the following weaker asymptotic statement may still be true.

**Conjecture 2.**

```math
\lim_{m\to\infty}\frac{d(m)}{m^2}=1.
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
in the complex, ambient Zariski-closure model is 47. If the real
same-degree outputs are Euclidean dense at degree $`r`$, the complex
ambient Zariski closure contains the entire complex coefficient subspace
through degree $`r`$. Indeed, any polynomial equation vanishing on the
outputs also vanishes on the real degree-$`r`$ locus, and therefore on that
complex subspace. This gives

```math
d(7)\leq47.
```

This improves the general dimension bound $`d(7)\leq48`$. The
conjectured equality $`d(7)=42`$ remains open. MF-25 requires all higher
coefficients to vanish in every approximating output.

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
12 as the optimal degree for coverage in the ambient complex model.
Together these imply $`d(4)=12`$ in the formulation above.

### Five products cover degree 20 exactly

**Partial result (AI-derived).** Every real degree-20 polynomial has an
exact five-product evaluation, and no higher degree has real same-degree
density with five products. Thus $`d(5)=20`$.

**Five-product construction.** Let $`V=\mathop{\mathrm{span}}\nolimits\{1,x,x^2,x^4\}`$,
which is available after two products. A third product suffices to obtain
any monic degree-8 polynomial $`Q`$ with zero $`x^7`$ coefficient. To see
this, multiply $`x^4+u x^2+v x`$ by $`x^4+\tilde u x^2+\tilde v x`$.
The coefficients at degrees 6, 5, and 3 are $`u+\tilde u`$,
$`v+\tilde v`$, and $`u\tilde v+\tilde u v`$. Choose $`u,\tilde u`$
with the required sum and $`u\ne\tilde u`$, then solve the two linear
equations for $`v,\tilde v`$. Free additions from $`V`$ adjust all
remaining coefficients.

It suffices to construct the evaluation for monic degree-20 polynomials
$`p`$ with zero $`x^{19}`$ coefficient in a neighborhood of $`x^{20}`$.
Every centered monic $`p`$ can be brought into this neighborhood by
$`p(x)\mapsto s^{-20}p(sx)`$ for sufficiently large real $`s`$. Leading
coefficient normalization, translation to remove $`x^{19}`$, and the
inverse affine substitutions and scalar multiplications are free.

Choose $`B=x^4+x^2+x+w\in V`$ so that the coefficient of $`x^{-1}`$ in
the formal Laurent series $`S=\sqrt{p/B}`$ at infinity vanishes. Use the
square root with leading term $`x^8`$. With $`t=1/x`$ the desired
coefficient is the coefficient of $`t^9`$ in

```math
\sqrt{t^{20}p(1/t)}\,(1+t^2+t^3+w t^4)^{-1/2}.
```

Both factors have zero linear term, so a term with $`w^2`$, which first
occurs at degree 8, cannot contribute at degree 9. The desired coefficient
is therefore affine in $`w`$. At $`p=x^{20}`$ the
binomial expansion gives $`25/32-15w/8`$. The affine coefficient stays
nonzero for $`p`$ close to $`x^{20}`$, so the chosen $`w`$ depends
continuously on $`p`$ and equals $`5/12`$ at the base polynomial.

Let $`Q_0`$ be the strictly positive-degree part of $`S`$ and set

```math
j=\frac{[x^3]\bigl(p\bmod B\bigr)}{[x^3]\bigl(Q_0\bmod B\bigr)},\qquad
p-jQ_0=BT+R_0,\quad \deg R_0<4.
```

Here $`\bmod B`$ denotes the polynomial remainder. The denominator is
$`15/4`$ at $`p=x^{20}`$ and remains nonzero near it. By construction,
$`R_0\in V`$. Write $`q_i=[x^i]Q_0`$ and $`L_i=[x^i]\bigl(Q_0^2-T\bigr)`$.
Dividing $`jQ_0`$ by $`B`$ contributes only up to degree 4 to the
quotient. Since the $`x^7`$ and $`x^{-1}`$ coefficients of $`S`$ are
zero, comparison with $`S^2=p/B`$ gives $`L_i=0`$ for $`i\ge9`$ and
$`L_7=0`$.

Seek $`Q=Q_0+c`$ and $`D=\sqrt K\,x^4+d_2x^2+d_1x`$ with $`K>0`$
such that $`Q^2-D^2-T\in V`$. Take $`c=(K-L_8)/2`$ to match degree 8.
For $`i=3,5,6`$ put $`z_i=L_i+(K-L_8)q_i`$. Degrees 6 and 5 then
match if $`d_2=z_6/(2\sqrt K)`$ and $`d_1=z_5/(2\sqrt K)`$. Degree 3
matches exactly when

```math
F(K)=2Kz_3-z_6z_5=0.
```

At $`p=x^{20}`$, expansion and polynomial division give

```math
\begin{aligned}
Q_0&=x^8-\tfrac12 x^6-\tfrac12 x^5+\tfrac16 x^4+\tfrac34 x^3
       +\tfrac38 x^2-\tfrac58 x,\
j&=-\tfrac{2707}{1620},\\
(L_8,L_6,L_5,L_3)&=(\tfrac{95}{48},-\tfrac{43}{12},-\tfrac{25}{8},\tfrac{779}{96}),\\
F(K)&=\tfrac54 K^2+\tfrac{523}{48}K-\tfrac{17015}{3072}.
\end{aligned}
```

The leading coefficient of $`F`$ is positive and its constant coefficient
is negative. These strict signs persist near $`x^{20}`$, ensuring a
positive real root. With this root, the unmatched coefficients of
$`Q^2-D^2-T`$ can occur only at degrees $`0,1,2,4`$, all in $`V`$.
Compute $`Q`$ in the first three products as above. The fourth product
$`(Q+D)(Q-D)`$, followed by a free adjustment in $`V`$, gives $`T`$.
The fifth product gives $`BT`$, and $`p=BT+jQ+(R_0-jc)`$ follows by
free additions. All operations use real scalars.

**Degree exclusions.**

The available polynomials after each multiplication form a linear span with
a basis of distinct pivot degrees. A nonzero linear combination has degree
equal to the largest pivot degree with a nonzero coefficient. Adding a new
product increases the maximum degree only if the sum of its factor degrees
exceeds the old maximum. Such an increase adds that sum as a new pivot.

An output of degree above 20 requires the fourth-product span to have
maximum degree at least 11. Hence the third-product span has maximum
degree at least 6. After two products the pivot list is contained in either
$`(0,1,2,3)`$ or $`(0,1,2,4)`$. The only sums of two available degrees
that are at least 6 are 6 and 8, so these are the only relevant maxima
after the third product. If the third maximum is 6, all the other pivots
are at most 4. Only $`6+6=12`$ can reach 11 on the fourth product, and
only $`12+12=24`$ can then exceed 20. If the third maximum is 8, all the
other pivots are again at most 4. The fourth maximum can be 12 or 16,
and the fifth product can exceed 20 only at degree 24 or 32. These
exhaust the possible output degrees above 20.

Let $`X_m`$ be the complex Zariski closure of the polynomials computable
with at most $`m`$ products from $`1,x`$. It is irreducible because the product and output
coefficients in the straight-line parametrization range over an affine
space and the map to the output coefficients is polynomial. Redundant
gates allow outputs using fewer products in this parametrization.
Theorem 4.2 gives $`\dim X_m=m^2`$. Since repeated squaring attains
$`x^{2^m}`$, intersecting with the hyperplane of zero $`x^{2^m}`$
coefficient gives a proper closed subset of dimension at most $`m^2-1`$.
For $`m=5`$, this section contains every degree-24 output and has
dimension at most 24, below the degree-24 coefficient-space dimension
of 25. Thus its equations exclude real Euclidean density there. Degree
32 is excluded by $`\dim X_5=25<33`$.

The same hyperplane argument strengthens the general upper bound to
$`d(m)\le m^2-2`$ for $`m\ge 5`$. The dimension bound already excludes
degrees $`r\ge m^2`$, and the degree-$`(m^2-1)`$ coefficient space has
dimension $`m^2`$ and lies in the hyperplane since $`m^2-1<2^m`$.

### Six-product bounds

**Partial result (AI-derived).** In the real, same-degree model above,
$`24\le d(6)\le 32`$. The conjectured value $`d(6)=30`$ remains open.

**Exact degree-24 coverage.** Start with a centered monic degree-24
polynomial $`p`$ near $`x^{24}`$. Let $`q_*`$ be its polynomial quotient
by $`x^4`$ and let $`Q_*(x)=Q_0(q_*)(x)`$ denote the degree-8 polynomial
$`Q_0`$ produced from $`q_*`$ by the Laurent construction above. The
coefficient $`[x^3]Q_*`$ equals $`3/4`$ at $`p=x^{24}`$ and remains
nonzero nearby. Choose $`h=[x^3]p/[x^3]Q_*`$ and divide

```math
p-hQ_*=x^4q+R,\qquad \deg R<4.
```

The choice of $`h`$ gives $`\deg R\le2`$. The polynomial $`q`$ is
centered and monic, and it is near $`x^{20}`$ since $`h`$ tends to zero
as $`p`$ tends to $`x^{24}`$. Also $`q-q_*`$ has degree at most 4. In
the five-product construction, the coefficient of $`x^{-1}`$ determining
$`w`$ depends only on the coefficients of the input at degrees 11 through
20. The positive-degree part $`Q_0`$ of the square root likewise depends
only on these coefficients once $`w`$ is fixed. Thus $`Q_0(q)=Q_*`$.
The five-product program for $`q`$ makes $`x^4`$ and $`Q_*=Q-c`$
available. The sixth product forms $`x^4q`$, and free additions yield
$`p`$. Normalization, translation and scaling extend this local
construction to every real degree-24 polynomial as at degree 20.

**Degree exclusions.**

Start with $`V=\mathrm{span}\{1,x\}`$. One product augments $`V`$
by $`fg`$ with $`f,g\in V`$. Work over the complex numbers for the
dimension bound. Choose a degree-echelon basis with monic elements of
distinct degrees $`0=s_0< s_1=1< \cdots< s_\ell`$. If the two factors
have degrees $`s_i,s_j`$, with $`1\le i\le j`$, we can make them monic
and remove their constant terms without changing the augmented span:
the changes to the product, apart from an overall nonzero factor,
belong to $`V`$. The normalized factors therefore have at most
$`i+j-2`$ free coefficients in this basis. A gate that leaves
$`V`$ unchanged may be omitted.

Set $`z=s_i+s_j`$. If $`z`$ is not already a pivot degree, then it is the
new pivot. Otherwise reduce against the old basis: either the product
is redundant or the new pivot is an unused degree below $`z`$. Each
choice of pivots defines a chart on which the updated echelon basis is
a rational function of the old parameters and the new factor
coefficients. Requiring degrees to drop only restricts the parameter
domain. The first nonredundant product adds $`x^2`$ with no parameters.
The second adds either degree 3, giving the full space through
degree 3 with no parameters, or degree 4, represented modulo the old
span by $`x^4+c x^3`$ with at most one parameter.

The [standalone Python checker](../../references/mf25-six-product-bound/check_degree_bounds.py)
starts with pivots $`(0,1)`$ and bound 0. For each nonconstant pivot
pair it inserts the new sum, or tries every unused lower degree if
the sum is already present. It adds the parameter cost above and
keeps the maximum over paths to each pivot list. The computation
uses only integers and does not assume the candidate drops occur.

After at most five products, the maximum possible degree is 32 by
degree doubling. Thus an output of degree 33, 34, or 35 needs a sixth
product whose factor degrees sum to the target; its leading term
cannot be canceled by the earlier span. In the cases below, the
second bound includes the last product and up to eight output
coefficients.

- Degree 33: pivots $`(0,1,2,4,8,16,17)`$, factors of degrees
  16 and 17, parameter bound 15 before the last product and 32 after
  including the output; or pivots $`(0,1,2,4,8,16,32)`$, factors
  of degrees 1 and 32, bounds 19 and 32.
- Degree 34: pivots $`(0,1,2,4,8,9,17)`$ or
  $`(0,1,2,4,8,16,17)`$, factors both of degree 17, bounds 15
  and 33; pivots $`(0,1,2,4,8,16,18)`$, factors of degrees 16
  and 18, bounds 16 and 33; or pivots $`(0,1,2,4,8,16,32)`$,
  factors of degrees 2 and 32, bounds 19 and 33.
- Degree 35: no pair.

At degrees 33 and 34, the upper bounds 32 and 33 are strictly below
the full coefficient dimensions 34 and 35. The Zariski closure
of the finite union of rational images is therefore proper. A
nonzero polynomial vanishing on it cannot vanish on all of the real
exact-degree locus, so continuity rules out real density.
Degree 35 is impossible outright. At every degree
$`r\ge 36`$, the ambient dimension bound of 36 from Jarlebring and
Lorentzon's Theorem 4.2 is strictly less than $`r+1`$. Together
these give $`d(6)\le 32`$.

### Numerical evidence at six products

Jarlebring and Lorentzon obtained a real evaluation scheme for a degree-30
polynomial using an iteratively regularized Newton method, with a
combinatorial analysis of zero patterns in the evaluation schemes (§5,
Conjecture 5.2). This supports the conjectured degree but leaves Euclidean
density and optimality unresolved. The experiments and evaluation schemes
are in the [accompanying software repository](https://github.com/GustafLorentzon/polynomial-set-paper).

Earlier five-product work includes the numerical schemes in Jarlebring and
Lorentzon's §5, Conjecture 5.1, and the degree-20 construction in Sastre
et al.'s §4, where a real scheme is demonstrated for a particular polynomial.

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
