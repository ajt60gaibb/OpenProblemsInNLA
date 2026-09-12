# SP-03: A saturated skew-multiplier system for symplectic critical points

**Author:** Sidney Holden  
**Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.  
**Submission date:** 12 September 2026.  
**Editorial record:** [Attribution, independent review and scope](../README.md).

The review statements below describe the supplied draft; the linked submission record records subsequent independent review.

**Scope:** An all-ranks algebraic reduction, with a complete rederivation of
$`D_1=4`$. **No formula for $`D_m`$ in general is proved here.**

**Review status:** Session-derived argument and exact symbolic checks; not
independently reviewed or formally verified. No novelty claim. The order-one
value is already recorded in the source and is included only as a consistency
check.

## 1. Setup

Put $`N=2m`$ and


```math
J=\begin{pmatrix}0&I_m\\-I_m&0\end{pmatrix},\qquad
\mathrm{Sp}_{N}(\mathbb C)=\{X:X^TJX=J\}.
```


All pairings in this note are the complex bilinear Frobenius pairing
$`\langle Y,Z\rangle=\mathop{\mathrm{tr}}\nolimits(Y^TZ)`$; no conjugate transpose is
used. For fixed data $`U`$, the critical points are those of


```math
f_U(X)=\mathop{\mathrm{tr}}\nolimits((X-U)^T(X-U))
```


on this smooth affine variety.

The repository asks whether the generic number is
$`D_m=2^{m^2}+2^{2m-1}`$. The purpose here is to give a smaller, auditable
system for that count while specifying exactly what must be excluded when
denominators are cleared.

Let $`\mathcal K_N=\{K:K^T=-K\}`$, of dimension
$`r=N(N-1)/2=m(2m-1)`$.

## 2. Normal-space equation

### Lemma 1

A symplectic matrix $`X`$ is a critical point if and only if there is a unique
$`K\in\mathcal K_N`$ satisfying


```math
U=X+JXK.
\tag{1}
```



### Proof

The derivative of the constraint at $`X`$ maps a matrix $`Y`$ to


```math
Y^TJX+X^TJY.
\tag{2}
```


It is onto the skew-symmetric matrices. Indeed, for prescribed skew-symmetric
$`W`$, put $`Y=\tfrac12 XJ^{-1}W`$. Then $`X^TJY=W/2`$, and
$`Y^TJX=-(X^TJY)^T=W/2`$. Thus the tangent space has codimension $`r`$.
It consists precisely of the matrices for which $`Z=X^TJY`$ is symmetric.

For skew-symmetric $`K`$,


```math
\langle JXK,Y\rangle=\mathop{\mathrm{tr}}\nolimits(KX^TJY)=\mathop{\mathrm{tr}}\nolimits(KZ)=0
```


on that tangent space. The map $`K\mapsto JXK`$ is injective, since both
$`J`$ and $`X`$ are invertible. Its image therefore has the full normal-space
dimension $`r`$ and equals the orthogonal complement of the tangent space.
The derivative of $`f_U`$ vanishes there exactly when $`U-X`$ belongs to
this image. Injectivity also proves uniqueness. $`\square`$

## 3. Elimination of X

For $`K\in\mathcal K_N`$, let


```math
Q=I+K^2.
```


The matrix $`Q`$ is symmetric and commutes with $`K`$. Equation (1) implies


```math
U-JUK=X(I+K^2)=XQ.
\tag{3}
```


Consequently, when $`\det Q\ne0`$,


```math
X=(U-JUK)Q^{-1}.
\tag{4}
```


Conversely, substitution into $`X+JXK`$, using $`J^2=-I`$ and
$`KQ=QK`$, shows that (4) satisfies (1).

Write


```math
G=U^TU,\qquad R=U^TJU.
```


The first is symmetric, the second skew-symmetric. A direct expansion gives


```math
(U-JUK)^TJ(U-JUK)=R+GK+KG-KRK.
\tag{5}
```


Since $`Q^T=Q`$, imposing $`X^TJX=J`$ in (4) is equivalent to


```math
R+GK+KG-KRK-(I+K^2)J(I+K^2)=0.
\tag{6}
```


Both sides are skew-symmetric. Thus their strict upper-triangular entries give
$`r`$ polynomial equations, each of degree at most four, in the $`r`$
independent entries of $`K`$.

### Theorem 2 — exact correspondence on the regular locus

The solutions of (6) with $`K^T=-K`$ and $`\det(I+K^2)\ne0`$ are in
bijection, by (4), with critical points having a multiplier with the same
nonvanishing determinant. The multiplier is unique.

**Proof.** Equations (3)–(6) establish both directions, and Lemma 1 supplies
criticality and uniqueness. $`\square`$

## 4. Why the omitted locus is generically absent

This step is essential: one cannot simply assume that a denominator is nonzero
at all solutions.

### Proposition 3

There is a proper Zariski-closed set of data matrices outside which every
critical point satisfies $`\det(I+K^2)\ne0`$.

### Proof

The full critical incidence is parametrized by the polynomial map


```math
\Phi:\mathrm{Sp}_{N}(\mathbb C)\times\mathcal K_N\longrightarrow
\mathbb C^{N\times N},\qquad \Phi(X,K)=X+JXK.
```


The symplectic group is smooth of dimension $`N^2-r`$, as follows from the
surjectivity calculation (2). The polynomial
$`g(K)=\det(I+K^2)`$ is not identically zero on $`\mathcal K_N`$, because
$`g(0)=1`$. Its zero set has dimension at most $`r-1`$. Therefore


```math
\dim\bigl(\mathrm{Sp}_{N}(\mathbb C)\times\{g=0\}\bigr)\le N^2-1.
```


The Zariski closure of its image under a polynomial map has dimension no greater
than its domain. That closure is consequently a proper Zariski-closed subset
of the $`N^2`$-dimensional data space. Outside it, (1) has no symplectic
solution with $`g(K)=0`$. Lemma 1 identifies precisely those solutions with
critical points. $`\square`$

Only standard algebraic dimension facts enter this argument: a nonzero
polynomial on affine space defines a set of dimension at most one less, product
dimensions add, and polynomial images do not increase dimension. The argument
does not infer genericity from a numerical sample.

### Algebraic implementation warning

Let $`I_U`$ be the ideal generated by the upper-triangular entries of (6).
The desired regular system is obtained by saturation


```math
I_U:\det(I+K^2)^\infty,
\tag{7}
```


or, equivalently for computations, by adjoining a variable $`z`$ and the
equation $`z\det(I+K^2)-1=0`$. Raw solutions of the cleared quartics can
contain spurious singular-denominator components. Proposition 3 concerns
actual critical points; it does not authorize counting those extra components.

Equations (4), (6), and (7) reduce the original generic critical-point count to
an explicit saturated system. They do not evaluate its degree.

## 5. The order-one check

For $`m=1`$, every skew-symmetric multiplier has the form $`K=tJ`$.
Then $`Q=(1-t^2)I`$. Put


```math
\rho=\det U,\qquad \tau=\mathop{\mathrm{tr}}\nolimits(U^TU).
```


In dimension two, $`R=\rho J`$ and $`GJ+JG=\tau J`$. Equation (6) reduces
to the scalar quartic


```math
q_U(t)=(1-t^2)^2-\rho(1+t^2)-\tau t
=t^4-(2+\rho)t^2-\tau t+1-\rho=0.
\tag{8}
```


For generic $`U`$, this quartic has four distinct roots, none equal to
$`1`$ or $`-1`$. To justify both generic assertions explicitly, take
$`U=\mathop{\mathrm{diag}}\nolimits(2,3)`$. Then


```math
q_U(t)=t^4-8t^2-13t-5,
```


whose discriminant is $`-16075\ne0`$, and whose values at $`1,-1`$ are
$`-25,1`$, respectively. Thus the relevant discriminant and exceptional-root
conditions are nonzero polynomials in the data entries. Together with
Proposition 3, Theorem 2 gives exactly four critical points for generic data.
Hence $`D_1=4`$, agreeing with the already-known value.

## 6. Remaining target and sources

Nothing here proves $`D_m=2^{m^2}+2^{2m-1}`$ for $`m\ge2`$. The missing step
is a generic degree calculation for (7), including control of multiplicity and
possible contributions at infinity in any chosen compactification. Counting
solutions for a special data matrix would not alone supply that step.

The target and its known small-rank evidence are taken from the pinned SP-03
README. Primary context: J. A. Baaijens and J. Draisma, *Euclidean distance
degrees of real algebraic groups*, Linear Algebra and its Applications 467
(2015), 174–187, Section 5; arXiv:1405.0422. Repository and manuscript
identifiers are recorded in `../sources/snapshot.json` and `../sources/REFERENCES.md`.
