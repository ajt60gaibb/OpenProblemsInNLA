# MI-23: exact statement boundary and numerical targets

This file is fixed before proof implementation. It describes Matthew J. Colbrook's
complete counterexample to the canonical MI-23 conjecture. Formalization is by
George Stepaniants, Department of Computing and Mathematical Sciences, California
Institute of Technology, Pasadena, California, USA, with AI-agent assistance.
No theorem in this project has yet been proved; the eight Challenge placeholders
are deliberate statement-review obligations, not a solution.

The source is [the complete informal proof](../solution.tex), Theorem 1.1 and its
proof, and the [canonical original target](../README.md), at repository revision
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. The primary research statement is
[Ghabries–Abbas–Mourad–Assi, arXiv:2105.13356v1](https://arxiv.org/pdf/2105.13356v1),
Conjecture 2.1 on page 6; the definition of log-majorization is on page 2. The
canonical target restricts its inputs to positive definite complex matrices.

## Full universal target

For every integer `n ≥ 1`, every `A,B : Matrix (Fin n) (Fin n) ℂ` with genuine
`Matrix.PosDef` hypotheses, every real `r,s,p,t` satisfying

```
p ≥ 1,   0 ≤ t ≤ 1,   ((r ≥ 1 and s ≥ 1) or (r ≤ 0 and s ≤ 0)),
```

the conjecture asserts

```
λ(G(r,t)^p G(s,1-t)^p) ≺log λ(A^(p(r+s-1)) B^p),
G(r,t) = A^(r/2) (A^(-1/2) B A^(-1/2))^t A^(r/2).
```

All real powers in this expression are `CFC.rpow`, in the displayed factor order.
No exponent is limited to integers or rationals in the conjecture. The negative
`r,s` region and the endpoints `t=0,1` remain present. The fixed rational witness
is used to negate the universal assertion, not to redefine it.

`orderedEigenvalues X` sorts the real parts of **all actual characteristic-polynomial
roots with multiplicity** in decreasing order. For every product of positive
definite matrices, `product_eigenvalue_semantics` must prove its list has length
`n`, is decreasing and strictly positive, contains every complex root after the
real-to-complex embedding, and has product equal to the genuine determinant. In
particular, mapping roots to real parts cannot hide a nonreal root: the reverse
multiset equality is an explicit obligation. The same theorem must prove an
explicit invertible similarity to `Y^(1/2) X Y^(1/2)` and characteristic-polynomial
equality. `positive_powers_and_means` supplies the generic definiteness facts for
all real exponents used by the full target.

For two equal-length positive decreasing lists, `LogMajorized` includes every
nonempty **proper** prefix-product inequality and equality of the **complete**
products. It is not weak log-majorization. Positivity and ordering are proved
separately for the matrices in the target. Failure of the first prefix inequality
at a three-dimensional witness suffices to refute the entire relation; the other
prefixes and determinant equality are retained in the definition.

## Rational witness and exact positivity

```
D = diag(16, 1/12, 1),             Dinv = diag(1/16, 12, 1),
T = [[2,1,2],[1,25,-10],[2,-10,10]],
A = D^2,                         B = D T^8 D,
r = s = 1,                       p = 2,                    t = 1/8.
```

The convenient exact positivity certificate is

```
L = [[1,0,0],[1/2,1,0],[1,-22/49,1]],
P = diag(2, 49/2, 150/49),
T = L P L*,
```

where `L` is invertible and all three pivots are strictly positive. This avoids
numeric eigenvalue isolation or an additional Sylvester-criterion development.
Every matrix is regarded as a complex matrix; real entries do not restrict the
universal complex target.

The required CFC identities are

```
A^(1/2) = D,   A^(-1/2) = Dinv,
A^(-1/2) B A^(-1/2) = T^8,
G(1,1/8) = G = D T D,
G(1,7/8) = H = D T^7 D.
```

All of `D,T,A,B,G,H` must be proved positive definite. Positivity of `T`, genuine
functional calculus, the power-composition laws and the natural-power bridge
justify `(T^8)^(1/8)=T` and `(T^8)^(7/8)=T^7`. These are analytic theorems, not
identifications inferred from a numerical check. The target products at the
witness must equal `G^2 H^2` and `A^2 B^2` respectively.

## The single numerical separation

With paper indices `(1,3)` corresponding to Lean indices `(0,2)`, the exact
complex entry and real Frobenius sum are

```
(G H)[0,2] = 1260589125202 / 9,
FrobSquared(A B) = 2009446159144992718181231562721 / 107495424,
normSq((G H)[0,2]) - FrobSquared(A B)
    = 99434824489435745411095588895 / 107495424 > 0.
```

`FrobSquared` sums `Complex.normSq` over all nine entries. No default matrix norm,
entrywise absolute-value sum or norm of just one row replaces it. Rational
matrix multiplication uses repeated squaring (`T²`, `T⁴`, `T⁸`, and `T⁷=T⁴T²T`)
and exact arithmetic. The scalar positive-gap inequality is the only planned
LeanCert certificate, using explicit `trust := kernel` and a singleton interval
for a constant expression. No subdivision or search over parameter boxes,
eigenvalues, matrix entries or unitary matrices is required. The final strict
norm comparison must retain the checked scalar certificate in its proof term.

## Analytic norm/eigenvalue obligations

`operatorNorm X` is explicitly `‖Matrix.toEuclideanCLM X‖` on complex Euclidean
space. The generic estimates to prove are

```
normSq(X[i,j]) ≤ operatorNorm(X)^2 ≤ FrobSquared(X).
```

For positive definite `X,Y` in a positive dimension, the actual first ordered
eigenvalue must satisfy

```
largestEigenvalue(X^2 Y^2) = operatorNorm(X Y)^2.
```

The reason is the similarity of `X²Y²` to `Y X² Y = (XY)* (XY)` and the genuine
spectral theorem for the positive Gram matrix. The semantic bridge cannot be
replaced by a definition that calls an operator norm an eigenvalue. The zero
default in `largestEigenvalue` is proved irrelevant by the positive list length.

The rational gap and generic norm bounds then give
`operatorNorm(A B)^2 < operatorNorm(G H)^2`, so the first actual ordered
eigenvalue on the left is larger than the first on the right. This contradicts
the full `LogMajorized` relation at `n=3` and the admissible fixed parameters.
The final theorem is exactly `¬ GeneralizedGeometricMeanConjecture` with no
additional hypotheses or imported unproved literature assertions.

## Review and trust gates

`Challenge.lean` contains eight exports: generic positive powers/means, product
eigenvalue semantics, the squared-product largest eigenvalue identity, genuine
operator norm bounds, exact witness data, the strict squared gap, the actual
counterexample, and full universal negation. Two independent statement referees
must approve Definitions, Challenge and this file before proof implementation.
Final proof review must re-elaborate actual source, inspect transitive axioms and
the numerical certificate consumer, and check all generic semantic bridges.

The later solution may depend transitively only on `propext`, `Classical.choice`
and `Quot.sound`; no `sorryAx`, native-execution axiom, custom axiom, or
unrecorded foreign oracle is permitted. Real Linux sandbox/Comparator/default
kernel checks remain a separate publication gate. The exact dependency pins are
in `lean-toolchain` and `lake-manifest.json`.

The in-session exact rational Python reconstruction is supplementary only. It
does not establish any CFC identity, positive-definiteness theorem, matrix-norm
bridge, eigenvalue semantics or Lean proof. No result is marked Lean verified at
this statement stage.
