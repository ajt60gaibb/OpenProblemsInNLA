# MI-22: statements fixed before proofs

This is a statement-only formalization candidate for the complete retained
MI-22 conjecture. The proof strategy adapts Matthew J. Colbrook's counterexample
to make the required computations exact and smaller. **The adapted matrix B is
not the integer matrix printed in Colbrook's manuscript.** The adaptation and
formalization are prepared for George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena, California,
USA, with AI assistance. No new mathematical priority is claimed.

No proof implementation may begin before two independent statement approvals.
The source revision is `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`; the complete
canonical statement and complete source proof have been read. Exact source
locators, attribution, and the change of witness are recorded in
[SOURCE_CORRESPONDENCE.md](SOURCE_CORRESPONDENCE.md).

## 1. Complete target and actual mathematical objects

For every positive integer dimension `n`, every complex positive definite pair
`A,B`, and every real `t` with `0 ≤ t ≤ 1`, define the actual weighted mean and
left product

\[
A\#_tB=A^{1/2}(A^{-1/2}BA^{-1/2})^tA^{1/2},\qquad
L(A,B,t)=A^t(A\#_tB)B^{1-t}.
\]

Every matrix power in these definitions is the genuine Mathlib `CFC.rpow`.
The registered generic spectral-power theorem must identify it with unitary
spectral decomposition and real powers of all positive eigenvalues, for every
positive definite complex matrix and every real exponent. It does not replace
the target with powers of rational proxy matrices.

`singularValue A j` is Mathlib's actual
`(Matrix.toEuclideanLin A).singularValues j`. This is the decreasing sequence of
square roots of the eigenvalues of the actual adjoint composition, retaining
their multiplicities, followed by zeros past dimension `n`. Index zero denotes
the first singular value. The generic semantics theorem must prove
nonnegativity, decreasing order, vanishing beyond dimension, the exact
square-root/eigenvalue characterization, and equality of the first singular
value to the actual Euclidean operator norm.

`singularPrefix A k` is the product of entries with zero-based indices
`0,...,k−1`. `SingularLogMajorized X Y` includes **all** proper nonempty prefix
inequalities `1 ≤ k < n` and equality of the two products at `k=n`. Thus the
full target is

\[
\forall n\ge1\;\forall A,B\in\mathbb C^{n\times n},\ A,B>0\;
\forall t\in[0,1],\quad s(L(A,B,t))\prec_{\log}s(AB).
\]

The final export negates this entire statement. The formal target has no
commutation, real-only, fixed-dimension, selected-parameter, root-existence, or
certificate assumption. A real positive definite witness is a valid special
case of the quantified complex class. The endpoints are included; no theorem
asserts failure at every parameter. The source's wider semidefinite formulation
is not separately encoded, since the retained canonical target is positive
definite and a counterexample in that class suffices for its negation.

`operatorNorm A` explicitly denotes the norm of `Matrix.toEuclideanCLM A`,
acting on complex Euclidean space. It is not the default entrywise matrix norm.
`frobeniusSquared A` is the sum of the squared complex moduli of all entries.
The generic norm theorem must prove

\[
\|A\|_2^2\le\sum_{i,j}|A_{ij}|^2,\qquad
|(Ax)_i|\le\|A\|_2\|x\|_2
\]

for arbitrary complex matrices and genuine Euclidean vectors.

## 2. Exact adapted witness

Let

\[
D=\operatorname{diag}(16,1/16,1),\quad A=D^2,
\quad
T=\frac1{8192}
\begin{pmatrix}
4616&-39&-1250\\
-39&55069&-1519\\
-1250&-1519&6499
\end{pmatrix},\qquad B=DT^8D.
\]

The chosen parameter is `t=1/8`. The diagonal `A=diag(256,1/256,1)` is identical
to the source's A. The entries of T are the entries of the source's rational R
rounded to the nearest multiple of `1/8192`. This explains how the candidate was
selected; no rounding-error estimate is a premise. The definition of B by an
exact eighth power makes the corresponding principal root exactly T after
positivity is proved. The source's integer B and approximate root S are not
used in this adapted witness.

An exact LDL factorization to certify positivity is

\[
T=H\Delta H^*,\qquad
H=\begin{pmatrix}
1&0&0\\
-39/4616&1&0\\
-625/2308&-7060454/254196983&1
\end{pmatrix},
\]

\[
\Delta=\operatorname{diag}\left(
\frac{577}{1024},\frac{254196983}{37814272},
\frac{1555181999141}{2082381684736}\right).
\]

All three pivots are strictly positive and H has determinant one. The integer
numerator matrix has positive leading minors
`4616`, `254196983`, and `1555181999141`. These are exact diagnostics and a proof
plan; `T.PosDef`, `A.PosDef`, `B.PosDef`, and the factorization are all required
theorem conclusions. No matrix positivity is assumed from a floating-point
eigensolver.

Define

\[
F=\operatorname{diag}(2,1/2,1),\quad
E=\operatorname{diag}(32,1/32,1),\quad
N=ETDB,\quad v=(0,4/5,-3/5).
\]

The vector v is represented in genuine `EuclideanSpace ℂ (Fin 3)`, and its
norm must be proved to equal one. `witnessTestValue` is the real part of the
actual zeroth coordinate of `Matrix.toEuclideanCLM N v`; it is not a separately
declared certificate constant.

The finite inequalities to prove are exactly

\[
\operatorname{Re}\operatorname{tr} B <4^8,\qquad
44000 < \operatorname{Re}(Nv)_0,\qquad
\sum_{i,j}|(AB)_{ij}|^2<10500^2.
\]

The independent standard-library Fraction reconstruction records every entry
of `T²,T⁴,T⁸,B,N,AB`, every LDL pivot, the complete rational scalar values, and
all strict rational margins in `reviews/reconstruction.json`. Its decisive
checks use no floating-point arithmetic and no submitted verifier routines.
The data are selected before any Lean proof; the later Lean implementation
must prove these statements on the exact definitions, not import this JSON as
an axiom.

## 3. Principal-power reduction: exact, no root approximation

Set `Y = CFC.rpow B (1/8)` and retain it as the actual root. The principal-power
export must prove all the following:

\[
A^{1/2}=D,\quad A^{-1/2}=D^{-1},\quad A^{1/8}=F,\quad A^{5/8}=E,
\]

\[
(D^{-1}BD^{-1})^{1/8}=T,\qquad A\#_{1/8}B=DTD,
\]

\[
Y>0,\qquad Y^8=B,\qquad B^{7/8}Y=B,
\qquad L(A,B,1/8)Y=N,\qquad \|Y\|_2<4.
\]

The exact factor order in the last identity is crucial. Using the weighted
mean and `FD=E`, the product is
`F D T D B^(7/8) Y = E T D B = N`. Neither T nor Y is commuted across D or A.
The identity `B^(7/8)Y=B` only combines functions of the same positive matrix.
The eighth root of `T^8` is T because T is positive definite and the powers are
genuine CFC powers; a nonprincipal root cannot be substituted.

For the root bound, positivity gives `‖Y‖₂^8 = ‖Y^8‖₂ = ‖B‖₂`, while positivity
also gives `‖B‖₂ ≤ Re tr B <4^8`. Nonnegativity of the norm and strict
monotonicity of the eighth natural power yield `‖Y‖₂<4`. These CFC, positivity,
trace, and norm bridges are proof obligations; no residual-to-root theorem is
assumed.

## 4. From the exact coordinate to the original singular-value failure

For the actual unit vector v, the generic norm bounds and submultiplicativity
give

\[
44000<\operatorname{Re}(Nv)_0\le |(Nv)_0|
\le\|N\|_2=\|LY\|_2\le\|L\|_2\|Y\|_2.
\]

If `‖L‖₂≤11000`, then `‖Y‖₂<4` makes the right side at most 44000, a
contradiction. Thus `11000<‖L‖₂`. The Frobenius comparison separately gives
`‖AB‖₂<10500`.

The only planned LeanCert computation is the exact strict scalar comparison
`(10500 : ℝ) < 11000`, explicitly in **kernel** mode. It must be consumed when
combining these actual operator-norm bounds and then in the actual singular
value reversal and final negation. Matrix coefficients and eighth powers are
checked by exact algebra. The root Y is never evaluated numerically.

The first-singular-value/operator-norm identity gives
`singularValue (AB) 0 < singularValue L 0`. The `k=1<n=3` prefix condition in
the full original log-majorization therefore fails. The complete-product
equality is retained in the target; refuting one mandatory proper prefix
already refutes the whole conjunction.

## 5. Registered exports and trust gates

All declarations have the prefix `NLA.MI22.` and are registered in
`comparator.json`.

| Export | Required scope |
| --- | --- |
| `singular_values_semantics` | Actual sorted singular values, all multiplicities via the adjoint-composition eigenvalues, zero extension, and first value equals actual operator norm. |
| `spectral_power_semantics` | Generic principal spectral meaning of actual CFC powers for every complex positive definite input and every real exponent. |
| `euclidean_norm_bounds` | Generic true Euclidean action bound and squared Frobenius upper bound. |
| `witness_rational_data` | Every exact finite factorization, positivity, unit-vector, trace, tested-coordinate and Frobenius certificate, as conclusions. |
| `witness_principal_powers` | Every actual power identity, the noncommuting factor reduction, and the actual root norm bound. |
| `witness_operator_gap` | The two strict operator-norm estimates on the true canonical products. |
| `counterexample` | Original admissibility, strict actual singular-value reversal, and failure of full log-majorization. |
| `not_weightedLogMajorizationConjecture` | Unconditional negation of the entire canonical universal statement. |

No proof has been implemented at this stage. The only deliberate holes are in
Challenge. The future Solution must not import Challenge and must contain no
`sorry`, custom axiom, or native-trust proof. Only `propext`, `Classical.choice`,
and `Quot.sound` are permitted transitively. The dependency pins are Lean
4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`.

The computation plan uses three exact squarings for T⁸, a small LDL
factorization, one actual test vector, and a point inequality. It avoids matrix
root approximation, interval subdivisions, singular-value computation, and a
new resolvent-integration development. After two statement approvals, proof
implementation still needs two independent final referee reviews and the
repository's actual Linux kernel/Comparator workflow with its controls before
any formal-verification status promotion.
