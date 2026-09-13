# TR-15: statements fixed before proofs

This is a statement-only candidate for the complete retained TR-15 conjecture.
The mathematical counterexample and optional existence argument are due to
Matthew J. Colbrook. The formalization author is George Stepaniants, Department
of Computing and Mathematical Sciences, California Institute of Technology,
Pasadena, California, USA. AI assistance and independent review are recorded
separately; no human peer review or novelty claim is made here.

The source revision is `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.
The complete canonical statement and complete Colbrook manuscript were read,
including the nonvacuity argument and scope limitations. Exact source hashes
and locators are in [SOURCE_CORRESPONDENCE.md](SOURCE_CORRESPONDENCE.md).
No proof implementation may begin until two independent statement referees
approve the frozen definitions, challenge, and this numerical specification.

## 1. Full target, field, and quantifiers

All coefficients, vectors, and eigenvalues are real. For every natural-number
triple `(m,q,n)` with `Odd m`, `3 ≤ m`, `2 ≤ q`, and `2 ≤ n`, and **every**
finite generating vector

\[
h:\operatorname{Fin}(qm(n-1)+1)\longrightarrow\mathbb R,
\]

let `A` have order `m` and dimension `q(n−1)+1`, and let `B` have order `qm`
and dimension `n`, using exactly the same vector `h`. The complete original
conjecture is the implication

\[
(A\text{ has no negative real H-eigenvalues})
\quad\Longrightarrow\quad
(B\text{ has no negative real H-eigenvalues})
\]

universally quantified over this entire class. The final exported theorem is
`¬ InheritanceConjecture`. A single admissible counterexample disproves this
universal statement; the challenge is not merely the failure of an auxiliary
inequality. There is no associated-Hankel-matrix positivity assumption,
strong-Hankel condition, restriction to even upper order, or eigenpair-existence
premise in `InheritanceConjecture`.

## 2. Actual finite arrays and contractions

An order-`s`, dimension-`N` tensor is the finite array
`(Fin s → Fin N) → ℝ`. Its Hankel entry is `h` at the sum of its zero-based
indices. This agrees with the canonical one-based sum minus `s`.
`generatorIndex` proves the actual bound

\[
\sum_{j=0}^{s-1}i_j\le s(N-1)
\]

and indexes a finite generating vector of length `s(N−1)+1`. It does not use
an out-of-range default or an infinite extension of `h`. For the lower tensor,
`Fin.cast` identifies the equal lengths

\[
m\bigl((q(n-1)+1)-1\bigr)+1=qm(n-1)+1.
\]

It neither rescales nor reorders the generators. The higher tensor uses `h`
directly.

For a vector `x : Fin N → ℝ`, `contraction T x i` is the sum over **all**
functions `Fin (s−1) → Fin N` of the tensor entry with initial coordinate `i`,
times one `x` factor for each contracted coordinate. Equivalently,

\[
(Tx^{s-1})_i=
\sum_{i_2,\ldots,i_s=0}^{N-1}T_{i,i_2,\ldots,i_s}
  x_{i_2}\cdots x_{i_s}.
\]

There is no division by factorials or contraction normalization. Ordered tuples
appear separately, so cross-term multiplicities arise from the actual sum.
`IsHEigenpair T λ x` requires `x ≠ 0` and every component equation
`contraction T x i = λ * x i ^ (s−1)`. The power is the ordinary integer power
of the signed real coordinate, not its absolute value, norm, or complex power.
`HasNoNegativeHEigenvalues T` says every such pair has `0 ≤ λ`; over the reals
this is exactly the absence of a pair with `λ < 0`. No theorem premise assumes
that the contractions or eigen-equations below already hold.

The generic array definitions are total at order zero, but all conjecture
instances have lower order at least three and higher order at least six. That
unused totalization cannot affect any quantified admissible instance.

## 3. Exact counterexample data

Use

\[
m=3,\quad q=2,\quad n=2,\qquad
h=(2,0,1,0,2,0,-1).
\]

Both source lengths are exactly seven: `3(3−1)+1 = 6(2−1)+1 = 7`.
The lower tensor is order three, dimension three, and the upper tensor is
order six, dimension two. The definitions `witnessLower` and `witnessUpper`
invoke the same generic construction used by the full conjecture.

For **every** real vector `x=(x₀,x₁,x₂)`, the exact lower contraction is

\[
Ax^2=\begin{pmatrix}
(x_0+x_2)^2+x_0^2+x_1^2+x_2^2\\
2x_0x_1+4x_1x_2\\
x_0^2+2x_1^2+4x_0x_2-x_2^2
\end{pmatrix}.
\]

Its first component is strictly positive for every nonzero real vector.
Consequently any H-eigenpair satisfies a strictly positive first component
equal to `λ x₀²`, forcing `x₀ ≠ 0` and `λ > 0`. This is universal positivity
for **all** real lower H-eigenpairs, not a sampled spectrum or a lower bound
for a selected eigenvalue.

For the actual upper tensor and `v=(0,1)`, each component contraction has
one nonzero summand, where all five contracted indices equal one. Thus

\[
Bv^5=(h_5,h_6)=(0,-1)=-1\,(v_0^5,v_1^5).
\]

The vector is nonzero and `−1 < 0`. These give the original premise for `A`
and negate the original conclusion for `B` at admissible parameters.

## 4. Nonvacuous lower premise

The manuscript additionally proves that the lower tensor has a real eigenpair.
This is an unconditional export, separate from the premise of the conjecture.
Define

\[
F(t)=2t^4+2t^3+3t^2-4t-1,\qquad
\lambda(t)=2+2t+2t^2,\qquad x(t)=(1,0,t).
\]

The required numerical statements are `F(0)=−1`, `F(1)=2`, and continuity of
this real polynomial on `[0,1]`. The intermediate value theorem then supplies
an **actual** root `0<t<1`. At every such root, the exact contraction equations
make `(λ(t),x(t))` a genuine H-eigenpair. The vector is nonzero because its
first component is one. The challenge includes the open interval, the actual
polynomial equation, and the eigenpair property; it does not assume a root or
use a numerical approximation as the eigenvector.

## 5. Registered challenge exports

All declarations below use the prefix `NLA.TR15.` and are registered in
`comparator.json`.

| Declaration | Exact scope |
|---|---|
| `lower_contractions` | All three actual contraction formulas for every real `x : Fin 3 → ℝ`. |
| `upper_contraction` | Actual full upper contraction at `v=(0,1)`. |
| `lower_eigenvalues_pos` | Strict positivity for every real lower H-eigenpair. |
| `lower_eigenpair_exists` | A root strictly in `(0,1)` with its actual lower H-eigenpair. |
| `upper_negative_eigenpair` | The explicit real upper H-eigenpair and strict negative eigenvalue. |
| `counterexample` | Original parameter admissibility, original lower premise, and failed upper conclusion. |
| `not_inheritanceConjecture` | Negation of the entire original universal conjecture. |

## 6. Computation and trust plan

Use exact finite sums, integer polynomial algebra, positivity of squares, and
Mathlib's real intermediate value theorem. The first lower slice alone proves
universal eigenvalue positivity; computing eigenvalues is unnecessary. For the
upper contraction, vanishing vector factors eliminate every tuple except the
all-one tuple. Even a direct expansion would cover only 27 lower tensor entries
and 64 upper entries; no large interval partition is justified.

Retain one explicit LeanCert **kernel** point certificate for `(-1 : ℝ) < 0`.
It must be consumed by `upper_negative_eigenpair` and hence by the actual
counterexample and full conjecture negation. The IVT argument needs no root
isolation, interval subdivision, floating-point approximation, or tolerance.
Polynomial endpoint values and all tensor coefficients are exact integers.

The project pins Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`,
and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. Only the standard axioms
`propext`, `Classical.choice`, and `Quot.sound` may occur transitively in final
exports. Proof sources will select kernel trust explicitly and undergo
`#assert_trust kernel`, actual axiom printing, two independent final reviews,
and the repository's real Linux Comparator workflow with its negative controls.
macOS elaboration is only a local gate. The intentional challenge placeholders
are not proof bodies and must never be imported by the eventual solution.

## 7. Reuse and limitations

The array and contraction definitions follow the original multi-way-array
meaning directly, using Mathlib `Fin`, finite function spaces, sums, products,
and real arithmetic. A general multilinear tensor-product development would
add interfaces that are unnecessary for this target. The proof will reuse
Mathlib's finite sum and IVT APIs rather than implement root finding or a
tensor-eigenvalue solver.

This refutes the retained odd-order inheritance conjecture. It does not prove
that every odd-order instance fails, classify other generating vectors, or
refute inheritance under an additional positive-semidefinite associated Hankel
matrix hypothesis. The source's historical and priority comments remain outside
the formal target. The canonical mathematical status remains `Solved` while
formal verification gates are pending.
