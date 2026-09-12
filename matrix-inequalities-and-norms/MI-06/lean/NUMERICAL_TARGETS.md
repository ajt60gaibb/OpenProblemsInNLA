# MI-06: frozen numerical and semantic targets

This is a statement-first draft of the fixed rational counterexample in Matthew
J. Colbrook's [complete source proof](../solution.tex), Corollary 1.2, following
Theorem 1.1. George Stepaniants's formalization work is affiliated with the
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. These statements require two independent
approvals before any Lean proof implementation begins.

## Exact original target

For every positive integer `n` and **every pair of complex square matrices**
`A,B`, the canonical conjecture asks for **complex unitaries** `U,V` such that

\[
S(A+B)\preceq\sqrt2\bigl(US(A)U^*+VS(B)V^*\bigr),\qquad
S(X)=\tfrac12\bigl((X^*X)^{1/2}+(XX^*)^{1/2}\bigr).
\]

`matrixModulus` is Mathlib's actual `CFC.abs`, whose definition is
`CFC.sqrt (star X * X)`. Matrix star is conjugate transpose. The explicitly
opened `MatrixOrder` interprets `P ≤ Q` as `(Q-P).PosSemidef`; it is the ordinary
Hermitian PSD order. `Matrix.unitaryGroup` supplies genuine complex unitaries.
The factor is the nonnegative real square root, embedded into the complex
scalars. No assumption of real entries, Hermitian inputs, invertibility, or a
selected unitary pair is added to `DominationConjecture`.

The final statement is `¬ DominationConjecture`. The counterexample happens to
have real rational entries, which are valid complex inputs. The source's
stronger assertion that **no finite constant** works is outside this
formalization's scope.

## Exact witness and all modulus obligations

Use `n=3`, `t=3/4`, and

\[
A=\begin{pmatrix}1&3/4&0\\0&0&0\\0&0&0\end{pmatrix},\quad
B=\begin{pmatrix}-1&0&0\\0&0&0\\-3/4&0&0\end{pmatrix}.
\]

Every entry below is exact. The target `witness_moduli` requires identification
with the **actual CFC quantities**, not an assumption that the tables are
correct:

| Quantity | Exact matrix |
| --- | --- |
| `matrixModulus A` | `[[4/5,3/5,0],[3/5,9/20,0],[0,0,0]]` |
| `matrixModulus A.conjTranspose` | `diag(5/4,0,0)` |
| `matrixModulus B` | `diag(5/4,0,0)` |
| `matrixModulus B.conjTranspose` | `[[4/5,0,3/5],[0,0,0],[3/5,0,9/20]]` |
| `matrixModulus (A+B)` | `diag(3/4,3/4,0)` |
| `matrixModulus (A+B).conjTranspose` | `diag(3/4,0,3/4)` |
| `symmetricModulus A` | `[[41/40,3/10,0],[3/10,9/40,0],[0,0,0]]` |
| `symmetricModulus B` | `[[41/40,0,3/10],[0,0,0],[3/10,0,9/40]]` |
| `symmetricModulus (A+B)` | `diag(3/4,3/8,3/8)` |

For each of the six modulus tables, the future implementation must establish
positive semidefiniteness and the square identity against the appropriate
`X.conjTranspose * X`, then use uniqueness of the positive CFC square root.
Rational Gram/outer-product decompositions suffice. The generic exported
`modulus_eq_sqrt` also requires that every complex matrix's `matrixModulus` is
the positive square root and is PSD.

## All-unitary obstruction without eigenvalue computation

Set `u=(3,1,0)`, `v=(3,0,1)`. With mathematical coordinates numbered 1,2,3,
the two exact decompositions in `witness_moduli` are

\[
S(A)=\tfrac18I+\tfrac1{10}uu^*-\tfrac18E_{33},\qquad
S(B)=\tfrac18I+\tfrac1{10}vv^*-\tfrac18E_{22}.
\]

Lean's `Fin 3` coordinates are numbered 0,1,2. Thus `missingA` is the
projector at coordinate 2 and `missingB` at coordinate 1. `rankOne w` is
the actual outer product `w w*`, with complex conjugation retained.

`two_vector_orthogonal` requires that **any** `a,b : Fin 3 → ℂ` have a vector
`w` with `0 < squaredLength w`, `star a ⬝ᵥ w = 0`, and
`star b ⬝ᵥ w = 0`. This follows from the nontrivial kernel of the linear map
from three complex coordinates to these two inner products; no independence
assumption on `a,b` is allowed. This is a universal linear-algebra obligation,
not a numerical search over unitaries.

For arbitrary unitaries `U,V`, `witness_quadratic_bounds` requires such a
nonzero `w` orthogonal to `Uu,Vv` and the three bounds

\[
\begin{split}
\tfrac38\,\ell(w)&\le q(S(A+B),w),\\
q(US(A)U^*,w)&\le\tfrac18\,\ell(w),\\
q(VS(B)V^*,w)&\le\tfrac18\,\ell(w),
\end{split}\qquad
\ell(w)=\sum_i|w_i|^2,\quad q(H,w)=\operatorname{Re}(w^*Hw).
\]

These are precisely the definitions of `squaredLength` and `quadraticForm`.
The function norm's default convention is never used. Replacing the source's
unit vector by a nonzero vector and retaining its positive length is the
homogeneous version of the same argument; it avoids a normalization square
root and does not weaken the obstruction. The PSD-to-quadratic-form implication
and unitary preservation of `squaredLength` must be proved or imported from
the pinned Mathlib library. Taking a real part is valid here because the
matrices are Hermitian and complex PSD nonnegativity implies nonnegative real
part; it must not become a substituted definition of PSD order.

## Minimal LeanCert numerical statement

The sole required strict scalar comparison is

\[
2<\frac94=\left(\frac32\right)^2,
\]

with exact rational gap `1/4`. Its kernel-checked LeanCert point certificate,
along with nonnegativity of `Real.sqrt 2`, yields `Real.sqrt 2 < 3/2` and hence
`Real.sqrt 2 / 4 < 3/8`. That certificate must remain in the transitive proof
of the counterexample; an unused decorative invocation does not meet this
target. There are no interval boxes, irrational matrix entries, approximate
eigenvalues, numerical unitary searches, or native-execution axioms needed.

Combining the three quadratic bounds with an assumed PSD domination would
give `(3/8)*ℓ(w) ≤ (sqrt 2/4)*ℓ(w)`, contradicting `ℓ(w)>0`. The resulting
`counterexample` quantifies over **every** complex unitary pair. Instantiating
the complete universal `DominationConjecture` at `n=3,A,B` then proves its
negation, without strengthening its premises.

## Review boundary

The six names in `comparator.json` are the intended public exports. The
Challenge contains exactly six intentional placeholders; no mathematical
proof body is supplied at this stage. Independent referees must inspect the
elaborated statements, the original canonical page and complete source, the
actual imported CFC/PSD/unitary definitions, the exact rational tables, and
the full universal negation. Only after both approve the frozen statement
hashes may implementation begin. The supplementary rational precheck is a
calculation aid, not a Lean proof, independent review, or formal certification.
