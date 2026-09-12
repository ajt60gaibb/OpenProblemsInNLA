# MI-26: frozen statement and numerical obligations

**Stage:** statement specification only. No implementation proof has started.
The seven intentional `Challenge.lean` placeholders are statement declarations,
not verification evidence. Proof implementation must wait for two independent
statement reviews of the compiled, hash-bound files.

**Mathematical result:** Matthew J. Colbrook, Department of Applied Mathematics
and Theoretical Physics, University of Cambridge. The complete local source is
[Theorem 1.1 and its proof](../solution.tex), especially its first, projection
counterexample. The [canonical MI-26 target](../README.md) and
[source attribution and scope](../solution.md) are preserved unchanged.

**Formalization:** George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.

Source base: upstream commit
`587bd896f0e1006f4a4b7f38555e3a523ef85176`, fetched before the isolated branch was
created. Exact source and statement hashes are retained in
`verification/statement-freeze/hashes.json` after successful elaboration.

## 1. Complete original target and its Lean representation

The canonical assertion quantifies over every integer `n ≥ 1`, every pair of
positive semidefinite complex `n × n` matrices `A,B`, and every real-valued
concave `f : [0,∞) → ℝ` satisfying only `f(0) ≥ 0`. It asks for two complex
unitaries `U,V`, which may depend on all preceding data, such that

\[
 f(A+B) \preceq U f(A) U^* + V f(B) V^*.
\]

`SubadditivityConjecture` retains all these quantifiers and uses
`Matrix.PosSemidef` and the `MatrixOrder` scoped order, where `X ≤ Y` is
**exactly** `(Y-X).PosSemidef`. A `Matrix.unitaryGroup (Fin n) ℂ` element is a
genuine arbitrary complex unitary, not a real orthogonal or enumerated matrix.
`unitaryConjugate` uses ordinary matrix products and the conjugate transpose.

The scalar function is represented by `f : ℝ → ℝ` whose values at negative
arguments are unconstrained. `AdmissibleFunction` is exactly
`ConcaveOn ℝ (Set.Ici 0) f ∧ 0 ≤ f 0`. This representation does not narrow the
half-line function class: any function on `[0,∞)` extends to all reals by
assigning its value at `max(t,0)`, and restriction recovers the original
function. The extra `Convex ℝ (Set.Ici 0)` component of Mathlib's `ConcaveOn`
predicate is a property of the fixed domain, not a new condition on `f`.

The public theorem `admissibleFunction_iff` must identify the predicate with
the exact scalar definition from the canonical page:

\[
f(0)\ge0,\qquad
\theta f(x)+(1-\theta)f(y)
\le f(\theta x+(1-\theta)y)
\quad(x,y\ge0,\ 0\le\theta\le1).
\]

No global nonnegativity, monotonicity, continuity, strict positivity of the
matrix inputs, or spectral-separation condition may appear as an additional
premise of the original target or its negation.

## 2. Genuine functional calculus and domain fidelity

`functionalCalculus f A` is the actual Mathlib `cfc (R := ℝ) f A` in the
complex matrix algebra, not the witness polynomial evaluated by definition.
For every Hermitian matrix `A` and every real function `f`, the public
`functionalCalculus_eq_spectral` obligation is

\[
 \operatorname{cfc}(f,A)
 = W\,\operatorname{diag}(f(\lambda_1),\ldots,f(\lambda_n))\,W^*,
\]

where `W = hA.eigenvectorUnitary` and `λᵢ = hA.eigenvalues i` are the genuine
Mathlib spectral theorem objects associated with `hA : A.IsHermitian`.
There is **no continuity hypothesis on `f`**: all functions are continuous on
the finite spectrum of a Hermitian matrix. This matters because concavity on
a closed half-line alone must not silently be used to add endpoint continuity.

The generic `functionalCalculus_congr_nonneg` obligation further states that
two arbitrary functions agreeing on `[0,∞)` give the same actual CFC value at
every PSD input. This verifies that unrestricted negative-argument extensions
do not affect the original problem.

Primary pinned library sources to use and independently inspect:

- Mathlib `Analysis/Matrix/HermitianFunctionalCalculus.lean`:
  `Matrix.IsHermitian.cfc`, `Matrix.IsHermitian.cfc_eq` (arbitrary functions on
  the finite spectrum), and the associated spectral representation.
- Mathlib `Analysis/Matrix/Order.lean`: `Matrix.le_iff`,
  `Matrix.nonneg_iff_posSemidef`, and the genuine nonnegative spectrum instance.
- Mathlib `LinearAlgebra/Matrix/PosDef.lean`:
  `Matrix.PosSemidef.dotProduct_mulVec_nonneg` supplies the actual complex
  quadratic-form consequence of positive semidefiniteness.
- Mathlib `Analysis/Convex/Function.lean`: the definition of `ConcaveOn`.

All are at Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

## 3. Exact witness and numerical statements

Use precisely Colbrook's first witness:

\[
 f(t)=t-t^2,\qquad
 P=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
 Q=\frac1{25}\begin{pmatrix}9&12\\12&16\end{pmatrix},\qquad
 w=\begin{pmatrix}1\\-2\end{pmatrix}.
\]

These rational entries are interpreted exactly as complex numbers.
The required `witness_data` export contains every following assertion, with
no witness-specific admissibility or numerical identity as a hypothesis:

1. `AdmissibleFunction witnessFunction`, `f(0)=0`, and `f(2)=-2`.
   The last equality explicitly documents why this example belongs to the
   real-valued class but not the globally nonnegative-valued class.
2. `P.PosSemidef` and `Q.PosSemidef`, and the exact projection identities
   `P²=P`, `Q²=Q`. Positivity must be established for actual complex matrices.
3. The actual CFC equalities `f(P)=0`, `f(Q)=0`, and
   
   \[
   f(P+Q)=F:=\frac1{25}\begin{pmatrix}-18&-12\\-12&0\end{pmatrix}.
   \]

4. `w ≠ 0` and the exact **complex** quadratic-form identity
   
   \[
   w^*Fw=\frac65\in\mathbb C,
   \qquad 0<\frac65\in\mathbb R.
   \]

The separate generic `quadratic_cfc` export must prove

\[
 \operatorname{cfc}(t\mapsto t-t^2,A)=A-A^2
\]

for **every** Hermitian complex matrix. This binds the elementary matrix
arithmetic to the original functional calculus at `P`, `Q`, and `P+Q`.

Independent exact rational reconstruction before proofs is retained as a
small script and its output under `verification/statement-freeze/`. It should
check

\[
 P+Q=\frac1{25}\begin{pmatrix}34&12\\12&16\end{pmatrix},\quad
 (P+Q)^2=\frac1{25}\begin{pmatrix}52&24\\24&16\end{pmatrix},\quad
 Fw=\begin{pmatrix}6/25\\-12/25\end{pmatrix}.
\]

These supplemental finite computations are not a Lean proof or an assumption
permitted in the final theorem. In Lean, PSD follows from exact projection or
Gram identities, CFC follows from the generic polynomial bridge, and finite
sums and matrix identities are proved by exact algebra.

## 4. Full obstruction and final negation

The public `counterexample` theorem must quantify over **every pair** of
complex unitaries `U,V` and deny the exact target inequality at the witness.
The two CFC terms on the right are zero, so their unitary conjugates are zero.
If the inequality held, `-F` would be PSD, forcing

\[
0\le w^*(-F)w=-\frac65,
\]

contradicting the certified strictly positive real scalar. The complex order
must be converted through Mathlib's actual order semantics; a bare real part
computation does not replace a PSD proof.

Finally, `not_subadditivityConjecture : ¬ SubadditivityConjecture` must
instantiate the full original quantifiers at dimension two and the proved
admissible witness. It has no hypotheses and is a complete resolution of the
canonical target.

## 5. Computation minimization, trust, and review gate

There is no need to compute a sorted spectrum, use a root finder, split any
interval, approximate a matrix norm, or establish a generic optimization
theorem. Exact finite `2 × 2` algebra and a single scalar point certificate
for `0 < (6/5 : ℝ)` suffice. The eventual proof must use LeanCert's explicit
**kernel** trust mode for this scalar and actually consume it in the
all-unitary exclusion. Merely adding an unused LeanCert example would not
meet this plan.

The toolchain is Lean `4.33.1`, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. Dependencies are pinned in the
manifest. Matching compiled dependencies were copied with APFS cloning into
this isolated project; the user's original dependency cache is not modified.

The seven reviewed public theorem signatures in `Challenge.lean` are listed
in `comparator.json`. No definition replacement is permitted. The eventual
`Solution.lean` must give those same signatures and export only proofs whose
transitive axioms are drawn from `propext`, `Classical.choice`, and
`Quot.sound`. Implementation `sorry`, `admit`, custom axioms, native-trust
axioms, unreviewed target changes, and assumptions of any displayed numerical
identity are prohibited.

Statement elaboration is a gate, not proof verification. Two independent
reviewers must approve the exact compiled definitions, challenge, numerical
scope, and canonical/source mapping before implementation starts. A changed
mathematical statement requires renewed approval. After implementation,
two independent proof reviews and a Linux Lean4 Comparator run will check the
frozen boundary and actual kernel trust. A completed `formalization.yaml`
with all seven exports and truthful verification evidence will accompany
that later stage; this statement-only scaffold does not claim completion.

## 6. Explicit scope exclusions

The complete canonical assertion is the PSD-input, real-valued-function
statement, and its negation is fully covered. Colbrook's source additionally
gives positive definite inputs `P+I/20`, `Q+I/20`; that stronger variant is
not one of these exports and is not needed to resolve the original target.
No claim is made about the narrower globally nonnegative concave function
class, external peer review, novelty, or historical priority. The repository
status remains `Solved` until the required final verification and publication
steps are complete.
