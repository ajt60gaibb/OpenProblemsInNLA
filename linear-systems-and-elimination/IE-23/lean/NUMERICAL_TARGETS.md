# IE-23: exact statement plan before proofs

Stage: **statement-only; no proof implementation**. These statements must be
approved by two independent referees before implementation. The full retained
canonical conjecture is the input to the final negation, not a restricted
replacement. No default of a totalized inverse or supremum may create the
counterexample.

## Original universal target

For every `1 ≤ m < n`, every complex `m×n` matrix A of actual rank m, every
finite real `p>2`, and every complex right inverse X distinct from
`A†=A* (AA*)⁻¹`, is its direct induced `p→2` norm strictly larger than that of
A†? The denominator is exactly `(Σ |yᵢ|ᵖ)^(1/p)`, the numerator is the true
Euclidean norm of `Xy`, and the supremum includes every nonzero complex input
vector. The finite-real parameter excludes both p=2 and p=∞ exactly as the
canonical statement does. No assertion about the different objective `‖XA‖`
is included.

The definition `RightInverseUniqueConjecture` contains every original
quantifier. The final export proves its logical negation. The source theorem
gives a stronger all-p family; only one admissible value is required to refute
the universal conjecture.

## Exact data and obligations

Specialize to m=2, n=3, p=4 and use the source matrices, unchanged:

```
A = [[1,1,0], [1,0,1]],
B = (1/3) [[1,1], [2,-1], [-1,2]],
X = [[0,0], [1,0], [0,1]],
z = (1,-1).
```

Let `G=[[2,1],[1,2]]`, `Ginv=(1/3)[[2,-1],[-1,2]]`, and
`c=√(√2)`. All scalar square roots here are the actual nonnegative real square
root. Required numerical identities are `c>0`, `c²=√2`, `c⁴=2`, and
`c=2^(1/2−1/4)`, with genuine real exponentiation in the last expression.

The eight Challenge contracts require the following.

1. **Generic supremum semantics.** On every original input domain, prove
   positivity of the denominator at every nonzero input, nonempty and bounded
   ratio set, the actual least-upper-bound property of its `sSup`, nonnegativity,
   and `‖Xy‖₂ ≤ ‖X‖ₚ→₂ ‖y‖ₚ` for every y, including zero. These facts are
   conclusions, never extra assumptions in the canonical conjecture.
2. **Genuine matrix certificates.** Prove actual rank(A)=2, `AA*=G`, invertibility
   of G, actual `G⁻¹=Ginv`, actual `A†=B`, `AB=AX=I₂`, `B≠X`, `B*B=Ginv`, and
   `X*X=I₂`. Both products certifying Ginv can be checked over the rationals;
   the bridge to Mathlib's matrix inverse and rank must then be proved.
3. **Universal norm control.** Prove the scalar identities for c and, for every
   complex y=(u,v),
   `‖y‖₂²=|u|²+|v|²`, `‖y‖₄⁴=|u|⁴+|v|⁴`, and `‖y‖₂≤c‖y‖₄`.
   Set a=|u|, b=|v|. The only polynomial inequality needed is
   `(a²+b²)²≤2(a⁴+b⁴)`, whose difference is `(a²−b²)²`. Positivity and
   monotonicity of actual roots/powers must connect this to the unsquared norm
   inequality; an inequality on unnamed surrogate powers is insufficient.
4. **Actual action identities.** For all complex y,
   `‖By‖₂² + |u+v|²/3 = ‖y‖₂²` and `‖Xy‖₂=‖y‖₂`.
   For *every* complex right inverse Y of A,
   `‖Yz‖₂²=2+3|(Yz)₀|²`.
   The last equation follows from the actual right-inverse equations, which give
   `Yz=(t,1−t,−1−t)`. It is not restricted to a guessed family of competitors.
5. **Attainment.** Prove `z≠0`, `‖z‖₄=c`, `‖Bz‖₂=‖Xz‖₂=√2`, and both actual
   norm ratios equal c. Thus the universal upper bounds are attained.
6. **Exact supremum values.** Prove `‖B‖₄→₂=‖X‖₄→₂=c` using the actual
   nonzero-input suprema and the proved semantic obligations above.
7. **Global minimality and attainment of the minimum.** Prove that both B and X
   minimize the norm over all complex right inverses of A. Equivalently, for
   every such Y the ratio at z is at least c; the feasible value set has
   `IsLeast ... c`. No full classification of all minimizing Y is necessary.
8. **Complete counterexample.** Discharge the original dimension/rank/p/right-
   inverse/distinctness hypotheses with these facts and prove
   `¬ RightInverseUniqueConjecture`.

## Computation and trust plan

Every certificate is exact rational algebra, a sum of squares, finite sums, or
an analytic property of the actual norm, real power, inverse, and supremum.
No eigenvalue enclosure, parameter grid, subdivision, or approximate norm
computation is needed. The nontrivial continuum is the set of all input vectors
and all competing complex right inverses; universal Lean proofs cover it.

The supplementary reconstruction uses rational arithmetic and exact polynomial
identities as diagnostics. Its output is not an oracle and will not enter Lean
as an axiom. LeanCert is planned in the same explicit **kernel trust audit**
mode approved for the campaign's other pure exact proofs: inspect actual
declarations and require only `propext`, `Classical.choice`, and `Quot.sound`.
There is no useful interval subproblem here and no artificial interval
certificate is introduced merely to satisfy a tool count. This exact-only
scope is itself part of the independent statement review.

`Solution` is registered from the start but absent at this stage;
`defaultTargets=["Challenge"]` remains deliberate. The eight `sorry`
placeholders are confined to Challenge. A future Solution must import only
completed proof modules, export every reviewed signature, and have no
`sorry`, custom axiom, or native execution trust. It will then undergo two
independent final proof reviews and the actual Linux kernel/Comparator checks.

## Attribution and limits

Matthew J. Colbrook retains credit for the analytic IE-23 resolution. The
underlying rational example is attributed in both source and formalization to
Dokmanić and Gribonval, Example 4.1. George Stepaniants is the AI-assisted
formalization author, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA. No contact email
is added. This formalization claims the complete negative canonical answer and
the stated p=4 global-minimizer certificate; it does not claim the source's
all-p formulas, entire minimizer disk/interval, higher-dimensional family,
smallest-dimension classification, separate product objective, or novelty.
