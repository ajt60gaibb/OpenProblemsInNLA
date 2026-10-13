# RA-10 general representation and completed target

**2026-10-11: the general representing measure and the full RA-10 target are
proved locally, with universal constant 11.**
The original `AdmissibleFunction`, `TransferBound` and `Target` are unchanged.
All results below are implementation drafts awaiting independent review and
isolated Linux verification. There are no new dependencies or axioms.

## What is locally proved

All twenty-seven representation-stage modules are under
`lean-statements/NLA/Proofs/RA10/` (97 at the original completion check;
99 after moving the submission onto upstream PR #350, which supplies two
additional existing modules).

| Module | Proved scope |
| --- | --- |
| `OperatorMonotoneScalar` | Scalar monotonicity; concavity on `[0,∞)` from a two-dimensional real matrix comparison and continuity; `min(1,x) f(1) ≤ f(x) ≤ max(1,x) f(1)`; `f(1)=0` implies the function vanishes on the relevant domain. |
| `OperatorMonotoneNormalization` | Nonnegative scaling and subtraction of `f(0)` preserve admissibility; a nonzero admissible function normalizes at one. |
| `SpectralFunctionOperations` | Congruence on the supplied spectrum, addition, scaling and constant functions for the frozen spectral sums. |
| `CompactLoewnerKernel` | Harmonic atoms with both endpoints, their ridge formula, positivity, measurable dependence on the parameter, and uniform bound/integrability for finite measures. |
| `LoewnerAtomTransfer` | Constant-11 transfer for every harmonic atom, using the existing unconditional ridge theorem and exact constant/linear cases. |
| `SpectralIntegral` | Entrywise spectral integration and a general nuclear integral bound derived from trace duality. |
| `CompactLoewnerTransfer` | Constant-11 transfer for every represented function, and an explicitly conditional reduction of the frozen target to measure existence. |
| `CompactLoewnerNormalization` | Concrete atomic representations, closure under positive scaling/addition, total mass equal to `f(1)`, and reduction to normalized admissible functions. |
| `CompactLoewnerEndpoint` | A representation on positive arguments extends to zero by dominated convergence; the final conditional reduction needs existence only on the open half-line. |
| `LoewnerMeasureConstruction` | Constructs a probability measure for a profile in the closed convex hull of harmonic atoms, using compactness of probability measures; includes pointwise limits of convex combinations. |
| `OperatorMonotoneCompactness` | Convexity and compactness of the normalized positive-profile closure; its Krein–Milman equality; representation and the frozen target conditional on extreme-point classification. |
| `OperatorMonotoneClosure` | The closure retains normalization, strict positivity, scalar concavity, continuity on the open half-line and the frozen real spectral-sum matrix order for strictly positive spectra. |
| `OperatorMonotonePositiveApproximation` | Normalized positive shifts identify the compact class with continuous positive normalized operator-monotone functions on the open half-line. |
| `LoewnerAtomMonotonicity` | Real matrix inverse-order reversal; all-size ridge and harmonic-atom monotonicity; every harmonic atom belongs to the frozen admissible class. |
| `OperatorMonotonePositiveCone` | Growth bounds, vanishing when the value at one is zero, and normalization for the nonnegative operator-monotone cone on `(0,∞)`. |
| `HarmonicExtremePoints` | Unconditional extremality of the constant and linear atoms; cone decompositions of an extreme profile are proportional; the harmonic formula follows **given a valid Hansen split**. |
| `HansenSplit` | Both canonical pieces are continuous, nonnegative and operator monotone; their sum and splitting identity give the unconditional harmonic extreme-point classification. |
| `SpectralFunctionalCalculus` | Spectral basis independence without ordering, positivity or simplicity assumptions; agreement with Mathlib's functional calculus; the frozen matrix-monotonicity contract implies CFC monotonicity on positive-definite matrices. |
| `MatrixFunctionalCalculus` | Reindexing, diagonal matrices, orthogonal conjugation and block direct sums; monotonicity for matrices indexed by any finite type. |
| `OperatorMonotoneCompression` | Exact Schur-complement comparison, the positive-shift limit, and the general positive-definite compression inequality. |
| `OperatorMonotoneConcavity` | All-size matrix concavity from monotonicity and continuity on the open half-line, hence unconditionally for profiles in the compact class. |
| `OperatorMonotoneDifferentiability` | A fixed rank-one two-dimensional comparison forces equality of the one-sided derivatives; every compact-class profile is differentiable at every positive argument. |
| `MatrixDividedDifference` | Matrix-variable CFC continuity, exact column divided-difference identities and the first derivative at a diagonal matrix, allowing repeated eigenvalues. |
| `OperatorMonotoneKraus` | Arrowhead compression gives the negative-semidefinite second divided-difference matrix without assuming a second scalar derivative. |
| `MatrixLoewnerCriterion` | Nonnegative Loewner matrices imply matrix monotonicity, allowing one exceptional scalar argument; polynomial roots control spectral crossings and scalar shifts remove the temporary regularity condition. |
| `BendatSherman` | The divided difference of a differentiable operator-monotone function on `(0,∞)` is operator antitone; inversion and negation preserve operator monotonicity together. |
| `OperatorMonotoneRepresentation` | Probability representation of every compact-class profile; finite-measure representation of every frozen admissible function; unconditional `TransferBound 11` and `Target`. |

No invertibility, spectral gap, positive-tail or commutation premise is added
to the transfer theorem. Its inputs keep both supplied spectral bases.
In particular, a selected zero eigenvalue still contributes the constant atom.

## Compact formulation and simplifications

For `t ∈ [0,1]`, define

```text
h_t(x) = 1                              if t = 0,
         x / (t + (1-t)x)               otherwise.
```

Thus `h_0 = 1`, `h_1(x) = x`, and for `0<t<1`,
`h_t(x) = (1-t)⁻¹ ridgeAtom(t/(1-t), x)`.
The internal representation predicate asks for a finite positive measure `μ`
with `f(x) = ∫ h_t(x) dμ(t)` for every `x ≥ 0`.

The checked bound `0 ≤ h_t(x) ≤ max(1,x)` provides absolute convergence at
every eigenvalue. Consequently the transfer proof works directly with this
finite measure: it needs neither an infinite-measure change of variables nor
separate weighted-integrability machinery.

The nuclear integral inequality uses the existing orthogonal trace maximizer
for the integrated matrix and applies the pointwise trace upper bound under
the integral. This avoids creating a second matrix norm. The exact spectral
tail formula then closes the estimate. Because every atom theorem already
covers zero tail, the integrated proof covers it as well.

## Measure construction now checked

Write `X = (0,∞)` and let `h_t` denote the harmonic atom above, restricted to `X`.
The constructor proves

```text
f ∈ closure(convexHull {h_t | t ∈ [0,1]})
  ⇒ ∃ μ : ProbabilityMeasure [0,1], ∀ x ∈ X, f(x) = ∫ h_t(x) dμ(t).
```

The closure is for pointwise convergence, and the conclusion supplies one
measure for all arguments. This is an existence proof by compactness, not an
algorithm for computing a density. It does not assume a representing measure.

For fixed `x > 0`, the kernel is continuous in `t`, including both endpoints.
The map from a probability measure to its integral profile is therefore
continuous. Its range is compact and closed because `[0,1]` is compact.
Explicit positive mixtures make this range convex, and Dirac measures supply
each atom. It consequently contains their closed convex hull. This reuses
Mathlib's measure compactness and integration continuity without separately
building a positive linear functional or invoking Riesz–Markov again.

Let `P` be the closure of profiles of the frozen admissible functions with
`f(1)=1`, restricted to `X`. The checked growth bounds place `P` in a compact
product of real intervals; it is closed and convex. Mathlib's Krein–Milman
theorem now gives

```text
P = closure(convexHull (extremePoints P)).
```

The closure has been checked carefully: its members retain normalization,
strict positivity, scalar concavity, continuity on `X`, and matrix monotonicity
for every real matrix size with strictly positive spectra. Conversely, any
continuous positive normalized function with that matrix monotonicity lies in
`P`: the admissible functions `f(x+ε)/f(1+ε)` converge to it for `ε ↓ 0`.
Thus the compact class is identified intrinsically, with no extra assumption
about continuous extension to zero. This limit is approximation by shifted
operator-monotone functions. The extreme-point classification below then
places every such profile in the closed convex hull of the harmonic atoms.

## Extreme points and final signatures

For `g ∈ P`, let `f` be its positive-domain extension and set

```text
u(x) = x · dslope(f,1,x),       v(x) = 1 − dslope(f,1,x).
```

Away from one these are `x(f(x)−1)/(x−1)` and `(x−f(x))/(x−1)`.
The proofs establish `u,v ≥ 0`, `u+v=g`,
`u(x)(x−1)=x(g(x)−1)` and matrix monotonicity of both pieces. Thus they
belong to the nonnegative operator-monotone cone, and extremality gives
`u(x)=u(1)g(x)`. The algebra then
yields `g(x)=x/(u(1)+(1−u(1))x)` with `0≤u(1)≤1`.
The zero-weight cases follow from growth bounds, avoiding separate strict
derivative bounds and derivative-zero rigidity lemmas.

The completed public signatures, in `NLA.Proofs.RA10`, are:

```lean
extreme_eq_loewnerProfile
  (hg : g ∈ normalizedAdmissibleCompactClass.extremePoints ℝ) :
  ∃ t : LoewnerParameter, g = loewnerProfile t

admissibleFunction_hasCompactLoewnerRepresentation
  (hf : AdmissibleFunction f) : HasCompactLoewnerRepresentation f

transferBound_eleven : TransferBound 11
ra10_target : NLA.Statements.RA10.Target
```

The final theorem has no representation, differentiability, matrix-concavity
or Hansen-split premise. `normalizedProfile_probabilityRepresentation` also
constructs one probability measure representing every positive argument of
each profile in `P`. Normalization and the zero-function case give a finite
measure for every admissible function; dominated convergence handles zero.

## Analytic prerequisites now checked

The bridge to functional calculus first proves that equal spectral matrices
give equal function matrices for any scalar function. If the two bases are
`Q,R`, their overlap `T=QᵀR` satisfies `(aᵢ-bⱼ)Tᵢⱼ=0`, hence
`(f(aᵢ)-f(bⱼ))Tᵢⱼ=0`. This handles repeated eigenvalues directly.

For a positive-definite block matrix `X=[[A,B],[Bᵀ,C]]`, the comparison

```text
X ≤ diag(A + εI, C + ε⁻¹ BᵀB),       ε > 0
```

follows from Mathlib's Schur-complement theorem with zero residual.
Apply monotonicity, take the upper-left block, and let `ε ↓ 0` to obtain
`[f(X)]₁₁ ≤ f(A)`. Orthogonal block rotation then gives matrix concavity.
No estimate on the norm of `B` or new external Jensen dependency is needed.

Differentiability has a separate short route. For `c>2ε>0`, compare

```text
A = cI + ε [[1/4,-3/4],[-3/4,-7/4]],
B = cI + ε [[1,0],[0,-1]].
```

Their difference is `(3ε/4)[[1,1],[1,1]] ≥ 0`. Test `f(B)-f(A)` at
`(1,-1)` and use the explicit eigenbasis of `A`. The checked inequality is

```text
f(c+ε) + f(c-ε) - (8/5)f(c+ε/2) - (2/5)f(c-2ε) ≥ 0.
```

Mathlib provides the one-sided derivatives from scalar concavity. After
division by `ε`, the limit is `(f′₊(c)-f′₋(c))/5 ≥ 0`; concavity gives the
reverse inequality. The derivatives coincide. This argument uses neither
the measure representation nor the Hansen split, so there is no circularity.

## Divided differences: the final analytic step

For diagonal `D=diag(a)` and Hermitian `B`, the exact identity

```text
[f(B)-f(D)]_ij = [dslope(f,a_j)(B) (B-D)]_ij
```

follows by applying CFC to `(x-a_j) dslope(f,a_j,x)=f(x)-f(a_j)`.
Mathlib's CFC continuity in the matrix variable gives the first derivative
along `D+tH`, with entries `dslope(f,a_j,a_i) H_ij`. No eigenvector
differentiability, simple-spectrum assumption or polynomial approximation
library is needed.

Apply the identity twice to `X(t)=diag(a,c)+tH`, where `H` has zero diagonal
blocks and ones in its off-diagonal column and row. Compression gives
`f(diag(a))-[f(X(t))]₁₁ ≥ 0`. Divide by `t²` and pass to the limit. This
proves that the Loewner matrix of `-dslope(f,c)` is positive semidefinite
whenever the nodes differ from `c`; nodes may coincide with each other.
Only first differentiability of `f` is used.

For the converse Loewner criterion, Schur's Hadamard-product theorem makes
the directional quadratic-form derivative nonnegative. Along an affine
matrix path, hitting `c` in the spectrum is a zero of a determinant polynomial.
Its finitely many zeros are handled by continuity and an interval-splitting
mean-value argument. Small scalar shifts remove the auxiliary condition at
the initial matrix. Thus the final theorem also covers spectra containing `c`.

This proves the Bendat–Sherman implication needed here: `-dslope(f,1)` is
operator monotone, so `v` is. For the other piece, `h(x)=-f(1/x)` is operator
monotone by inverse-order reversal. Apply the same theorem to `h` and invert
again; the identity `dslope(h,1,1/x)=x dslope(f,1,x)` gives `u`.
The filled-in value at one is checked by the ordinary chain rule. This avoids
a separate operator-perspective theorem or a second-derivative regularization.

## Reuse audit

The pinned Mathlib search found power-function integral representations in
`Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/IntegralRepresentation.lean`,
but no general positive operator-monotone representation. The public
[QICLean coverage tracker](https://github.com/LionSR/QICLean/issues/2) and
[Jensen work](https://github.com/LionSR/QICLean/issues/135) distinguish the
general gap from their special-function work. The
[QIQT-H index](https://qiqt.org/formalization/) lists specific operator
inequalities, without supplying the general existence theorem needed here.
These were searches for reusable work, not independent audits of those projects.

[Hansen's paper](https://arxiv.org/html/1112.0098v2) offers a route avoiding
complex analytic continuation. Its scalar concavity argument is now implemented
using the frozen continuity hypothesis. Matrix concavity and regularity are
now implemented too, together with the required divided-difference
monotonicity and extreme-point arguments. The extremal
algebra uses unnormalized pieces to retain the zero-weight endpoints. The paper
uses Krein–Milman and compactness of probability measures to construct the measure;
that last construction is now implemented using pinned Mathlib:

- `Analysis/Convex/KreinMilman.lean`: `closure_convexHull_extremePoints`.
- `MeasureTheory/Measure/Prokhorov.lean`: compactness of `ProbabilityMeasure E`
  for compact `E` under the file's stated hypotheses.
- `MeasureTheory/Measure/ProbabilityMeasure.lean`: continuity of integration
  against bounded continuous test functions in the weak topology.
- `Analysis/Convex/FunctionTopology.lean`: `isClosed_setOfPred_concaveOn`.
- `Analysis/Convex/Continuous.lean`: continuity of a concave real function on an open convex set.
- `Analysis/Calculus/DSlope.lean`: the filled-in divided difference, its algebraic
  identity and its exact continuity/differentiability criterion.
- `Analysis/Matrix/HermitianFunctionalCalculus.lean`: finite spectral CFC and
  the bridge to the generic functional calculus API.
- `LinearAlgebra/Matrix/PosDef.lean`: the Schur-complement equivalence and
  preservation of positivity under congruence and principal submatrices.
- `Analysis/Convex/Deriv.lean`: existence and order of one-sided derivatives.
- `Analysis/Calculus/Deriv/Slope.lean`: slope-limit criteria for derivatives.
- `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Continuity.lean`:
  continuity in the matrix variable, using its existing L2 operator norm instance.
- `Analysis/Matrix/Order.lean`: positivity of Hadamard products.
- `Analysis/Calculus/Deriv/MeanValue.lean`: monotonicity from nonnegative derivatives.
- `Algebra/Polynomial/Roots.lean`: finiteness of exceptional spectral crossings.
- `MeasureTheory/Integral/DominatedConvergence.lean`: used for the endpoint proof.

An important constraint respected by the compactness argument: continuity at
zero is not preserved by arbitrary pointwise limits of normalized ridge
functions. Work on strictly positive arguments first; the checked endpoint
lemma then restores zero using the original function's continuity. Do not
assume the entire closed-half-line admissible class is pointwise compact.

The later reuse search also found
[Lean-LiebConcavity](https://github.com/eiKeViN/Lean-LiebConcavity), whose README
reports a general operator-Jensen implementation and lists its remaining
power-function admissions separately. This is a potential source for a later
Jensen/compression bridge, not a checked replacement for the needed
divided-difference theorem. The required compression bridge has been
implemented directly with pinned Mathlib. No code or dependency was imported
from that project. A further targeted web search for Lean Bendat–Sherman and
divided-difference proofs did not identify an implementation to reuse; this
is not a claim of an exhaustive search.
The final route was checked against the original
[Bendat–Sherman paper](https://www.ams.org/journals/tran/1955-079-01/S0002-9947-1955-0082655-4/S0002-9947-1955-0082655-4.pdf)
and [Hansen's account](https://arxiv.org/html/1112.0098v2). The local proof
uses the finite-matrix compression and exact identities above; neither paper
nor any external theorem is introduced as an axiom.

## Local verification

```bash
lake build NLA.Proofs.RA10.OperatorMonotoneRepresentation NLA.Proofs.RA10.OperatorMonotoneConcavity
```

This passed locally with 3044 jobs, including the complete representation and
ridge-transfer dependency chain.
All new exported theorems have `#assert_trust kernel`; the unconditional
representation, transfer bound and target report only `propext`, `Classical.choice`
and `Quot.sound`. No proof module was added to the reviewed aggregate.

The earlier build log and hashes remain in `verification/2026-10-11-representation/`.
The measure-construction build is in `verification/2026-10-11-measure-construction/`.
The earlier extremal-argument build is in
`verification/2026-10-11-harmonic-extreme/`; the earlier regularity build is in
`verification/2026-10-11-analytic-prerequisites/`. The final build and hashes
are in `verification/2026-10-11-complete/`. Dependency pins remain Lean 4.33.1,
Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`.
The frozen statement SHA-256 remains
`dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82`.

Successful local compilation is not independent review or the repository's
authoritative non-root Linux Comparator verification. Both remain outstanding.
Neither Docker nor Podman was available in this macOS session. No canonical
status or reviewed-aggregate import was changed. See [the review guide](README.md)
for the draft PR scope and reproduction instructions.
