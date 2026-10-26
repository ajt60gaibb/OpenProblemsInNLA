# Independent IE-22 lower/support source review

**Approve the exact lower-witness and fourteen support modules at commit
`7660eae85e1636de38c85a5c103ff0480f971e05`. No changes requested.**

Reviewer `/root/inventory`, 2026-10-25, author of no reviewed IE-22 proof or
statement source. I reviewed immutable Git objects, not the actively changing
worktree. Parent is `d80eaa9910ea9d6ab578839d75bd704647c99e4c`. Full Target and
universal squared upper are **not proved or approved by this checkpoint**.
`Assembly` proves conditional bridges only. Any later upper implementation or
changed baseline source needs its own review.

The exact implementation header of `near_sharp_unit_row_witness` is byte-equal
to the independently pre-approved Challenge header. Its implementation file is
SHA-256 `c155dafab5d625ca4b2cfc396342b7855ff60b7d7393784da10ebd3cf63250f4`.
The reproducible `audit_source.py` passes **105 source/preservation checks**.
It binds all fourteen source hashes and 89 lexically identified named
declarations; that lexical count is not a fresh theorem-kind/kernel audit.
The accompanying JSON binds all inspected inputs and exact declaration header.

## Source and mathematical fidelity

I read every declaration and proof in EnergyBounds, ExtremaBounds, FiniteSamples,
UniformFiniteSamples, GaussianBasics, GaussianNormBounds, GaussianCovariance,
GaussianTrimming, NormalizedGaussianRows, NormalizedGaussianApprox, LowerWitness,
SpectralProjection, TrimmingDual and Assembly, against the actual shared
RowDeletion/IE22 definitions, the full source manuscript and frozen contract.

The witness retains every original quantifier: for each θ in `(0,1)`, positive
actual Gaussian quantile a, every positive error and arbitrary natural N,R,
it produces positive n,m and an actual real unit-row matrix with `N≤n` and
`R*n≤m`. Its lower bound uses the literal normalized energy infimum; it is not
a model record, assumed probability event, generic ensemble or lower bound at
only one dimension. The moment and quantile use the actual standard Gaussian,
its true density and the original normalized interval integral.

The lower proof is a qualitative alternative to the source's quantitative
random theorem. It does not assert IE-21's explicit concentration bounds,
operator-norm ratio or all-sequence probability limit. It does not need to
identify normalized Gaussian rows with the shared UniformSphere law, since
its output is an actual finite deterministic unit-row matrix. These are
faithful implementation choices for the approved IE-22 witness endpoint.

## Probability and normalized-row safeguards

- `normalFourthMoment` and `normalSquareVariance` are definitions using actual
  Gaussian integrals/variance, not free constants or hypotheses. The proof
  establishes fourth integrability, L² of the squared coordinate, exact second
  moment one, and finite-vector norm-square mean n and variance n*K using the
  genuine finite product law. Symbolic M4/K cannot hide divergent integrals.
- `GaussianNormBounds` divides only in its positive-dimensional mean/variance/
  tail results. The general L² helper remains valid at n=0 as a totalized
  scalar expression; the witness only uses positive n. Chebyshev is applied
  to an actual L² centered norm square. The small-radius event includes zero
  and has the stated bound `4*K/n`.
- `normalizedGaussianRow` has a fixed first-coordinate unit fallback when
  g=0 and genuine norm normalization otherwise. Unit norm and original
  UnitVector/UnitRows hold pointwise for every sampled outcome. Measurability
  is proved for the actual piecewise map. There is no almost-sure unit-row
  exception hidden in the deterministic witness.
- The expectation approximation proves the exact law of a unit Euclidean
  linear functional. On norm square ratio q≥1/2 it derives the actual identity
  `observation²*q=Z²` and the difference bound `2*Z²*abs(q-1)`. Cauchy–Schwarz
  uses proved L² factors and actual fourth/norm moments. On q<1/2 both hinges
  lie in `[0,t]`; the indicator is measurable and integrable. Every integral
  subtraction/comparison has its integrability justification. No independence
  of radius and direction, CLT or unproved scalar moment is assumed.
- `FiniteSamples` samples from the actual finite `Measure.pi` probability
  measure. It proves expectation and variance of the average from marginal
  transport and `variance_sum_pi`, then Chebyshev and a finite union bound.
  The chosen natural m exceeds both the requested threshold and the genuine
  union-bound coefficient. Bad-union mass is strictly below one, so the union
  is not the entire sample space and an actual sample exists outside it.
  Independence between different tests at one row is never asserted.
- `UniformFiniteSamples` takes finite centers inside the actual compact
  Euclidean sphere. Both empirical average and expectation are separately
  L-Lipschitz, giving the safe `2*L` centered extension, hence `4*n` for these
  normalized hinges. Its radius `ε/(8*(L+1))` also handles L=0. Empty test
  families and an empty sphere do not introduce a sampling oracle.

## Lower bound, extrema and edge cases

The scalar Gaussian density proof identifies the literal TrimmedMoment with
the truncated second moment. The quantile-selector integral uses the actual
quantile mass and proved integrability; equality at t=a² holds pointwise,
including the endpoints where the hinge is zero. Moment nonnegativity and
the bound by the full second moment one are proved. No approximate quantile
or replaceable numerical constant enters the witness.

`LowerWitness` first chooses n above the requested and expectation thresholds,
with n≥1, then chooses m after n and the sphere net. Thus m can absorb every
sampling, aspect-ratio and floor requirement. It splits the error into the
population approximation, empirical approximation and floor loss. The actual
floor gives `θ*m-1≤card S`, and choosing `m>3*a²/ε` makes `a²≤m*ε/3`.
The finite trimming dual is applied to **every** retained S and **every** unit
direction x. The raw coordinate vector is transported explicitly into WithLp2
Euclidean space; norm one and the original row product are proved there.
The resulting energy lower bound holds before taking the actual infimum.

EnergyBounds constructs an actual retained set when θ≤1 and an actual unit
vector when n>0. Its energy set is nonempty and bounded below by zero.
`le_csInf` uses nonemptiness for the lower comparison; `csInf_le` uses an
explicit lower bound for candidate comparisons. Zero retained count, repeated
rows and rank deficiency are included. If ε makes the requested lower bound
negative, multiplication by the positive n/m still preserves it; no positive-
energy assumption is introduced. N=0 or R=0 still yields positive dimensions.

ExtremaBounds supplies an actual unit-row matrix for nonemptiness and a finite
`sqrt(n)` upper bound on positive dimensions. `le_csSup` for the witness uses
that genuine bounded set. Square-root transport uses nonnegative energy and
ratio; every cancellation requiring positive m or n is guarded. The more
general squared-upper-to-supremum helper is also valid without an m>0 premise
because its own bound controls the nonempty value set; this is not a use of
an empty/unbounded sSup default.

Assembly's no-smaller-constant bridge handles c'<0 separately using actual
supremum nonnegativity. For c'≥0 it chooses a positive gap to the original
square-root constant, invokes the arbitrary-N,R squared witness and obtains
a contradiction at one fixed positive upper-property tolerance. Its upper
bridge chooses squared tolerance ε² and R=0. Both bridges preserve the literal
original quantifier order; neither asserts the absent upper endpoint.

## Other proved support, reuse and scope

GaussianCovariance constructs the genuine jointly Gaussian residual and proves
independence by actual zero covariance. It separates zero variance before
division and never claims the residual has the original Y marginal. Its
Lipschitz variance/covariance bounds use actual L² integrability, fixed-constant
centering and Cauchy–Schwarz. The hinge is globally Lipschitz at its corners.
Actual Gaussian row covariances are the Euclidean Gram entries, with no row
independence premise. These are valid support facts, not the final upper bound.

SpectralProjection proves the actual ordered covariance eigenbasis, nonnegative
eigenvalues and unit-row trace. Its conditional diagonal-covariance Gram bound
uses an explicitly positive natural r+1, trace cyclicity and finite
Cauchy–Schwarz; empty dimensions cause no missing denominator case.
TrimmingDual chooses a minimizing finite row set, including k=0, and handles
ties through weak inequalities. It proves an attaining threshold and its
cardinality/energy bound, not a sorting or real-supremum oracle. The bounded
threshold helper derives its conclusion from actual total energy and θ<1;
it does not assume a favorable retained set or unattested mean-energy event.

The code uses pinned Mathlib spectral, Gaussian, integral, finite-cover,
finite-product variance and Chebyshev APIs. It does not import the historical
canonical Challenge axiom or pretend its incorrect extra convergence clause
is proved. Original mathematical credit to Matthew J. Colbrook and the
retained source history remain explicit; the new formal route and reviews
are disclosed as AI-agent work without external endorsement.

All 32 original/frozen inputs match the approved source bytes, including
historical canonical files, actual shared/frozen Targets and original manuscript.
All 217 ID/path pairs are unchanged. The commit changes no canonical project,
page, other problem proof, statement source or registry relative to its parent.
The fourteen modules have explicit LeanCert kernel mode and contain no
admission, axiom, unsafe or native-decide construct in their uncommented source.
The checkpoint README and metadata truthfully state incomplete full Target,
Solved status and no Linux/Comparator acceptance.

This is a non-author source/math approval. Verification's separate fresh
transitive replay governs kernel/theorem-kind acceptance. I have not relabeled
individual author builds as a fresh replay, authoritative Linux receipt,
canonical Comparator result or complete-problem proof. Later full-target review
must inspect the actual upper implementation, new imports and assembly diff.
