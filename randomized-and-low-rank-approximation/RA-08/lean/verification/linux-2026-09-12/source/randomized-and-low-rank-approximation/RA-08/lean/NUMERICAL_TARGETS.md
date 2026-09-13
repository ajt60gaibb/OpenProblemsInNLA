# RA-08 numerical and semantic targets, before proof implementation

This is a statement-stage plan, not a proof or a verification claim. The fourteen
`Challenge.lean` placeholders are intentional and isolated. No `Proof.lean` or
`Solution.lean` exists. Two independent approvals of this exact boundary are
required before implementation.

The source is the complete original RA-08 entry and Matthew J. Colbrook's
`03_concave_transfer_counterexamples.tex`, Theorem 3.1, at upstream
`5830ed4fb06da0659414a3deb2a40ad327aca052`. Source hashes and Git blobs are recorded
in `source-inputs.json`. The source's original mathematical attribution is
preserved. Formalization: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena, California,
USA, with AI-agent assistance. No contact email is added.

## Entire original quantified target

For every natural `n ≥ 2`, every natural `1 ≤ k < n`, every real symmetric PSD
pair `A ≥ Ahat ≥ 0`, every continuous, concave, nondecreasing, nonnegative scalar
function on `[0,∞)`, every permitted complete ordered orthonormal eigenbasis of
each matrix, and every real `ε ≥ 0`, the conjecture states

```
||A - Ahat_k||₂ ≤ (1+ε) ||A - A_k||₂
  → ||f(A) - f(Ahat)_k||₂ ≤ (1+ε) ||f(A) - f(A)_k||₂.
```

The theorem to be proved is the negation of this ENTIRE proposition. These are
actual Euclidean operator norms (`Matrix.toEuclideanCLM` over `ℝ` and `Fin n`),
not Frobenius, entrywise, or maximum-row-sum norms. Matrix order is the scoped
Mathlib PSD order, not an entrywise relation. Real PSD implies symmetry.

`OrderedSpectralData X` carries an arbitrary real orthogonal matrix `Q`, a
nonnegative antitone `Fin n` eigenvalue family, and exact reconstruction
`X = Q * diagonal lambda * Q.transpose`. No preferred matrix from an algorithm
is substituted for a spectral truncation. Existence of such data for EVERY PSD
matrix is a separate theorem obligation; so are actual column orthonormality,
eigenvector equations and CFC semantics. The conjecture quantifies over all
such data, hence all choices inside repeated eigenspaces. Index `i.val < k`
is the zero-based form of source indices `1,…,k`; `lambda k` is the first
omitted eigenvalue. The same `Q` is used for both original and function
truncations. `functionTruncation` zeros all omitted coefficients even if
`f(0)>0`; it is not `f(X_k)` and does not rotate a new plateau of `f(X)`.

Functions on the half-line are encoded by real extensions with
`ContinuousOn`, `ConcaveOn`, `MonotoneOn`, and nonnegativity on `Set.Ici 0`.
There is NO generic `f(0)=0`, strict monotonicity, differentiability, positivity,
operator monotonicity, or analyticity premise. The generic spectral CFC theorem
also states independence of extensions away from the nonnegative half-line.

## Unchanged source witness and all exact constants

Use `n=6`, `k=3`, `ε=0`, `t=1/65536`, `a=17/16`, `b=127/128`, and
`f(x)=min(x,1)`. Set

```
U = (1/9) [[1,8],[8,1],[-4,4]],       E = U Uᵀ,
F = (1/65) [[64E,8U,0],[8Uᵀ,I₂,0],[0,0,65]],
Ahat = diag(1/2,b,a,0,0,0),           A = Ahat + t F,
w = (4,3,1,0,0,0).
```

The Lean definition writes the SAME `F` with common denominator `5265`:

```
[[4160,1024,1792,72,576,0],
 [1024,4160,-1792,576,72,0],
 [1792,-1792,2048,-288,288,0],
 [72,576,-288,81,0,0],
 [576,72,288,0,81,0],
 [0,0,0,0,0,5265]] / 5265.
```

The obligations prove `Uᵀ U=I`, `F²=F`, `F≥0`, `I-F≥0`, `Ahat≥0`, `A>0`,
and `Ahat≤A`. They prove the true fourth eigenvalue of `A` is `t`, not a
prescribed list accepted as an assumption. For EVERY ordered decomposition,
`Ahat_3=Ahat`, `f(Ahat)_3=f(Ahat)`, `||A-Ahat||₂=t`, and both actual optimal
spectral tails are `t`. In this witness alone, `f(0)=0` is a proved fact.

The source also supplies an exact Nyström sketch, a stronger numerical output
ratio, nuclear-norm examples and a strictly increasing perturbation. None is a
premise or an advertised result here. The canonical RA-08 target does not
require any particular approximation algorithm; omitting the ancillary sketch
identity does not narrow the target.

## Exact polynomial minorant replacing the contour remainder argument

Set

```
c = 67108864/1896129,
h(x) = x - c x² (x-1/2)² (x-b)²,
K(A) = A (A-I/2) (A-bI),
H(A) = A - c K(A)².
```

`H(A)` is a named polynomial expression, never the definition of `f(A)`.
An actual theorem must identify `cfc h A = H(A)` and prove `H(A) ≤ cfc f A`
from scalar domination ON THE PROVED SPECTRUM of the actual matrix. It must
not assume operator monotonicity of `min(x,1)`, which is unavailable.

Required spectral location: `spectrum ℝ A ⊆ [0,1] ∪ [a,∞)`. A prospective
exact proof splits out coordinate index 2. Its diagonal entry `alpha≥a`, while
the complementary five-dimensional compression `D≤(b+t)I` with
`b+t=65025/65536<1`. If `1<lambda<a` were an actual eigenvalue with eigenvector
`(u,z)`, the two eigenvector equations would give

```
zᵀ (lambda I-D) z = (lambda-alpha) u² ≤ 0.
```

The left side is positive unless `z=0`; the other equation then forces `u=0`.
This argument and the conversion between spectrum and genuine nonzero
eigenvectors remain proof obligations. The root coordinator contributed this
compression route. No spectral-location premise occurs in the witness theorem
or the full conjecture negation.

For `0≤x≤1`, `h(x)≤x=f(x)` follows from the nonnegative square product. For
`x=a+z`, `z≥0`, the ascending coefficients of `1-h(a+z)` are exactly

```
[0, 19/17, 537952/23409, 2069504/23409,
 288428032/1896129, 227540992/1896129, 67108864/1896129].
```

Every nonconstant coefficient is positive. This is a finite polynomial
identity and positivity argument, not an interval covering or an analytic
remainder estimate. The CFC order theorem applies only after actual spectral
containment is proved.

## Three matrix-vector products and one scalar certificate

Keep `w` unnormalized: `wᵀw=26`; no square root or approximate eigensolver is
needed. Compute successively `(A-bI)w`, `(A-I/2)` times that vector, then `A`
times the result. The exact `Kw` is

```
[-119989013011/10452232411545600,
 2434900073263/167235718584729600,
 1756776553030423/41808929646182400,
 -24520157/743269860376576,
 14703909709/445961916225945600,
 0].
```

The exact targets are

```
wᵀ F w = 14912/585,
||Kw||₂² =
  1800760572753083906132034496291 /
  1019907849866242673982515970048000,
f(Ahat) = diag(1/2,b,1,0,0,0),
g = 78605142319958855341529309 /
    11432529876841442781954048000 > 0,
wᵀ (H(A)-f(Ahat)) w = 26 t (1+g).
```

Only `g>0` is planned to use an explicit kernel-only LeanCert point certificate
on a singleton domain; its retained checker term must actually feed the
Rayleigh comparison and final negation. Choose only enough precision to prove
this exact rational sign. Do not introduce an interval around matrix entries,
a perturbation interval, approximate eigenvalues or subdivisions. All matrix,
CFC, orthogonality and norm arguments are exact. The rational reconstruction
script is an independent diagnostic, not a theorem oracle.

After proving `H(A)≤f(A)`, the true operator Rayleigh bound gives
`||f(A)-f(Ahat)||₂>t`. The exact tails and source admissibility then falsify the
original implication at `ε=0`. The formal strict gap is about `0.0068755685`,
weaker than the manuscript's `334583/15769728`; the weaker gap still yields the
same complete negative answer. The original stronger ratio remains untouched
in the canonical informal resolution and is not claimed by these exports.

## Generic spectral bridges still to implement

All fourteen obligations are separately visible in `Challenge.lean`. In
particular, the universal tail theorem must use the actual antitone values and
orthogonal conjugation, while the fixed fourth-eigenvalue proof must establish
the required eigenvalue count. A possible finite-dimensional route uses
`Ahat` supported on three coordinates, `0≤F≤I`, the top three-coordinate lower
bound `Ahat≥I/2` there, and the exact sixth-coordinate eigenpair with value `t`.
Dimension/intersection or eigenbasis quadratic-form arguments must be proved;
no min-max or best-rank theorem is assumed from the manuscript.

Actual pinned APIs inspected include the sorted `eigenvalues₀_antitone`,
`eigenvectorUnitary`, `spectral_theorem`, `cfc_eq`, `cfc_mono`, `cfc_polynomial`,
`Matrix.toEuclideanCLM`, and `Matrix.l2_opNorm_diagonal`. The unsorted-reindexed
`eigenvalues` API must not silently replace the ordered family. The L2 matrix
norm lemmas require their actual scoped instances and an explicit bridge to
`spectralNorm`; default matrix norms are insufficient.

## Acceptance gates and exclusions

No implementation before two hash-bound independent statement approvals.
After implementation, require two independent final mathematical referees,
actual fresh kernel and transitive-axiom checks, all fourteen formal statement
comparisons under the pinned Linux Comparator, real sandbox/negative controls,
independent operational review and publication review. No target definitions
are replaceable holes. Only `propext`, `Classical.choice` and `Quot.sound` may
occur in completed exports; no `sorryAx`, native execution trust or custom
axiom. The author agent and any mathematical coauthor cannot count as an
independent final proof referee. Canonical status, IDs and original source
remain unchanged during this stage.
