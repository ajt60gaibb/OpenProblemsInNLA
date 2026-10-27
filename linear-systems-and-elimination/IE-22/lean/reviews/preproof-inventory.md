# Independent IE-22 pre-proof review

**Approve the frozen three signatures and mathematical route. No changes
requested.** Reviewer `/root/inventory`, 2026-10-23; author of no IE-22 proof or
statement source. This approval precedes implementation and applies only to:

- Challenge: `bd20cbb3d4495ff312192ab29fe7722463c8b74861f0a00ae83dd9b98ed4ec79`
- Contract: `7e7224aabf0514c1a66cf74e0892b9a9e5a979dbb1b85862d4abfa3736ad94fd`
- Input lock: `26fe6dce1658d183be3629094b83ea58e3c11aeb721566c4dd2711372906aad5`

All **32 frozen inputs** independently match their bytes, sizes and SHA-256
hashes in actual published Git object
`5487945e5a72abd952b0c89915915de8cc9b3e65`. I read the complete exact shared and
reviewed Target, RowDeletion definitions, original canonical statement,
numerical specification, complete IE-21/22 TeX manuscript §§1–7, source review,
and the historical definitions/Challenge/Solution scope. IDs and originals are
preserved. No existing proof or statement was edited for this review.

## Exact statement correspondence

`uniform_squared_upper` retains every real unit-row matrix and every positive
row count. It chooses only an ambient threshold after the requested squared
error, before both dimensions and the matrix. Its squared normalized quantity
is exactly `(n/m)*SubsingularSquared`; no aspect-ratio, rank, incoherence,
genericity, independent-row or probability assumption restricts this universal
upper theorem. It is stronger than the original eventual uniform upper clause,
and matches the source's deterministic projection theorem qualitatively.

`near_sharp_unit_row_witness` produces actual finite positive dimensions and an
actual real matrix with unit rows, beyond arbitrary **both** dimension and
aspect-ratio thresholds. Its witness, not an assumed ensemble certificate,
provides the needed lower bound for the original matrix supremum. Choosing a
sufficiently large row count after a fixed sufficiently large dimension is
legitimate for this statement. It does not pretend to prove IE-21's explicit
concentration theorem or every high-aspect-ratio sequence.

`target` has exactly `NLA.Statements.IE22.Target` as its type and no extra
parameters. The shared Target contains both the exact eventual uniform upper
property and failure of that property for **each** strictly smaller real
constant, including negative constants. The Gaussian quantile is the actual
standard-normal measure of `Icc (-a) a`; the moment is the specified normalized
interval integral. No unconstrained law, quantile, moment or extremizer record
is introduced. Positivity of `a` and `0<θ<1` make the interval orientation and
quantile domain correct. Gaussian atomlessness reconciles closed endpoints
with the trimming selector. The actual density gives the usual unique finite
positive quantile for each such θ; the contract is not concealing an impossible
quantile predicate.

The historical canonical Challenge's separate `SupremumConverges` drops
`n→∞` and is false already for `n=1`. It is correctly preserved as historical
source and excluded from the new imports and acceptance boundary. Its axiom is
not a reuse opportunity. Removing that false extension from a new separately
reviewed boundary preserves the original mathematical problem; it does not
weaken the unchanged shared Target.

## Universal upper route

The covariance alternative is mathematically sound. For centered jointly
Gaussian X,Y with `σ²=Var(X)>0`, put `c=Cov(X,Y)/σ²` and `Y'=Y-cX`.
The actual joint Gaussian zero-covariance theorem proves independence of X,Y'.
Consequently

```
Cov(f(X),g(Y)) = Cov(f(X),g(Y)-g(Y')),
sqrt(Var(f(X))) ≤ Lip(f)*σ,
sqrt(Var(g(Y)-g(Y'))) ≤ Lip(g)*|c|*σ.
```

Cauchy–Schwarz yields the proposed absolute covariance bound
`Lip(f)*Lip(g)*|Cov(X,Y)|`. The variance bound uses the second moment about
the fixed constant `f(E X)`, not the false identity `E(f(X))=f(E X)`.
There is no requirement that Y' have Y's marginal law. If `Var(X)=0`, X is
almost surely constant and its covariance with an integrable transformed Y
vanishes; that case must be separated before division. The inspected pinned
Mathlib supplies `HasGaussianLaw.indepFun_of_covariance_eq_zero` for genuinely
joint Gaussian pairs; constructing that actual joint law is an obligation,
not an additional Challenge premise.

For `t≥0`, `(t-z²)+` is globally `2*sqrt(t)` Lipschitz, including the constant
zero function at `t=0`. Removing the top r covariance directions gives
`trace(BᵀB)≤m`, operator square at most `m/(r+1)` and projected row norms at
most one. For its actual Gram matrix G, finite Cauchy–Schwarz gives

```
sum_ij |G_ij| ≤ m * sqrt(sum_ij G_ij²)
             ≤ m²/sqrt(r+1).
```

The resulting hinge-average variance is at most `4*t/sqrt(r+1)`, which tends
to zero. This slower bound supports fixed finite threshold meshes and a
qualitative theorem; it does not justify the source's stronger Poincaré rate.
No projected-row independence is used.

For every threshold t, each projected scalar has variance at most one, so the
same-standard-normal scaling coupling gives the needed hinge expectation
inequality. The selector of the actual interval `[-a,a]` proves
`θ*t-E(t-Z²)+≤h`, with equality at `t=a²`; no expectation of a random minimum
is interchanged. On the event `||Bg||²/m≤4`, the kth order statistic is at most
`4/(1-θ)`, since `m-k+1≥(1-θ)m`. Markov leaves failure probability at most
1/4. A finite mesh plus the covariance bound controls the actual trimming
maximum on this interval; Gaussian norm concentration supplies a nonzero
realization for normalization. Choosing r large but fixed after θ/error,
then n sufficiently larger than r, makes both remaining failure probabilities
small and `n/(n-r)` close to one. The thresholds stay independent of m,A.

## Finite lower construction

The normalized-Gaussian route avoids any need to assume a spherical law or
independence between Gaussian radius and direction. For a genuine unit x,
`Z=<g,x>` has standard-normal law and `W=||g||²/n` has mean one. With the actual
finite standard-normal fourth moment M4 and squared-coordinate variance K,
`E Z⁴=M4` and `Var(W)=K/n`. On `W≥1/2`, actual normalized-row square
`Y=Z²/W` has hinge difference bounded by `2*Z²*|W-1|`; its expectation is at
most `2*sqrt(M4*K/n)`. On the complementary event both hinges lie in `[0,t]`,
and Chebyshev gives contribution at most `4*t*K/n`. These vanish uniformly
over actual unit x. The exact constants M4=3 and K=2 are unnecessary for the
frozen qualitative statements, but their finiteness and the mean/variance
identities must be proved for the genuine product Gaussian law.

At `g=0`, a fixed first-coordinate unit-vector fallback ensures every sampled
row is unit, not merely almost surely unit. Dimensions can be chosen positive
and sufficiently large before sampling. Applying that measurable row map to
independent Gaussian rows preserves their independence. This needs no uniform-
sphere identification because the output theorem is an actual finite-matrix
existence statement.

For fixed n the sphere is compact. A finite net controls all unit directions:
`x↦(a²-n*<row,x>²)+` is `2*n` Lipschitz on the unit sphere. The expectation has
the same bound, so extending an empirical-minus-expectation estimate can use
`4*n` times the net radius. Choosing a finer net absorbs this factor. Bounded
independent-row Chebyshev and a finite union bound yield an event of positive
probability for sufficiently large m. The trimming dual at `t=a²`, valid for
every subset and unit direction, then bounds the actual infimum from below.
The only floor loss is at most `a²/m`. There is no uniform-in-n sample-size
claim: m may be made arbitrarily large after choosing n, including beyond
`R*n` and any rank/cardinality requirement needed for a positive lower bound.

## Degenerate cases and literal assembly

- `n=0` and `m=0` are excluded exactly where actual unit spheres/division are
  used. The universal upper may choose N large enough for `r<n`; it does not
  add a new lower-dimensional assumption. The lower witness can choose
  `n≥max(2,N)` and positive m even when N or R is zero.
- From `0<θ<1` and `m>0`, `0≤floor(θm)≤m`, indeed `<m`. Finite retained sets
  exist. With positive n the unit sphere is nonempty. If k=0 the actual
  retained energy and its infimum are zero; repeated rows and rank-deficient
  submatrices remain in the universal domain.
- Every energy is nonnegative and at most k for unit rows/unit vectors.
  Thus the actual energy set is nonempty and bounded below, and the matrix
  supremum set is nonempty and bounded above by `sqrt(n)`. Lower/upper
  comparisons must establish these facts before applying real sInf/sSup
  lemmas. Compact-minimum attainment may be proved, but no empty-set default
  is an admissible shortcut.
- The moment is nonnegative. For positive dimensions the square of the exact
  original product `sqrt(n/m)*sqrt(SubsingularSquared)` is the squared
  normalized energy. An upper squared tolerance such as ε² gives the requested
  upper tolerance ε without changing the square-root placement. The stronger
  upper can take R=0 or R=1 in the literal eventual property.
- For `c'<0`, nonnegativity and nonemptiness of the actual matrix supremum
  already refute the upper property at tolerance `-c'/2`. For `0≤c'<sqrt(h)`,
  choose a positive intermediate b between c' and sqrt(h), then a squared
  tolerance with `h-η>b²`. The lower witness exists beyond **any** N,R and
  makes the actual supremum greater than b. This contradicts the putative
  upper property at a single sufficiently small positive tolerance. This is
  the exact negated quantifier order; no lower bound at all tolerances or
  false `n=1` limit is needed.

## Independent scaffold evidence and limits

I ran `check_scaffold.py` into a separate fresh private output directory
`/private/tmp/nla-ie22-inventory-preproof-oct23`. All **four** commands passed:
RowDeletion, Infrastructure, IE22 and Challenge. The only Challenge warnings
are its three deliberate placeholders. The compiler is official Lean 4.33.1,
commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, using pinned dependency caches
and new private project objects. A separate negative compiler invocation
attempts LeanCert kernel acceptance of each of the three Challenge constants;
all three are required to reject with sorryAx. `check_inventory_preproof.py`
binds the exact 32 inputs, packet, compiler, dependency revisions, positive
logs and negative control. Persistent evidence is under
`verification/inventory-preproof/`; result is `PRE_REVIEW_INVENTORY.json`.

This is approval to implement the frozen endpoints, not an assertion that
their placeholder bodies prove anything. No implementation, full transitive
axiom audit, canonical Comparator, Linux acceptance or status promotion is
claimed. A canonical project still needs its separate exact boundary review
and final evidence gates; current canonical status remains Solved.
