# Independent complete IE-22 source and mathematics review

**Approve the complete unchanged literal Target source and mathematics at
`353ebcfcbbcfc08184c32f391ecb6068c7d9098f`. No changes requested.**

Reviewer `/root/inventory`, 2026-10-25; author of no reviewed IE-22 proof or
statement. I froze the accepted worktree bytes before reviewing and then bound
them to this immutable commit. All **23 locked inputs**, comprising **19 proof
modules** and four statement/infrastructure/mirror files, match the commit.
The reproducible auditor passes **167 source/preservation checks**. The actual
Final import closure contains all nineteen proof modules plus the three live
shared statement/infrastructure modules. Its 108 lexically identified named
declarations are an inventory, not a fresh theorem-kind/compiler result.

This is a full **source/math** approval. Independent fresh transitive kernel
replay, separate canonical-package boundary review, actual Comparator/default
kernel/LeanCert Linux acceptance and receipt audit remain distinct gates. No
canonical promotion is approved here. The checkpoint truthfully retains Solved
status and distinguishes author kernel builds from fresh independent evidence.

## Frozen scope and exact endpoints

The prior independent lower/support approval at
`7660eae85e1636de38c85a5c103ff0480f971e05` remains valid. Thirteen of its fourteen
files are byte-unchanged. SpectralProjection adds the actual retained-subspace
construction and a heartbeat setting; I read its full new diff and underlying
reviewed basis/Gram proofs. The five added modules are GaussianUpperBounds,
GaussianUpperRealization, UpperParameters, UniversalUpper and Final. I read
every new proof and revisited the complete lower/assembly dependencies relevant
to the final theorem.

| Source | SHA-256 |
|---|---|
| SpectralProjection | `9fa8af995e6c8f1d8e61194992339bed0eadaec65643fb3d78b84232a4731158` |
| GaussianUpperBounds | `0052c55343a066bc149bdc57cb239d01e1c04c838ab00c98904f7295a225ca8a` |
| GaussianUpperRealization | `52ac80eacb0d7c2502a887640804949e4d38e822928e3bb7835fda4d162e432f` |
| UpperParameters | `1bdc86dc6828e5a3d9f0a2531bfd504d6cf385211377b2d6063f29629dbcc796` |
| UniversalUpper | `265c6c32c943f6aa2b4aba0b6ba0fcce7edcd73291fe87c73d12ec07c186d068` |
| Final | `dfd32178457de146e22c1f2a9c779622352677b5420ee0eb7079661160111719` |

All three implemented theorem headers are byte-equal to the frozen approved
Challenge headers. `uniform_squared_upper` works for every positive row count
and every actual unit-row matrix after an ambient threshold. The lower witness
produces actual finite unit-row matrices beyond arbitrary N,R. Final.target has
type exactly `NLA.Statements.IE22.Target`, with no added binders or assumptions;
it supplies both actual proved endpoints to the conditional Assembly bridges.
The literal Target, RowDeletion, Infrastructure and Reviewed mirror remain
byte-identical to published `5487945e5a72abd952b0c89915915de8cc9b3e65`.

## Actual spectral construction: no retained-subspace oracle

`ordered_covariance_basis` uses the actual PSD operator `AᵀA`, its real
orthonormal eigenbasis and eigenvalues in decreasing order. Their nonnegativity
and sum m follow from actual unit rows and the actual trace. The added
`antitone_tail_le` bounds the eigenvalue at zero-based index r by `m/(r+1)`
using the first r+1 nonnegative eigenvalues; no strict eigenvalue gaps or rank
assumption is introduced.

`exists_spectral_projection` takes only `r<n`, the actual matrix and UnitRows.
It retains columns indexed `r+j`, proves their orthonormality, constructs a
genuine Euclidean linear isometry into the original ambient space and forms
the actual projected matrix `B=A*U`. It proves `BᵀB` is diagonal with the
retained eigenvalues, each projected row norm is at most one, the retained
trace is at most m and each retained eigenvalue is at most `m/(r+1)`. Its Gram
bound follows from trace cyclicity and finite Cauchy–Schwarz:
`sum_ij |Gram_ij| ≤ m²/sqrt(r+1)`.

Every field of SpectralProjectionData is thereby discharged, including exact
original row-product equality after the isometric lift. The data structure is
an intermediate proved witness, not an extra final hypothesis. Both its row
norms and Gram entries explicitly use WithLp2 Euclidean coordinates; there is
no accidental identification of the raw function-space maximum norm with L².
Multiplicity, rank deficiency, zero retained eigenvalues and r exceeding the
matrix rank are allowed. The positive divisor r+1 is unconditional.

## Genuine Gaussian observations and probability estimates

The unchanged GaussianCovariance module constructs actual jointly Gaussian
linear pairs and identifies their covariance with the Euclidean Gram entry.
Its residual-independence theorem proves zero covariance for the actual joint
Gaussian residual. Zero variance is handled before division. The residual is
not assumed to retain the original second marginal. Integral comparisons use
proved L²/ordinary integrability. Thus the correlated-row hinge variance bound
is a proved consequence of the original Gaussian law; row independence is
never asserted.

GaussianUpperBounds correctly handles a projected row of norm zero separately.
For a nonzero row it normalizes to an actual unit vector, uses that vector's
standard-normal linear-functional law and applies pointwise variance scaling.
Contracting the scalar increases the lower hinge, so its expectation bounds
the standard-normal hinge expectation in the correct direction. The floor
ratio is at most θ. The exact quantile selector then bounds the expectation
of every nonnegative finite trimming dual by the literal TrimmedMoment.

The finite dual is actually L². Its variance is bounded by
`4*t/sqrt(r+1)` after the genuine Gram bound and positive-m cancellation. This
is the slower derivative-free route authorized by the contract; no stronger
Poincaré rate is asserted or assumed.

GaussianUpperRealization proves the actual total projected energy expectation
is at most m, then applies Markov to obtain failure probability at most 1/4
for energy exceeding 4m. The actual norm-square Chebyshev theorem bounds
failure of `||g||²≥(1-δ)*(n-r)`. For each finite mesh point, mean ≤h plus the
actual dual variance supplies a Chebyshev bound on exceeding h+δ. Finite
subadditivity combines exactly these three failure terms. Their proved sum
is strictly below one, so the bad union is not the entire probability space
and an actual Gaussian realization exists outside it. No favorable-event
existence, independence between failures, measurability shortcut, concentration
certificate or custom probability-law record is a final assumption.

## Finite mesh, parameter order and original matrix estimate

The actual finite dual is proved globally **2-Lipschitz** in its threshold.
The proof uses this conservative constant consistently: a radius-δ mesh with
dual values ≤h+δ gives every threshold ≤h+3δ. It does not silently use the
source's sharper Lipschitz constant or retain an h+2δ normalization formula.
Finite centers lie inside the compact real interval `[0,4/(1-θ)]`; there is
no assumed mesh-cardinality estimate.

`exists_upper_parameters` first chooses a positive δ<1 from ε. After any
finite mesh size M, it chooses a fixed natural deletion count r and then N.
For every n≥N it proves r<n, the actual bad-probability sum <1 and

```
n / ((1-δ)*(n-r)) * (h+3δ) ≤ h+ε   whenever 0≤h≤1.
```

The proof uses only elementary Archimedean choices and positive-denominator
algebra, with the actual finite constant K. It makes the Gaussian norm error
small by large n-r and the ratio r/(n-r) small after r is fixed. There is no
exchange of dimension limits, no r depending on the input matrix, and no
undeclared quantitative rate. The mesh is chosen before r; r,N are chosen
before **both m and A**. This is the required uniformity for all positive m,
including m<n and floor(θm)=0.

`subsingular_upper_of_good_gaussian` invokes the exact finite trimming cut on
the actual projected observations, with total energy ≤4m. The attained
threshold is at most `4/(1-θ)`, including k=0 and tied observations. The good
norm bound and r<n make `||g||` strictly positive; the proof normalizes it and
lifts through the actual isometry to an original ambient unit vector. The
retained set has the original floor cardinality, and the exact original row
products are recovered. Candidate energy bounds the genuine SubsingularSquared
infimum using its proved lower boundedness. All divisions, square-root
identities, normalization and final denominator comparisons have the needed
positive/nonnegative guards. The remaining inflation is exactly the parameter
theorem above, with `0≤TrimmedMoment≤1` supplied by actual Gaussian integrals.

## Literal Target and preserved source boundary

The lower proof and no-smaller bridge are unchanged from the independently
approved checkpoint: actual normalized finite Gaussian samples with pointwise
zero fallback, all-direction finite-net control, exact floor loss before
taking the actual infimum, genuine matrix-supremum nonemptiness/boundedness,
and a separate c'<0 case. Final passes the actual upper and lower theorems to
the exact Assembly bridges. It proves both the eventual uniform upper property
and failure for every smaller real constant, at the original Gaussian
quantile/moment, without the historical scaffold's false extra convergence
clause. The proof does not claim IE-21's stronger probability theorem.

All 32 frozen original inputs, historical canonical files and original
manuscript remain exact. The 217 permanent ID/path pairs, canonical IE-22
project/page, all statement sources and all other problem proofs are unchanged
relative to the lower checkpoint. The comment-stripped proof sources have no
admission, axiom, unsafe or native-decide construct and import no Challenge.
Every proof module explicitly selects LeanCert kernel mode. Original
mathematical credit and retained history remain intact; new formal work and
independent review are disclosed as AI-agent work without human endorsement.

The author checkpoint retains an actual successful Final invocation printing
only `propext`, `Classical.choice` and `Quot.sound`. I have not relabeled that
author build as a new independent fresh replay. The next package review must
check the separate canonical boundary, source copies, selected exports and
eventual actual CI receipts. This approval binds only the immutable complete
mathematical source described above.

## Portable auditor replay

The auditor now requires explicit `--repo` and `--output` arguments and writes
only the selected evidence directory. I reran the same immutable `353ebcfc`
audit after this driver-only change; all 167 checks pass. It now unconditionally
checks all 23 snapshot bytes, including a snapshot first created by the driver,
so the check count is independent of whether the output directory was fresh.
The first portable replay and its conditional-count diagnostic are retained
under `portability-first-replay-diagnostic/`. The result now
records the actual invocation, repository, output directory and auditor hash.
The exact initial auditor, JSON receipt and prose report are retained under
`initial-receipt-before-portable-auditor/`, with their original hashes in
`PRESERVATION.json`; no earlier receipt is silently replaced.

Example invocation from any working directory:

```
python3 /path/to/audit_source.py --repo /path/to/OpenProblemsInNLA --output /path/to/reviewer-evidence
```

This driver portability change does not alter any reviewed mathematical source,
statement, frozen input or approval scope.
