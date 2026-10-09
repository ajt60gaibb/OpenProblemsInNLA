# TR-07 Lean proof guide

This project formalizes the **entire original TR-07 asymptotic theorem**.
The exported declaration is `NLA.TR07.random_column_subsets : SolvesTR07`.
For every fixed sparsity `s >= 2`, finite aspect limit `C >= 1`, and
admissible deterministic sequence of signed sparse matrices, the probability
that a uniformly selected column subset has smallest singular value above
any fixed positive threshold tends to zero. Arbitrary signs, repeated
column values, and unrestricted support intersections are included.

[NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) records the original source,
its fixed revision and hashes, and all quantifiers and conventions.
[Definitions.lean](NLA/TR07/Definitions.lean) defines the literal matrix
product, Euclidean unit-sphere infimum, and exact uniform subset cardinality
ratio. Sparsity is required eventually, allowing the irrelevant small
row dimensions below `s`. Positivity and divergence of the sample size are
proved from the ratio assumptions.

## Proof route

The internal deletion deficiency is the minimum number of columns whose
removal leaves a restriction bounded below by `eta`. It is one-Lipschitz
under a single column replacement and is zero on the advertised tail event.
If `m` center columns can each be approximated to error `eta/2` using a
shared disjoint reservoir, an identity block in the coefficient witnesses,
rank-nullity, and Bessel's inequality give deficiency at least `m/2`.
There is no bound or independence assumption on the reconstruction coefficients.

For a finite column law, let `Sigma = E[u*u^T]` and
`D_i = E[u_i^2] + 1/k`. Fixed signed sparsity implies `Sigma <= s*D`
and `trace D = s+1`. The Hermitian spectral theorem applied to
`D^(-1/2)*Sigma*D^(-1/2)` bounds the average squared residual of the
possibly nonsymmetric filter `(I-Sigma*D^(-1)/s)^L` by
`2*s^2/(2*L+1)`. No Euclidean contraction of that nonsymmetric matrix is assumed.

An absorbing-zero signed-column Markov chain realizes the corresponding
mean transition. A binomial combination of its first `L` post-transition
states has mean equal to the center minus its filter residual. Averaging
`b` independent paths conditional on the center gives mean squared error
at most

```
2*s^2/(2*L+1) + s*(2^L-1)^2/b.
```

Finite positive `L,b`, depending only on `s,eta`, make this at most
`(eta/2)^2/4`. Markov's inequality gives ideal reconstruction success
probability at least `3/4`.

The real transition retains a fresh block of sampled columns. With
probability one half it outputs zero; otherwise it takes the first column
with a nonzero requested coordinate, orienting its sign as in the ideal
transition. If there is no hit, it also outputs zero. Every visited state
therefore lies in the span of its retained block. The unconditional mass
of every outcome dominates `c` times the ideal mass when
`0 <= c <= 1/2` and `c <= ell/(2*k)`. This is a pointwise domination of
finite laws; no conditioning on favorable paths is used.

Put `J=b*L`, reserve `floor(r/2)` centers, and partition the remaining
columns into `J` blocks of length `ell`. For `r >= 4*J` and
`beta*k <= r <= k`, choose `c=beta/(8*J)`. Path and batch domination,
actual reservoir span membership, and linearity of expectation imply

```
E[deficiency of r independent columns] >= rho*r,
rho = c^(L*b)/8 > 0.
```

The IID variance is at most `r`. A sequential collision repair couples
independent index draws to a uniform ordered injective sample, with mean
Hamming cost `r*(r-1)/(2*n)`. Chebyshev and Markov give

```
Pr { smallestSingular > eta }
  <= 4/(rho^2*r) + (r-1)/(rho*n).
```

Equal fibers of size `r!` identify the ordered sample's range law with
the exact `powersetCard` ratio in the frozen definition. With
`beta=1/(2*C)`, the ratio assumptions imply the required aspect bound
eventually, `r -> infinity`, and `r/n -> 0`. The displayed bound tends to zero.

This proves the source's entire original asymptotic target (Corollary 1.2).
It does not formalize the source's stronger exponential finite tail or
positive-fraction singular-value theorem. The proof replaces source
pruning with regularization and uses a polynomial tail. Relative to the
planned route in the frozen target record, no-hit transitions return zero
and the auxiliary constants are simplified; the frozen theorem is unchanged.

## Modules and reused mathematics

| Modules | Role |
| --- | --- |
| `Definitions`, `ColumnAction`, `DeletionDefect` | Frozen semantics, coefficient transport, and actual deletion minimum |
| `Witnesses`, `FiniteCommonReservoir`, `Reconstructible` | Rank-nullity and Bessel bridge from reservoir approximation to deficiency |
| `FiniteProbability`, `FiniteVariance`, `FiniteVector`, `FiniteVectorAverage`, `FiniteBlocks` | Finite weighted laws, variance and mean identities, independent blocks |
| `SpectralFilter`, `Covariance`, `SignedVectors`, `CovarianceFilter` | PSD comparison, signed sparsity, and spectral residual bound |
| `FinitePaths`, `IdealKernel`, `IdealEstimator`, `IdealReconstruction` | Exact mean transition, polynomial estimator, and ideal success |
| `FirstHit`, `CoupledPaths`, `ReservoirStep`, `ReservoirReconstruction` | Real sampled blocks, unnormalized domination, and actual span witnesses |
| `IIDMean`, `UniformMean` | Uniform expected deficiency with dimension-independent positive constants |
| `FiniteSampling`, `FiniteSubsets`, `ProbabilityTransfer`, `SubsetDefect` | Collision coupling and exact uniform-subset tail |
| `Asymptotics`, `Solution` | Ratio consequences, squeeze, and complete exported theorem |

Mathlib supplies Euclidean spaces, linear isometries, orthonormal bases,
Bessel's inequality, rank-nullity, PSD matrices and the Hermitian spectral
theorem, finite sums and products, and filter limits. The small `Law` type
uses nonnegative real weights summing to one because every sample space here
is finite and the exported probability is a real cardinality ratio. Its
probability identities and concentration estimates are proved in the project;
no probabilistic oracle or new axiom is introduced. These local modules
are not presented as replacements for Mathlib's general probability library.

## Reproduction and provenance

Lean `4.33.1`, Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`, and transitive dependencies are pinned.
From this directory:

```sh
lake exe cache get
lake build Solution Challenge
lake env lean verification/Check.lean
```

For the authoritative fresh check, from the repository root on supported
unprivileged Linux:

```sh
tools/lean/bootstrap.sh /tmp/nla-tr07-checker
tools/lean/verify.sh randomized-and-low-rank-approximation/TR-07/lean /tmp/nla-tr07-checker
```

The independent [Challenge](Challenge.lean) contains one deliberate
comparison placeholder and is excluded from the Solution import graph.
[comparator.json](comparator.json) permits only `propext`, `Classical.choice`,
and `Quot.sound`, with no replaceable definitions. No numerical interval
certificate or trusted native evaluation is used. See [verification](verification/)
and [reviews](reviews/) for recorded checks, source hashes, scope and limitations.
Local compilation and the fresh sandboxed Linux check are separate gates.
Both passed; the authoritative [Linux run](https://github.com/marcusdavidwebb/OpenProblemsInNLA/actions/runs/36544197412)
accepted all 36 unchanged proof inputs on 29 September 2026.

The mathematical resolution is credited to Sidney Holden, Center for
Computational Biology, Flatiron Institute, Simons Foundation, New York, USA.
Huang, Rudelson and Tikhomirov retain conjecture and prior-result credit.
OpenAI Codex agents authored this Lean implementation and documentation.
Independent AI-agent reviews are identified separately; no human peer review
or source-author endorsement is claimed.
