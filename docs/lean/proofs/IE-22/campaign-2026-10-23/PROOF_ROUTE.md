# IE-22 proof route and module map

The theorem `NLA.Proofs.IE22.target` proves the literal reviewed `NLA.Statements.IE22.Target`. For each exact Gaussian quantile with `0 < θ < 1`, it gives the eventual uniform upper constant `sqrt(TrimmedMoment a)` for the supremum over every real unit-row matrix, and excludes every smaller real constant. The original floor, Euclidean unit vectors, actual energy infimum, matrix supremum, and Gaussian integral remain in the statement.

The implementation was developed by coordinated OpenAI Codex AI agents, with separate independent statement and proof reviews. The retained mathematical resolution and manuscript credit belong to Matthew J. Colbrook; the source's AI-assistance and review disclosures remain intact. The Lean development uses a qualitative route tailored to the original target. It does not claim a new source resolution, an explicit asymptotic rate, or a formalization of every stronger manuscript result.

## Universal upper bound

Write `h = TrimmedMoment a` and `hinge(t,z) = max(t-z²,0)`. The genuine Gaussian integral at the quantile threshold is `θ a² - h`. More generally, `θ t - E hinge(t,G) ≤ h` for every nonnegative threshold. These statements use the exact original Gaussian law and literal interval-integral definition of `h`.

The covariance argument needs no derivatives or Gaussian Poincaré theorem. For centered jointly Gaussian `X,Y`, subtract the actual regression term `Cov(X,Y)/Var(X) * X` from `Y`. When the variance is positive, the resulting Gaussian residual is independent of `X`. Cauchy–Schwarz and the elementary Lipschitz variance contraction then give `|Cov(f(X),g(Y))| ≤ Lip(f) Lip(g) |Cov(X,Y)|`. The zero-variance case is proved separately. Applying this to the quadratic hinge gives the bound `4t |Cov(X,Y)|`.

For each matrix, diagonalize its actual covariance `AᵀA` and remove the fixed number `r` of leading covariance directions. The retained orthonormal columns define a Euclidean linear isometry from dimension `d = n-r` to the original space. Every projected row has squared norm at most one. Nonnegative ordered eigenvalues with total trace `m` bound the remaining covariance eigenvalues by `m/(r+1)`. The trace/Frobenius identity and finite Cauchy–Schwarz therefore prove the actual row Gram bound

```
sum_(i,j) |<b_i,b_j>| ≤ m² / sqrt(r+1).
```

Consequently the normalized finite threshold dual has variance at most `4t/sqrt(r+1)`, and its expectation is at most `h`. A finite threshold mesh in `[0,4/(1-θ)]` suffices. Chebyshev bounds control its finitely many dual errors, the actual Gaussian norm-square variance controls norm loss, and Markov bounds the total row energy above `4m` with probability at most `1/4`. Explicit parameter selection makes the union of the bad events have probability strictly below one, producing an actual Gaussian vector satisfying all three requirements.

The threshold dual is 2-Lipschitz, so the mesh estimate extends over the entire interval. An actual minimum-energy retained subset realizes the finite trimming dual at some threshold in that interval; the energy bound supplies this threshold bound. Normalizing the Gaussian vector through the retained isometry produces an original Euclidean unit vector. Its actual retained energy gives the upper estimate for the original infimum. First choose the tolerance, then the finite mesh and fixed `r`, then the ambient threshold `N`. This proves the squared bound for every positive row count once `n ≥ N`.

## Sharp unit-row witnesses

Normalize actual Gaussian vectors to unit rows, defining a fixed unit vector at the zero input. The scalar observation is the original Euclidean inner product multiplied by `sqrt(n)`. The norm-square mean and finite variance, together with a finite fourth moment, show that its hinge expectation approaches the scalar Gaussian hinge expectation uniformly in the unit direction. This uses direct estimates on the small-norm event and Cauchy–Schwarz; no radius–direction independence or replacement probability law is assumed.

For a finite family of bounded measurable tests, the genuine finite product measure gives variance of an average proportional to `1/m`. Chebyshev and the finite union bound produce arbitrarily large actual finite samples approximating all tests. A compact unit-sphere net and the proved direction Lipschitz bound extend this to every unit direction simultaneously. These normalized samples are an actual matrix with unit rows.

At threshold `a²`, the elementary trimming dual lower bound applies to every retained subset and every unit vector. The Gaussian expectation identity and the floor loss, bounded by `a²/m`, give the normalized squared lower bound `h-ε` for the actual infimum. The dimension and sample count can exceed any prescribed `N` and `R*n`, respectively. This is the exact witness quantifier order required for no-smaller optimality.

## Module map

| Modules | Role |
| --- | --- |
| `EnergyBounds` | Exact finite trimming inequality; genuine nonempty, bounded energy infimum. |
| `GaussianBasics`, `GaussianNormBounds` | Actual Gaussian linear observations, scalar moments, norm-square means, variances, and probability bounds. |
| `GaussianCovariance` | Derivative-free Gaussian residual argument and the correlated hinge variance estimate. |
| `GaussianTrimming` | Literal interval moment and exact quantile/hinge integral identities. |
| `TrimmingDual` | Actual minimizing retained subset and bounded attaining threshold. |
| `SpectralProjection` | Ordered covariance eigenbasis, true retained isometry, and actual Gram bound. |
| `GaussianUpperBounds`, `GaussianUpperRealization` | Genuine dual expectation/variance estimates and simultaneous Gaussian realization. |
| `UpperParameters`, `UniversalUpper` | Qualitative tolerance selection, threshold mesh, normalization, and complete universal squared upper endpoint. |
| `NormalizedGaussianRows`, `NormalizedGaussianApprox` | Actual unit rows, direction continuity, and uniform expectation approximation. |
| `FiniteSamples`, `UniformFiniteSamples`, `LowerWitness` | Genuine large finite samples, compact-direction extension, and complete near-sharp witness endpoint. |
| `ExtremaBounds`, `Assembly`, `Final` | Nonempty bounded matrix supremum; square-root transport; exact eventual-uniform and no-smaller clauses. |

These are the 19 proof modules at checkpoint `353ebcfc`. They import the preserved shared statement modules. `ExtremaBounds` establishes the supremum's actual nonempty bounded domain, so the final comparison does not use a default supremum value. `Assembly` supplies `UniformUpper` with natural dimension/aspect-ratio thresholds chosen before all dimensions and matrices, and uses the witnesses to refute every smaller real constant, including negative ones. `Final` applies both complete endpoints without extra hypotheses.

The historical scaffold also contained a separate `SupremumConverges` clause with the ambient-dimension growth hypothesis omitted. That unsupported extension is retained as historical source and is not part of the reviewed original two-clause target. This proof makes no claim for that clause and does not silently extend its quantifiers. Stronger convergence or rate claims in the manuscript require their own exact statements and verification.
