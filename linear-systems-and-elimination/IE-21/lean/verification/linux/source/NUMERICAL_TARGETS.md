# IE-21 exact statement draft

Status: unreviewed, incomplete, statement-only. No proof implementation has started. The 23 Challenge declarations contain deliberate reference placeholders; zero results are proved. Typechecking checks syntax and types only, not truth. Comparator and LeanCert verification have not run. Two independent exact-statement reviews must approve a frozen boundary before proof work.

Original proof: Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Formalization draft: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. No contact email is added. Original proof attribution and the canonical ID and page remain unchanged.

## Complete canonical mathematical statement

The following is the complete mathematical problem-statement section of `linear-systems-and-elimination/IE-21/README.md`:


Fix $`0<\theta<1`$. For $`A\in\mathbb R^{m\times n}`$ define

```math
s_\theta(A)=\min_{S\subseteq\{1,\ldots,m\},\ |S|=\lfloor\theta m\rfloor}
\min_{\|x\|_2=1}\|A_Sx\|_2,
```

where $`A_S`$ contains the rows indexed by $`S`$. Let $`a_\theta>0`$ satisfy $`\mathbb P(|G|\le a_\theta)=\theta`$ for $`G\sim N(0,1)`$, and set

```math
h_\theta=\frac1{\sqrt{2\pi}}\int_{-a_\theta}^{a_\theta}t^2e^{-t^2/2}\,dt.
```

For every integer sequence $`(m_j,n_j)`$ with $`n_j\to\infty`$ and $`m_j/n_j\to\infty`$, let the rows of $`A_j\in\mathbb R^{m_j\times n_j}`$ be independent and uniformly distributed on $`\mathbb S^{n_j-1}`$. Is

```math
\frac{s_\theta(A_j)^2}{\|A_j\|_2^2}\ \xrightarrow{\mathbb P}\ h_\theta?
```

This states Steinerberger's proposed asymptotic with $`\theta=q-\beta`$. Convergence in probability and the floor convention make the source's limiting statement explicit. The source also asks for quantitative error bounds; these belong to this problem rather than separate entries.


## Literal semantics and mandatory bridges

`Space n` is Mathlib's real Euclidean space on `Fin n`, with its Euclidean norm. `Mat m n` is the actual real Matrix type. Its measurable structure is the ordinary finite product Borel structure. `matrixMap` is `Matrix.toEuclideanLin` promoted to a continuous linear map, and `operatorNorm` is that map's operator norm. It is **not** the matrix entrywise supremum norm. `matrix_semantics` must prove coefficient multiplication, attainment of the operator norm on the unit sphere, the norm bound, and the retained-norm sum of squares.

`retainedRows θ m = Nat.floor (θ*m)`. On `0<θ<1` this is the required nonnegative integer floor. `retainedMatrix A S` is an actual matrix indexed by the subtype of rows in `S`, so its Euclidean image norm equals the canonical `‖A_S x‖₂`. `deletionSingular` is the real infimum over exactly the pairs `(S,x)` with `|S|=floor(θm)` and `‖x‖₂=1`. The compulsory `deletion_minimum` proves nonnegativity, attainment, and the lower bound for every admissible pair. Thus the infimum is a genuine finite/compact minimum; no empty-set default is licensed. `deletion_zero_cases` explicitly handles zero retained rows and a nonzero kernel vector of any admissible retained submatrix, with no full-rank restriction.

`finiteTrim k y` is the least sum over exactly `k` entries. Its required theorem proves both finite minimum attainment and the attained scalar maximization formula with `(t-y_i)_+`. `directional_minimum` identifies the minimum over all unit directions with `(n/m)sθ(A)^2`. These obligations cover exchanging the finite and compact minima.

`surfaceMeasure n` is `(volume : Measure (Space n)).toSphere`, Mathlib's genuine Euclidean surface measure from polar coordinates. `surfaceLaw` divides this measure by its actual total mass; it is not a Gaussian definition. `sphereLaw` is its inclusion into Euclidean space. `surface_probability` proves finite positive surface mass, probability normalization and unit-sphere support for every `n≥1`. `matrixLaw` is the pushforward of the finite product of these laws through the actual row-coordinate map. `product_row_semantics` proves its probability, independence, row marginals and support. `independent_row_transport` proves equality with the law of **any** measurable random matrix whose rows are independent and have `sphereLaw`. The final theorem allows a different probability space at each dimension and imposes no coupling between dimensions.

`gaussianDirection g = ‖g‖⁻¹ • g` is defined as zero at the zero vector. Its equality in law with `sphereLaw`, Gaussian nullity of zero, independence from the Gaussian radius, and radius-square mean `n` and variance `2n` are explicit required conclusions of `gaussian_surface_correspondence`. They are never premises of the target or probability bounds.

`gaussianCutoff θ` is the infimum of nonnegative `a` with standard Gaussian probability `P(|G|≤a)≥θ`. `gaussian_constant` must prove positivity, exact equality to θ, uniqueness, and that `gaussianTrim θ` (defined by the displayed canonical density integral) equals the truncated Gaussian second moment and lies in `[0,1]`. There is no hidden supplied quantile. `populationTrim` is the scalar dual supremum `sup_{t≥0}(θt-E(t-Y)_+)`; it is a proof interface, not the definition of the final Gaussian constant. Its use avoids choosing law-dependent selectors. The spherical comparison and pointwise concentration statements must prove its exact required behavior.

All finite statements with ratios assume `m≥1,n≥2`; the underlying sphere and minimum semantics also cover `n=1`. The final sequences use positive integer dimensions. Any sequence of positive matrix dimensions tending to infinity satisfies the finite `n≥2` restriction eventually, so no canonical sequence is excluded. The finite theorem covers every row retention count, including zero and counts below the column dimension.

## Exact finite-size certificate

Fix `0<θ<1`, `m≥1`, `n≥2`, and

* `0<t<1`;
* `0<ε≤(1-θ)/2`;
* `0<δ<1`.

Define

```
L = 2/(1-θ)
D = 2Lε + L/m + 2(1+t)δ
F = 2*9^n*exp(-m*t^2/512) + 5*(1+2/δ)^n*exp(-2*m*ε^2)
E = (D + sqrt(2/n) + t)/(1-t).
```

`finite_size_bound` says the probability of failing **any** of these simultaneous conclusions is at most `F`:

```
operatorNorm A > 0
|(n/m)*operatorNorm(A)^2 - 1| ≤ t
|(n/m)*deletionSingular(θ,A)^2 - hθ| ≤ D + sqrt(2/n)
|deletionRatio(θ,A) - hθ| ≤ E.
```

This is precisely the source's quantitative covariance, trimming and ratio argument. The denominator is proved positive on the successful event. A bound `F>1` is permitted and simply uninformative; it does not restrict the input. `finite_size_independent_rows` supplies the same ratio-probability bound on any probability space satisfying the canonical independent spherical row law.

The intermediate `GoodEvent` combines covariance operator error at most `t` with the directional trimming bound for **all** unit vectors. Its complement probability is bounded in `uniform_trim_concentration`; measurability is a separate required theorem. No finite test net is substituted for the universal direction quantifier. The net is only a proof device.

Numerical constants in required proof interfaces remain those of the manuscript:

* spherical moment identity `E Y^r = n^r prod_{j<r}(2j+1)/prod_{j<r}(n+2j)` and bound `2^r*r!`, including `r=0`;
* `E exp(a(Y-1)) ≤ exp(32a^2)` for `|a|≤1/8`;
* pointwise trimming failure at most `5 exp(-2mε^2)` with error `2Lε+L/m`;
* sphere net size at most `(1+2/δ)^n`, with actual unit net points and covering distance at most δ;
* covariance failure at most `2*9^n exp(-mt^2/512)`;
* spherical-to-Gaussian trimming discrepancy at most `sqrt(2/n)`.

Every identity and inequality is universally quantified. No numerical interval subdivision or floating-point calculation is proposed.

## Every-sequence conclusion

For arbitrary positive integer sequences `m_j,n_j` assume exactly `n_j→∞` and `Q_j=m_j/n_j→∞`. `aspect_schedule` must prove that

```
t_j = ε_j = δ_j = 32 sqrt(log(Q_j)/Q_j)
```

eventually satisfies all finite-size parameter restrictions, and that both `F_j` and `E_j` tend to zero. There is no hidden lower bound on the rate at which `Q_j` grows.

`spherical_ratio_limit` then asserts for every `η>0` that the probability of `|sθ(A_j)^2/‖A_j‖₂^2-hθ|>η` tends to zero under `matrixLaw`. `original_random_row_limit` asserts this on arbitrary changing probability spaces with independent normalized surface-law rows. Probability convergence is stated directly through these real-valued probabilities; it does not require an unnecessary common sample space. These final limit declarations and the quantitative theorem are all compulsory Comparator targets. A finite-size result alone does not finish IE-21.

## Dependency and API plan for reviewers

The checked pins are Lean `v4.33.1`, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The package lock is copied from the campaign's reviewed TR-27 package with only the local package name changed.

1. Finite trimming and attained minima: `Finset`, real `sInf/sSup`, compact Euclidean spheres, `IsCompact.exists_isMinOn`, `Matrix.toEuclideanLin`, and finite-dimensional continuous linear maps.
2. Surface/Gaussian bridge: `Measure.toSphere` and `measurePreserving_homeomorphUnitSphereProd` in `MeasureTheory/Constructions/HaarToSphere`; `stdGaussian`, `stdGaussian_map`, and `stdGaussian_eq_map_pi_orthonormalBasis` in `Probability/Distributions/Gaussian/Multivariate`. Normalization, Gaussian polar density, radius-direction independence, exact spherical moments and trimming comparison still need proofs.
3. Independent products and transport: `iIndepFun.map_fun_eq_pi_map` and the corresponding equivalence in `Probability/Independence/Basic`; ordinary measurable finite product maps. Matrix Borel/coefficient semantics still need the stated bridges.
4. Bounded-variable concentration: `hasSubgaussianMGF_of_mem_Icc`, `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, and independent-sum Hoeffding in `Probability/Moments/SubGaussian`. The source's empirical trimming/count comparison, spherical quadratic MGF and its Chernoff specialization still need proofs.
5. Nets and covariance: `Metric.coveringNumber`, maximal separated sets and Haar volume. The precise dimension-dependent cardinal estimate, symmetric quadratic-form estimate, subset-form Lipschitz estimate, and all-directions measurability/concentration still need proofs.
6. Final assembly: exact rational inequalities, real square root/log/exp limits and measure monotonicity. The `32` schedule must be proved for all divergent aspect ratios, not checked for examples.

The Challenge contains only these explicit obligations and the complete canonical conclusions. There are no hypothesis structures containing any concentration, rank, Gaussian representation, quantile, norm equivalence, or asymptotic conclusion. Some intermediate interfaces are stronger than the minimal canonical theorem; they organize the supplied source proof and must also be discharged if retained in the reviewed boundary.

## Reproduction and review status

`lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` pin the build. `reviews/typecheck.py` is a development-only macOS cache runner; it writes oleans outside this source tree and records the exact Lean command and result. An ordinary fresh pinned Lake build is the portable intended route. The draft does not yet have a Solution module, so `comparator.json` is a future boundary specification, not an executed comparison.

The only allowed future proof axioms are `propext`, `Classical.choice`, and `Quot.sound`; `sorryAx` is confined to the intentional Challenge reference. Every selected future Solution declaration must receive LeanCert kernel trust marking and successful independent Comparator, axiom, clean-build and correspondence checks before any verification metadata or canonical status is promoted.
