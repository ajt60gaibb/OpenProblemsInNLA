# IE-22 exact mathematical and numerical target inventory — unreviewed draft

Status: statement drafting only. No IE-22 proof implementation has begun. The proposed Challenge has 20 intentional reference placeholders, which prove nothing. Local typechecking, if successful, verifies syntax/types only. Two independent reviewers must read the complete original target, full retained manuscript, these numerical targets, definitions and every Challenge statement before any boundary is frozen or any proof is implemented. The drafter cannot supply one of those independent approvals.

Original mathematical proof: Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Formalization draft: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. No contact email is added. Canonical IE-22 identity and source attribution are unchanged.

## Complete canonical mathematical statement

The following is the entire mathematical problem-statement section of `linear-systems-and-elimination/IE-22/README.md`, without replacing the supremum or its quantifiers:

Fix $`0<\theta<1`$. For a real $`m\times n`$ matrix $`A`$ with every row of Euclidean norm one, put

```math
s_\theta(A)=\min_{S\subseteq\{1,\ldots,m\},\ |S|=\lfloor\theta m\rfloor}
\min_{\|x\|_2=1}\|A_Sx\|_2,
\qquad
M_{m,n}(\theta)=\sup_{\|a_i\|_2=1}\sqrt{\frac nm}\,s_\theta(A).
```

Here $`a_i`$ is row $`i`$ of $`A`$, and $`A_S`$ contains exactly the rows indexed by $`S`$.

Determine the sharp asymptotic upper constant for $`M_{m,n}(\theta)`$ as $`n\to\infty`$ and $`m/n\to\infty`$. In particular, is it

```math
c_\theta=\left(\frac1{\sqrt{2\pi}}\int_{-a_\theta}^{a_\theta}t^2e^{-t^2/2}\,dt\right)^{1/2},
\qquad
\mathbb P(|G|\le a_\theta)=\theta,\quad G\sim N(0,1)?
```

Precisely, the proposed uniform inequality asks whether, for every $`\varepsilon>0`$, there exist integers $`N`$ and $`R`$ such that

```math
M_{m,n}(\theta)\le c_\theta+\varepsilon
\quad\text{whenever }n\ge N\text{ and }m/n\ge R,
```

and whether no smaller constant has this property. The supremum and quantifiers specify the source's uniform $`1+o(1)`$ bound; the floor convention handles row-count integrality.


## Literal objects and obligatory semantic bridges

Use unchanged IE-21 objects: `Space n = EuclideanSpace ℝ (Fin n)`, actual real `Mat m n`, Euclidean `matrixMap`, exact natural floor `retainedRows θ m`, actual retained row matrices, variational `deletionSingular`, its attained minimum and zero cases, `normalizedDeletion = (n/m)*sθ(A)^2`, the canonical density integral `gaussianTrim`, the proved positive unique Gaussian cutoff, and literal normalized surface law/product matrix law. No new definition of these objects is introduced.

`UnitRows A` is exactly `∀i, ‖matrixRow A i‖=1`. `normalizedSingular θ A = sqrt(n/m)*deletionSingular θ A` is the **unsquared** canonical statistic; it is not the IE-21 ratio divided by the operator norm. `unitRowValues` is precisely the image of all actual unit-row matrices under this statistic. `extremalValue` is the real supremum of that set. Its compulsory semantics prove nonemptiness, boundedness, attainment by an actual unit-row matrix, domination of every such matrix, nonnegativity and a harmless crude bound `sqrt(n)`. They also prove `normalizedSingular^2 = normalizedDeletion` and nonnegativity, for positive dimensions. Neither an empty supremum default nor an abstract “extremal constant” may replace M.

The final constant is `sharpConstant θ = sqrt(gaussianTrim θ)`, with its square and displayed canonical integral identified explicitly. Cutoff/quantile semantics are inherited from the unchanged proved IE-21 theorem. All primary statements fix `0<θ<1`; no uniformity as θ approaches an endpoint is claimed. All final matrix dimensions are positive integers. Finite auxiliary projected spaces have dimension `d>=1`. The exact floor is retained at every stage. Empty retained selections and maps with nonzero kernels continue to have zero variational singular value. No hypothesis `floor(θm)>=n`, full rank or invertibility is introduced.

## Source finite deterministic certificate

For any positive m, `1<=r<n`, `0<δ<1`, let `d=n-r` and `L=2/(1-θ)`. Define exactly

```
P(θ,d,r,δ) = 2/(r+1)
             + 4L(L/δ+2)/((r+1)δ²)
             + 2/(dδ²),
B(θ,n,r,δ) = n/((n-r)(1-δ)) * (hθ+2δ).
```

If `P(θ,n-r,r,δ)<1`, the selected `deterministic_finite_bound` must prove

```
(n/m)*sθ(A)^2 <= B(θ,n,r,δ)
```

for **every** unit-row A, with no aspect-ratio assumption and no dependence of the premise on m or A. The companion supremum theorem proves `M_{m,n}(θ)^2<=B` and `M_{m,n}(θ)<=sqrt(B)`. The strict probability-budget inequality is essential to extracting a good Gaussian realization. Positivity of `n-r` and `1-δ` must be proved before normalization or division. The natural subtraction in the Lean expression is legitimate only under `r<n`.

The following proposed selected interfaces prevent the finite argument from hiding its analytic assumptions:

1. `projection_semantics`: B is defined literally by restricting A along a Euclidean linear isometry J. Matrix multiplication agrees with A applied to Jg, row norms contract, and `sθ(A)<=sθ(B)`. This is the correct direction of the minimum inequality.
2. `spectral_projection`: existence of J from dimension n-r into n with `‖B‖op²<=m/(r+1)`, each projected row norm at most one, and `trace(BᵀB)<=m`. This spectral conclusion is proved, never supplied by the final theorem.
3. `gaussian_objective_mean`: for `Ψ_t(g)=(k/m)t-(1/m)Σ(t-(Bg)_i²)_+`, with standard d-dimensional Gaussian g and projected row norms at most one, integrability and `E Ψ_t<=hθ` hold for every t>=0. Gaussian projected rows can be correlated; no independence assumption is allowed. The scalar zero-variance case must be handled.
4. `gaussian_objective_variance`: `Ψ_t` has an actual second moment and `Var Ψ_t<=4t‖B‖op²/m`; spectral control then gives exactly `4t/(r+1)`. This is an obligation, not a Poincare axiom or a premise of the final matrix bound. It holds even for arbitrary θ because the θ-dependent term is constant in g.
5. `gaussian_energy_moments`: for `Z=‖Bg‖²/m`, actual second-moment integrability, `E Z=trace(BᵀB)/m` and `Var Z=2 trace((BᵀB)^2)/m²`. Nonnegative spectral eigenvalues and the spectral/trace bounds must imply `E Z<=1` and `Var Z<=2/(r+1)`.
6. `bounded_trimming_threshold`: nonnegative observations of average at most two have an attained exact floor-trimming maximum in `[0,L]`, including k=0. `threshold_lipschitz` gives the **one**, not two, Lipschitz constant in t. `threshold_grid` gives at most `L/δ+2` actual points in `[0,L]` covering it within δ.
7. `projection_good_event_bound`: the complement of the event `Z<=2`, `‖g‖²>=(1-δ)d`, and `Ψ_t<=hθ+2δ` for **all** t in `[0,L]` has probability at most P. Measurability of this full event is an explicit conclusion. Chebyshev supplies the three exact terms displayed above; the Gaussian radius variance `2d` is inherited from IE-21. This is not an assertion about only the finite grid.

The selected final finite bound must then normalize a nonzero good g through J to an actual unit direction and apply the exact finite trimming identity. No numerical integration, floating point or example matrices establish these universal statements.

## Exact schedule and uniform error rate

Use the source schedule literally,

```
r(n) = floor(n^(2/3)),
δ(n) = n^(-1/6),
```

with real powers, not integer division or an unreviewed rounded exponent. `deterministic_schedule` must prove eventual `1<=r(n)<n`, `0<δ(n)<1`, `P<1`, and `δ(n)->0`. It also makes the manuscript's Oθ estimate explicit: some real C>0, depending only on θ, bounds both P and `B-hθ` by `C*n^(-1/6)` for all sufficiently large n. The constant is existential because that is exactly what the manuscript's Oθ notation asserts; all finite-certificate constants remain literal.

`universal_squared_rate` requires `∃C>0 ∃N>=1 ∀m>=1 ∀n>=N`, both every unit-row matrix's normalized squared singular value and the **square of the actual supremum** are at most `hθ+C*n^(-1/6)`. Thus C and N cannot depend on m, A or an aspect sequence. `uniform_upper_all_rows` then requires `∀ε>0 ∃N>=1 ∀m>=1 ∀n>=N, M<=cθ+ε`, which is the source's stronger upper assertion with no aspect-ratio condition.

## Lower realization, every-sequence limit, and sharpness

`spherical_realization_from_finite_bound` reuses IE-21's simultaneous normalized-deletion estimate and actual unit-row support. Whenever its exact finiteFailure is strictly less than one, it must produce an actual unit-row matrix with normalizedDeletion within the original IE-21 error of hθ. The IE-21 **ratio limit alone is insufficient** for this step unless the operator normalization is also used. The unchanged finite-size theorem already supplies the required squared normalized numerator directly.

`high_aspect_near_extremizers` quantifies over every positive integer sequence m_j,n_j with **only** `n_j->infinity` and `m_j/n_j->infinity`. For every ε>0, eventually there is an actual unit-row A_j with `sqrt(n_j/m_j)*sθ(A_j)>cθ-ε`. These are pointwise existence statements; no common probability space, coupling between dimensions or computable choice is imposed.

`high_aspect_supremum_limit` requires, for every such pair of sequences,

```
M_{m_j,n_j}(θ) -> cθ.
```

It is not enough to exhibit one sequence, obtain an upper limsup or take a supremum over only random matrices. The true all-m upper bound and spherical lower witnesses must both connect to the literal M definition.

Finally define the original property without moving its quantifiers:

```
EventualUniformUpper(θ,C) :=
  for every ε>0, there exist integer N,R such that
  for all positive m,n, if n>=N and m/n>=R, then M_{m,n}(θ)<=C+ε.
```

Natural N,R are integer thresholds with no loss: any integer thresholds can be increased to nonnegative ones. The final selected `canonical_sharp_constant` must prove the property for cθ and that every real C<cθ fails it. Expanded, failure means **some fixed ε>0** defeats **every** pair N,R with an admissible positive m,n and `M>C+ε`; ε cannot depend on the thresholds. The every-sequence limit also remains a separate compulsory target. These exact assertions preserve the original sharpness, rather than merely identifying a convenient upper constant.

## Proposed boundary and dependency status

`comparator.json` lists all 20 proposed obligations, including the semantic, finite, rate, all-sequence and canonical sharpness targets. It is a **future specification**, not a successful Comparator receipt. There is no Solution, no proof implementation, no final Lake packaging and no formalization.yaml completion claim. The permitted future axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`; `definition_names` is empty. Every selected proof must eventually receive authentic LeanCert kernel trust checks, exact Comparator comparison, independent final review and reproducible Linux verification.

Draft Definitions import `NLA.IE21.FiniteSize` unchanged so the definitions and source-backed surface/Gaussian/matrix facts are reused verbatim. A hashed dependency inventory records those 31 inputs. IE-21's authenticated Linux run has passed; independent completion and publication reviews are in progress, and its PR has not yet been published. Reuse must be tied to its verified immutable source revision once available; no mutable cross-worktree path is an acceptable publication dependency. The portable packaging decision is intentionally deferred. Nothing in this draft edits or weakens IE-21.
