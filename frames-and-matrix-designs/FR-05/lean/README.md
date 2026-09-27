# FR-05 Lean formalisation

The full FR-05 Gaussian probability theorem is locally Lean-checked, following
the frozen [source manuscript](sources/README.md). [Solution.lean](Solution.lean)
exports:

- `NLA.FR05.phaseRetrieval_injective_probability_le_inv`:
  $p_d \le C/d$ for every $d \ge 2$, for some $C>0$.
- `NLA.FR05.phaseRetrieval_injective_probability_tendsto_zero`:
  the original target $p_d \to 0$.

Both use the original iid standard complex-Gaussian law, `4d-5` rows, and
all-signals injectivity predicate. No analytic hypotheses remain. Independent
review and the isolated Linux verification are still pending; the catalog
status remains unchanged.

## Where to start

1. [Definitions](NLA/FR05/Definitions.lean) and
   [Probability](NLA/FR05/Probability.lean) give the exact statement boundary.
   [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) records its scope and parameters.
2. [FinalAssembly](NLA/FR05/FinalAssembly.lean) is the short proof joining the
   two propositions and the sampler identities. [FINAL_ASSEMBLY.md](FINAL_ASSEMBLY.md)
   explains the argument.
3. [Proposition31](NLA/FR05/Proposition31.lean) supplies the planted-law
   $C/M^2$ bound; [PROPOSITION_3_1.md](PROPOSITION_3_1.md) explains the proof.
4. [LikelihoodComparison](NLA/FR05/LikelihoodComparison.lean) is the public
   entry point for Proposition 3.2; [PROPOSITION_3_2.md](PROPOSITION_3_2.md)
   explains its $L^2$ comparison and Lemmas 3.3–3.5.

The public import `NLA.FR05.Proof` exposes the complete development. The
repository-standard `Definitions.lean`, `Proof.lean`, `Challenge.lean`, and
`Solution.lean` entry points and final theorem names have been retained.
Imports of individual implementation modules now use the subject folders;
retired auxiliary lemmas are recorded in the library-style guide.

For reuse, import the relevant subject module instead of the full `Proof`:
`NLA.FR05.Measure.Comparison` for product densities, mixtures, and Cauchy–Schwarz;
`NLA.FR05.Geometry.Obstruction` for deterministic phase-retrieval invariance;
or `NLA.FR05.SmallBall.GaussianSmallBall` for scalar Gaussian bounds. The Gaussian
tail law has a registered probability-measure instance, so callers need no local setup.

## Source organisation

The library has 112 modules, arranged by mathematical subject (down from 177
before reorganisation and 157 before the latest consolidation). Short, closely
related developments are combined into sections; longer analytic proofs stay
separate. The root of `NLA/FR05/` contains only eight definition/entry-point
modules, including the parameter definitions and final numerical reduction.

| Folder under `NLA/FR05/` | Contents |
| --- | --- |
| `Geometry/` | Exact ambiguity, rank-two charts, finite-dimensional linear algebra, event measurability |
| `Planted/` | Jacobian and derivative bounds, perturbations, Newton contraction, good-event assembly |
| `SmallBall/` | Phase/Gaussian small-ball bounds and their source-row specialisations |
| `Gaussian/` | Gaussian densities, moments, radial laws, and sphere projections |
| `Densities/` | Source sampling laws, row coordinates, planted/reference densities and moments |
| `Cone/` | Cone coordinates, phase integrals, correlation and exponential estimates |
| `Overlap/` | Haar conditioning, overlap geometry, and overlap-density identities |
| `Likelihood/` | Likelihoods, kernel bounds, Taylor estimates, and Proposition 3.2 integration |
| `Bridges/` | Exact sampler-to-density and Haar-mixture identities |
| `Measure/` | Product-section estimates, Haar mixtures, and event-local Cauchy–Schwarz |

The [library-style guide](LIBRARY_STYLE.md) describes the reusable measure-theory,
coordinate-invariance, Gaussian, small-ball, and overlap APIs and their regression
checks. The refactors share product/symmetry laws and remove duplicated analytic
arguments without adding library modules. Paper-specific small-ball assembly and
reference-law constants remain in their application modules.
The latest mathematical simplifications use exact midpoint cancellation for the
quadratic planted map and factorised exponential/cosh estimates for the likelihood.
They shorten the proof and strengthen intermediate bounds without changing the
original final statements; see the guide for retired auxiliary lemma names.
The final simplification pass removes another 309 source lines without adding
modules or declarations, chiefly by simplifying the cosine-band argument and
reusing mathlib's norm comparisons.

The source organisation is not a strict dependency layering: some subjects
share technical lemmas. The module import graph is acyclic. The
[module map](verification/reorganisation/module-map.json) records every old
flat module's current location and the 45 subsequently retired subject modules.
Merged developments have named sections; their subsequent proof simplifications
are recorded separately in the library-style guide.

## Build and verification

The project pins Lean 4.33.1 and Mathlib in `lakefile.toml`. With the pinned
dependencies available, run:

```sh
bash verification/library-cleanup/check.sh
shasum -a 256 -c verification/library-cleanup/source-sha256.txt
```

The four `Challenge.lean` placeholders are isolated statement-comparison
fixtures and are never imported by `Solution`. The solution contains no proof
placeholders; the final theorems use only `propext`, `Classical.choice`, and
`Quot.sound`. The [current local audit](verification/library-cleanup/README.md)
records the checks after the reusable-API refactor. Earlier verification directories are
preserved as historical evidence for their original source layouts.

These local development checks are not the repository's isolated Linux
Comparator/kernel verification or independent statement review. Neither is
claimed here. The source manuscript, author attribution, license, public
FR-05 theorem statements, and canonical problem ID are unchanged by these refactors.
Both the quantitative bound and original limit are selected in `comparator.json`.
