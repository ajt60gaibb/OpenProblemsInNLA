# Complete probabilistic proof: local implementation finished

The original IE-06 limit and the stronger all-Schur tail are proved in
[Unconditional.lean](NLA/IE06/Unconditional.lean), with all six frozen reference
signatures implemented in [Solution.lean](Solution.lean). The final exports
have compiled with LeanCert kernel checks and only the three permitted
foundational axioms. The
[fresh local verification run](verification/local/attempt-0i_0ibma/result.json)
passed: 114 source modules compiled, 3,229 owned declarations across 113 concrete
modules passed the transitive axiom audit, both `sorry` and native-execution
controls were rejected, and the unchanged Comparator library accepted the
actual statements, referenced definitions, and proof axioms of all six targets.
The [Comparator log](verification/local/attempt-0i_0ibma/CompareSolution.lean.log)
records each result. This uses trusted pinned dependency caches and is not an
authoritative Linux sandbox, exporter, or separate raw-kernel-replay run; see
[verification/SUMMARY.md](verification/SUMMARY.md).

No mathematical probability premise remains in the final theorems. Reusable
conditional helpers, such as `ExtensionBound` and `InverseTailEstimate`, remain
visible in intermediate modules; the final proof supplies their unconditional
implementations. The six deliberate `Challenge.lean` reference placeholders
are excluded from proof-development sorry counts and are never imported into
the candidate proof.

## Complete proof chain

1. **Exact elimination and Gaussian semantics.** `Definitions`, `Semantics`,
   `Measurability`, `Pivot`, and `GEPP` formalize the actual all-Schur growth
   event, prove its measurability and probability normalization, and construct
   admissible paths for nonsingular inputs. `GaussianNull` proves polynomial
   nullity and Gaussian nonsingularity. `GaussianTies` proves almost-sure path
   agreement, preserving the event that allows every admissible tie choice.
   `GaussianDenominator` proves the exact input-normalization exception
   probability $q^{n^2}$, $0<q<1$, and its eventual decay against every real
   inverse power.

2. **Gaussian and spectral estimates.** `GaussianQuadratic`,
   `GaussianFrobenius`, and `GaussianLinear` prove actual product-Gaussian
   moment and tail estimates. `GaussianConcentration` and
   `GaussianConcentrationSpace` connect the pinned, proved Gaussian Lipschitz
   concentration development to the concrete laws used here. `Spectral`,
   `SpectralMeasurability`, `KyFan`, `FiniteNet`, `GaussianOperatorNet`, and
   `GaussianSpectralTail` prove the product singular-value estimate with
   universal constant 16. `GaussianSmallest`, `GaussianRegression`,
   `GaussianOperatorInverse`, the determinant/principal-moment modules, and
   `GaussianOvercrowding` prove rank, inverse, and small-singular-value bounds.
   `KernelFrame` and `SpectralStacking` prove the deterministic kernel-frame and
   stacking estimates with all rank and denominator guards discharged where
   applied. No measurable choice of a singular-vector basis is assumed.

3. **Actual adaptive pivot conditioning.** `GaussianShift` derives Anderson's
   inequality from the pinned proved Prékopa–Leindler development.
   `GaussianRestriction` proves the directional MGF bound for the actual
   normalized restriction of Gaussian measure to a measurable convex symmetric
   set of positive mass. `SubGaussianQuadratic` supplies its quadratic tail.
   `GaussianPivotConditioning` proves the canonical pivot-order fiber law,
   including the exact weights $q(T)^{n-t}$ and their total mass one.
   `PivotFiltration`, `GaussianColumnSplit`, `GaussianCoordinates`, and
   `GaussianFutureWindow` establish independence of the actual unrevealed
   columns. The argument neither conditions on a future success event nor
   incurs a factorial pivot-order union loss.

4. **Selected-block extension.** `SelectedBlockElimination` identifies actual
   selected blocks and elimination rows. `GaussianPivotMasking` supplies a
   measurable candidate depending only on outside rows. `GaussianCandidateRows`,
   `GaussianStackingTail`, `GaussianCandidateStacking`, and
   `SelectedBlockCandidates` prove the fixed-fiber estimates and finite
   candidate union. `GaussianAppend`, `GaussianAdaptiveAppend`, and
   `SelectedBlockAppend` prove the actual fresh-column extension bound and pay
   its failure cost once. `SelectedBlockExtensionCore` combines these
   probability estimates. `SelectedBlockExtensionScalars` proves the explicit
   dimension-independent numerical absorption. `SelectedBlockExtension`
   supplies the unconditional source Lemma 5.4 event and probability bound,
   with the original singular-value indices and quantifiers.

5. **Simultaneous retained-inverse bound.** `ScalarRecurrence`,
   `SpectralRecursionScalars`, and `GaussianSpectralBase` establish the scalar
   profile and Gaussian base case. `TruncatedInverse` and `ProfileSum` prove
   the retained inverse decomposition and reciprocal-sum estimate.
   `GaussianSpectralRecursion` implements the induction and finite union.
   `GaussianSpectralProfile.inverse_tail` supplies the unconditional result:
   for every $\beta\ge1$, a uniform $D\ge0$ bounds the simultaneous bad event,
   over all selected prefixes and all $r\ge\lceil\sqrt{\log n}\rceil$, by
   $\exp(-(\beta-2)\log n)$ whenever $\log n\ge256$.

6. **Rows, growth, and final probability.** `Elimination`, `EliminationBlock`,
   and `EliminationSmoothing` prove exact operator composition, processed-column
   annihilation, and cancellation of the discarded directions.
   `GaussianPrefixDecomposition`, `GaussianFutureSmoothing`,
   `GaussianAdaptiveFuture`, and `GaussianStageSmoothing` prove the actual
   stage bound with failure $(2n+1)e^{-x}$. `GaussianAllRows` performs the
   early/late-stage argument and finite union. `GrowthEvents` and
   `GaussianEliminationTail` transfer canonical row bounds to the original
   normalized all-admissible-path event. The combined failure bound is
   
   $$
   \Pr\{\text{retained-inverse failure}\}
   +(2n^2+n+2n^3)e^{-x}+q^{n^2}.
   $$
   
   `FinalGrowthScalars` bounds the actual growth threshold by
   $\sqrt n\exp(C\sqrt{\log n})$. `FinalFailureScalars` proves a strict
   $n^{-\alpha}$ budget using $\beta=\alpha+4$ and $x=(\alpha+6)\log n$.
   `FinalAssembly` combines the estimates, `Unconditional` supplies the proved
   simultaneous inverse theorem, and `Reduction` derives the original
   $n^{1/2+\eta}$ limit for every $\eta>0$.

The intermediate constant 16, the quadratic tail derived by a Gaussian mixture
and finite Jensen inequality, and the sufficient scalar cost
$6\sqrt{\log n}$ are reviewed proof routes. They preserve the complete final
all-Schur estimate and original limit. The sharper arbitrary-cutoff profile
from the manuscript is not advertised as a separate formal result. Symbolic
inequalities and eventual bounds avoid a large finite numerical cutoff.

## Scope, review, and preservation

The fixed source is [Urschel v1](https://arxiv.org/abs/2610.06785v1), Sections 4
and 5. The displayed Theorem 1.4 concerns LU growth; the all-Schur strengthening
is extracted from the argument, with its additional bridges proved here.
The [full proof specification](reviews/full-proof-specification.md) records
that distinction and the contracts for the supporting estimates.

Exact mathematical and numerical statements received independent AI-agent
review before implementation. Subsequent reviews checked concrete sources,
source hashes, proof dependencies, and compilation evidence. The
[final independent mathematical scope audit](reviews/final-independent-mathematical-scope-audit.md)
approved preservation of the original event, quantifiers, stage coverage,
normalization, tie convention, and closed probabilistic proof chain. Adopted proof
modules retain immutable upstream revisions, licenses, and compatibility
records in `source/`. The package uses no assumed literature axiom, native
trust axiom, or proof-development `sorry`. Review reports are not human peer
review or John Urschel's endorsement.

IE-06 remains the same permanent ID, canonical path, and complete original
problem. The canonical README, TeX, and PDF were not changed by this task;
preexisting working-tree edits and full statement snapshots were retained.
There is no additional unsolved IE-06 target. Nothing has been committed or
pushed, no remote CI has been dispatched, and John has not been contacted.
The maintainer will decide the next step after speaking with him.

The successful local LeanCert and actual six-target Comparator library checks
have distinct scopes from the unchanged shared Linux sandbox/exporter/kernel-
replay gates, which were not run. The final receipt binds the delivered proof
sources; earlier receipts describe only their recorded snapshots. The local
checks trust the pinned compiled dependency caches, whose tracked sources and
revisions were checked before and after execution.
