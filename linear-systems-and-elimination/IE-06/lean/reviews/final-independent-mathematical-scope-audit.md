# Final independent mathematical scope audit — IE-06

Reviewer: independent mathematical review agent, separate from the author of the final assembly and Solution. Verdict: **approved**. No replacement of the original target, quantifier weakening, loss of a Schur stage, unaccounted normalization exception, restriction to a favorable tie choice, or remaining source-probability premise was found.

This report is a targeted semantic audit of the frozen sources and the final proof connections. It is not a fresh-build, Comparator, Linux-sandbox, exporter, or raw-kernel-replay receipt. The separate final verification run supplies execution evidence. In particular, the source-pattern check described below is not substituted for the complete transitive axiom audit.

## Bound source identities

| File | SHA-256 |
| --- | --- |
| `source/original-HEAD-README.md` | `60a6d3ba647c4443e07e906cca8950007c15c12e326c8496db8a670e6ec308bf` |
| `NLA/IE06/Definitions.lean` | `a5a8bf8d4a9f6dc97d0b645a4ed7639ee808ae4d340dc70c913e06ed5057c19a` |
| `NLA/IE06/Statements.lean` | `16d5a994426a65e9a167af3766b4ea66521448294f46b493fe1bf6e79e5b807b` |
| `Challenge.lean` | `701de729aceba6a69c72440c030b98c686942571b7f0160c84bdd9b95ceecbda` |
| `Solution.lean` | `6defa3c5108824ee18be9f9180fd15cd166b476afd6e0476cbce35c929c0a2be` |
| `NLA/IE06/Unconditional.lean` | `5fa32ea1b08029b89c2965226697611b90612d9dc7d78b381e03b155b64ef3f4` |

Additional exact hashes for the inspected final-chain and conditioning modules are in `final-independent-mathematical-scope-audit.json`. The retained original README was compared byte-for-byte with `git show 286d8768fbd9a69264daa88e285680293db29837:linear-systems-and-elimination/IE-06/README.md`; it matches. The permanent registry still maps IE-06 to that canonical path. The retained statement includes the complete original context and target, rather than only its displayed formula.

## Exact original event and probability law

The original asks, for every real eta>0, for the probability of exact-arithmetic partial-pivoting growth exceeding n^(1/2+eta) to tend to zero. `SquareRootUpperBound` states precisely this, with a real exponent and direct ENNReal measure values converging to zero. No finite numerical experiment, fixed eta, unspecified polynomial exponent, or subsequence substitutes for the limit.

`gaussianMatrix n` is the nested finite product of n^2 scalar `gaussianReal 0 1` laws, with variance one. It is neither an arbitrary abstract law nor a Gaussian law conditioned on successful elimination. The separately implemented `gaussianMatrix_probability` theorem supplies probability mass one.

`trajectory A path 0=A`. At stage k, the recursive update swaps the selected active row into position k and applies the exact scalar Schur update to rows and columns strictly beyond k. `activeMaxNN` restricts the maximum to active indices. `growth` takes all k in Fin n, hence includes the input at k=0 and the last scalar complement at k=n-1. Stored multipliers, eliminated entries, and the zero matrix after all n eliminations do not replace or contaminate these maxima. Only rows are permuted, as required for partial pivoting.

Admissibility requires an active row, a nonzero pivot, and a non-strict largest-magnitude comparison against every active row. Consequently all tied maximizers are permitted. Total real division extends the recursion to invalid inputs but is never accepted as an admissible zero pivot. `exceedanceEvent` excludes singular inputs and zero dimension, exactly matching the nonsingular convention and making only a harmless finite-dimensional totalization. Nonsingular positive-dimensional inputs have a positive input entry maximum, so the ratio is the stated normalization.

The event contains an **existential bad admissible path**. Its complement bounds every admissible path; it is not the easier assertion that one successful choice exists. `admissiblePath_exists` prevents a vacuous path interpretation for nonsingular matrices, and `gaussianMatrix_singular_null` establishes the actual Gaussian exceptional-set fact. `exceedanceEvent_measurable` proves Borel measurability of the literal finite-path event.

## All-path and normalization bridges

The proof does not silently identify the source's canonical tie rule with the original universal convention. `GaussianTies` proves that along every admissible path distinct active-column magnitudes cannot tie outside a Gaussian null set. Its polynomial nonvanishing argument explicitly restricts symbolic paths to valid active prefixes. The finite simultaneous assertion gives actual admissible-path uniqueness almost surely, and `gaussianMatrix_admissiblePath_eq_firstPath_ae` identifies every admissible path with the canonical one. `GrowthEvents.exceedanceEvent_ae_selected` therefore equates the actual bad events almost surely, with no combinatorial probability loss.

`rawSchurMax` is literally the numerator of `growth`. On `entryMax A>=1`, growth is bounded by that numerator. The discarded denominator event is retained with its exact probability q^(n^2), where q is the N(0,1) probability of (-1,1), proved to lie strictly between zero and one. `normalized_tail_transfer` adds this term; `FinalFailureScalars` later absorbs it. Neither unit normalization of a random input nor a deterministic lower bound on every input maximum is assumed.

## Stage coverage and adaptive conditioning

`GaussianEliminationTail` tests every k in Fin n and every future active column j>=k. The identity between an active Schur entry and the corresponding canonical elimination row times the original input column is used directly. `PivotFiltration` proves that the elimination rows after k completed pivots depend only on the first k original columns, and that their joint law with column j>=k is the product with a fresh standard Gaussian column. The row cap is imposed only at that stage. A later all-stage cap is used solely for set containment, not to assert a Gaussian conditional law after conditioning on all-stage success.

`GaussianAllRows` covers stages k<=5r by the deterministic row-l1 bound 2^k. For k>5r, it sets t=k-4r>r and uses a four-r-step smoothing window. Thus no late or early stage is skipped, and the general measurable-SVD branch at t<=r is unnecessary. At most n stage events and n^2 stage/column pairs are paid. The resulting Gaussian linear-tail coefficient is explicitly 2n^3.

On a fixed selected-prefix fiber, `GaussianPivotConditioning.fixed_order_lintegral` retains the exact factor q(T)^(n-t) and the Good(T) restriction. Normalized remaining-row restrictions form the actual product law. The exact pivot-order weights sum to one. `GaussianAdaptiveFuture.event_le` transfers intrinsic measurable events using that weighted equality, rather than declaring every order to have mass one. The fixed-T inverse decomposition is chosen inside each fiber; no unproved measurable spectral selector is assumed. `GaussianStageSmoothing` integrates the exceptional retained-row set with its explicit n exp(-x) cost, then the fresh-window cost (n+1)exp(-x).

The selected-block extension is also an actual probability theorem: its reusable spectral-threshold interface is instantiated by the proved append and candidate-row results and exact scalar constants. In the candidate-row argument, the outside-row matrix is fixed before using the Gaussian candidate rows; no law conditioned on those candidates being the next selected rows is presumed. The selected-extension exception is paid once, while the candidate-set union cost remains explicit and is absorbed by the proved threshold accounting.

## Closed final theorem chain and quantifiers

The two probability interfaces `GaussianSpectralRecursion.ExtensionBound` and `FinalAssembly.InverseTailEstimate` are proposition definitions, not axioms. Their presence in intermediate reusable theorems does not survive as an assumption of Solution:

1. `SelectedBlockExtension.extension_bound` supplies the actual extension estimate.
2. `GaussianSpectralProfile.inverse_tail` supplies the simultaneous retained-inverse estimate using `profileConstant beta=max(100*extensionConstant beta,4*beta+4004)`. This constant depends on beta alone, not n, a matrix, or a pivot path.
3. `Unconditional.schurSubpolynomialTail_proved` supplies that concrete estimate to `FinalAssembly.schur_tail_of_inverse_estimate`.
4. FinalAssembly takes arbitrary alpha>0, sets beta=alpha+4 and a=alpha+6, and chooses the fixed constant from `FinalGrowthScalars`. With r=ceil(sqrt(log n)), the exact row threshold is bounded by sqrt(n)*exp(C sqrt(log n)). `FinalFailureScalars` gives a **strict** total failure bound below n^(-alpha), including spectral failure, all smoothing and entry unions, and the denominator exception. The eventual threshold becomes one natural N>=2, followed by **every** n>=N.
5. `Reduction.squareRootUpperBound_of_schurSubpolynomialTail_proved` takes arbitrary eta>0. The subpower threshold is eventually at most n^(1/2+eta). Applying the proved tail with alpha=1 and squeezing against n^(-1) proves the full ENNReal limit.

The six Solution declarations retain exactly the six Challenge signatures: `squareRootUpperBound`, `schurSubpolynomialTail`, `gaussianMatrix_probability`, `exceedanceEvent_measurable`, `admissiblePath_exists`, and `gaussianMatrix_singular_null`. Solution imports Unconditional, not Challenge. The local import closure contains 111 modules and no Challenge import. A supplementary simple source-pattern scan found no hole or custom-axiom declaration patterns in that closure. The authoritative evidence for the transitive proof axioms remains the separate complete audit and exact-name Comparator check; this semantic review does not infer kernel trust merely from absence of those strings.

## Manuscript correspondence and limits of the claim

The manuscript was rechecked at [arXiv:2610.06785v1](https://arxiv.org/html/2610.06785v1), particularly its introduction, Theorem 1.4, Section 5.1, and the proof of Proposition 5.1. Its displayed growth definition uses L and U. An upper bound on U alone would not imply the original all-Schur target. Section 5.1 explicitly develops the stronger all-Schur estimate, and Proposition 5.1's proof takes the needed stagewise entry union. The Lean result follows that argument structure while proving the all-Schur event directly; it does not mislabel an LU-only theorem as the original target.

The implementation includes reviewed alternative supporting estimates and larger universal constants where sufficient. It proves the unchanged original limit and the separately named all-Schur subpower tail, rather than claiming a literal line-for-line formalization of every manuscript theorem or its numerical constants. It makes no matching lower-bound, limiting-distribution, floating-point, arbitrary deterministic-center, or unrelated open-problem claim. No source result is imported as an unproved stochastic axiom.

No mathematical code was edited during this final audit. The approval is bound to the hashes above and the companion support-hash record.
