# TR-06 actual model correspondences and Gaussian transfer

These twelve new support modules preserve the intrinsic statement and all 58
retained source files. `model-authored-source-lock.json` binds the exact bytes;
`model-retained-source-preservation.json` checks every retained copy against the
published receipt. The implementation author is campaign subagent
`solved_inventory`. This report is an implementation account and author-build
receipt, **not** independent approval of these sources.

The original problem number, canonical path, original mathematical artifacts,
the live intrinsic statement, and its frozen review are unchanged. None of these
modules claims the full `Target`.

## Proved correspondences

- `ModelSemantics` proves actual rank-one, decomposition, exact-rank,
  unordered-summand, complex genericity, dimension, and Gaussian-weight
  equivalences. The opposite permutation orientations are handled explicitly.
- `ModelNormalization` and `ModelTupleNormalization` differentiate the actual
  individual normalization and tuple map. The output remains the exact product
  Frobenius norm on `EuclideanSpace`, without a maximum-norm substitution.
- `ModelOuterDerivative` differentiates the genuine outer product.
  `ModelTangent` proves both directions between the frozen intrinsic factor
  variations and the actual pivot-decoder derivative range. `ModelRegularity`
  identifies frozen addition-derivative regularity with actual pivot-sum
  derivative injectivity.
- `ModelChartDerivative` proves that every intrinsic tangent tuple at a genuine
  smooth chart point is the actual tuple of summand derivatives in one chart
  direction. This uses the bijective full pivot-coordinate derivative, actual
  reconstruction near the chart point, and the exact parameter dimension.
  It derives `smoothRegularSet ⊆ SmoothIdentifiable` pointwise.
- `ModelAngular` proves equality of the frozen intrinsic `AngularCondition`
  with the retained order-free `angularSlope` at every actual smooth chart
  point. The proof ranges over every alternative decomposition in the frozen
  supremum, uses actual identifiability to permute it to the chart branch, and
  uses the actual product-space permutation isometry. It also identifies
  `sourceAngular` there.
- `ModelCone` constructs a genuine scaling homeomorphism of the entire
  identifiable sampling space and an actual scaled embedded smooth chart.
  Thus the smooth regular locus is a measurable positive cone, avoids zero
  for positive rank, and has the actual degree minus one angular homogeneity.
  Angular measurability on its Hausdorff-restricted volume follows from the
  retained C1-locus measurability result by measure monotonicity.
- `ModelMeasure` proves exact intrinsic-volume and Gaussian-integral transfer
  from the explicit full-measure smooth-chart conclusion. It does not assume
  pointwise equality of the two regular loci at exceptional points: the
  inclusions `smoothRegular ⊆ intrinsic ⊆ sampling` and restriction identities
  suffice.
- `ModelGaussian` instantiates the independently authored dyadic Hausdorff-cone
  integration theorem with the **actual** smooth regular locus and actual
  angular slope. Its remaining premises are precisely full measure of that
  locus, positive finite literal annular Hausdorff volume, and a finite literal
  annular angular integral. These are intermediate obligations, not added
  assumptions of the frozen final theorem.
- `ModelMeasureRestoration` restores the C1/source volumes, normalizers, and
  normalized input laws, proves probability from actual positive finite
  normalization, proves slope/source-angular a.e. measurability, and proves the
  exact normalized expectation formulas.

## Kernel evidence and reproduction

Every source was directly typechecked under LeanCert `kernel` mode. Its
explicit trust assertions pass; the reported axioms are only `propext`,
`Classical.choice`, and `Quot.sound`.

`model-bridges-local-check/result.json` records a separate immutable-source,
fresh-output replay of the first eleven modules through `ModelGaussian`:
27 actual source inputs plus a consumer, **28 successful commands**. No
project-local objects were reused. Pinned Mathlib/LeanCert dependency objects
were reused. The result receipt SHA256 is
`b9f5dcc3f4adca1a27ce5bdbdffb3d9919d71afa5ec7c11755379af1d20b7b64`.
`ModelMeasureRestoration` was added afterward and directly compiled separately;
it is not silently included in that 28-command count. The independent verifier
performs its own source review and separate fresh replay.

From a checkout containing the frozen source files, replay into a new output
directory (the checker deliberately refuses prior local objects):

```sh
python3 docs/lean/proofs/TR-06/campaign-2026-10-18/model-bridges-local-check/check.py \
  --repo-root "$PWD" \
  --lean-bin /absolute/path/to/pinned/lean \
  --dependency-root "$PWD/lean-statements/.lake/packages" \
  --output /private/tmp/tr06-model-bridges-fresh-replay
```

Use the pinned Lean 4.33.1 compiler and the repository-pinned dependency cache.
The checker copies and hashes the import closure, makes the snapshot files
read-only, builds only into its new output directory, logs all commands, and
checks that live source hashes remained stable during the replay.

The actual algebraic good-locus/full-measure and annular geometric bounds are
separate campaign gates. The model reduction does not establish those bounds
or a completed TR-06 proof by itself.
