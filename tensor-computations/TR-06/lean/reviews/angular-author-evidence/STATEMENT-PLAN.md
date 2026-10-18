# Pre-approved angular measurability boundary

Root independently approved this exact theorem before implementation:

```lean
theorem aemeasurable_angularSlope_regularVolume
    (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    AEMeasurable (angularSlope (d := d) (n := n) r) (regularVolume d n r)
```

There are no genericity, full-measure, positive-dimension, or finite-slope hypotheses. Definitions remain unchanged. Supporting statements will show lower semicontinuity of the intrinsic derivative ratio on every actual C1 chart source, lower semicontinuity of angularSlope on the regularSet subtype, and Borel measurability on that subtype.

For each fixed tangent vector v, C1 regularity gives continuity of both ambient differentials on the open chart source. If v is nonzero, injectivity of the input differential makes its norm denominator nonzero at every source point, so the real quotient and ENNReal.ofReal quotient are continuous. For v=0 the ratio is identically zero. The supremum of these continuous ENNReal functions is lower semicontinuous, without needing a countable supremum.

The exact previously kernel-checked MetricSlope theorem identifies that derivative-ratio function with the intrinsic slope on every chart source. The actual OpenPartialHomeomorph inverse transports lower semicontinuity to its open chart target in the whole identifiable set. At every point of regularSet some such target is a neighborhood, yielding lower semicontinuity and hence Borel measurability on the regularSet subtype. The already-proved Borel measurability of regularSet then gives AEMeasurable for its Hausdorff-measure restriction, exactly regularVolume. Topological lower semicontinuity, not an uncountable union of measurable sets, justifies the passage across all charts.

This proves no angular-slope measurability for tensorVolume, regular full measure, volume equality, finite link integral, or finite expectation. Those require separate theorems.

Authorship: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Original mathematical proof remains attributed to Matthew J. Colbrook.
