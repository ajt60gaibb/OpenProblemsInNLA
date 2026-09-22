# IE-21 uniform-trimming helper author evidence

Status: stable helper modules, awaiting independent review. This is author evidence only. No additional frozen main target is claimed complete yet.

`UniformTrimmingGeometry.lean` proves the exact Euclidean norm identity for the scaled covariance operator, its nonnegativity, the upper bound by covariance error plus one, and the full absolute inequality `|normalizedOperator A−1|≤covarianceError A` for `n≥1`. No `m≥1` is needed for these deterministic identities under Lean's literal division convention; canonical finite-size applications satisfy both dimensions positive.

Retained submatrix image norms and operator norms are bounded by the full matrix norm. The generic quadratic-form Lipschitz theorem from the stable QuadraticNet module, applied to each retained map's adjoint square, gives the exact squared-norm bound. Comparing actual finite minimizing selections in both directions yields

```
|directionalTrim θ A x−directionalTrim θ A y|
  ≤ 2*normalizedOperator A*‖x−y‖
  ≤ 2*(1+t)*‖x−y‖  when covarianceError A≤t.
```

Both directions are arbitrary unit vectors; empty retained sets, ties, and rank deficiencies are preserved. `goodEvent_of_net` then combines this inequality with actual unit-sphere covering points, the pointwise trimmed deviation and spherical-to-Gaussian discrepancy to conclude membership in the literal frozen all-directions GoodEvent, with exactly the source's constants and floor term.

`UniformTrimmingBound.lean` proves `uniform_trim_probability_of_bounds` for any probability measure on the actual Matrix space. Its covariance-tail, pointwise-tail and population-discrepancy premises are explicit. The complement of GoodEvent is contained in the covariance bad event union the finitely many net bad events. Measure subadditivity and exact sphere-net cardinality give `Bcov+(1+2/δ)^n*Bpoint`. This helper is **not** a conditional substitute for the frozen main target: the future UniformTrimming wrapper must discharge all three analytic input premises using the separate covariance, spherical-trimming and pointwise-trimming proof modules. Those are owned by other agents and were not assumed as axioms or imported from Challenge.

A fresh author rebuild of Definitions, the four stable semantic/net dependencies, both helper modules and the axiom audit passed in eight steps with zero errors/warnings. All 13 new public declaration closures use exactly `propext`, `Classical.choice`, `Quot.sound`. No implementation imports Challenge or uses sorry, admit, native_decide, run_tac, or a custom axiom. Source/dependency/log hashes and the exact external build path are in `helper-author-evidence.json`.

All four frozen boundary hashes were rechecked unchanged. The previously reviewed MatrixSemantics/FiniteTrimming modules were not edited. No canonical status, Solution, shared metadata, or other proof source was changed. Complete-target independent review, actual Comparator and LeanCert kernel verification remain pending.

Original argument: Matthew J. Colbrook. Formalization credit: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, with no contact email added.
