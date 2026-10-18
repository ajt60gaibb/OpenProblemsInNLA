# TR-06 angular-slope measurability on the regular locus

Author: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Original proof attribution remains Matthew J. Colbrook. Canonical definitions, target, source statement, and original proof attribution were not modified.

Source: `NLA/TR06/AngularMeasurability.lean`, SHA-256 `a93ab24637efeb22108f9fdd05732d1e0371e1184ade76590f9f21e4718a41d9`.

The root approved the exact hypothesis-free boundary and route before implementation; `ANGULAR-STATEMENT-PLAN.md` records them and the run receipt records its hash. No mathematical change to the approved route was needed.

## Exact proved statements

- `continuousOn_chart_directionalRatio`: for each fixed tangent vector, the frozen quotient of output/input differential Frobenius norms, embedded in ENNReal, is continuous on an actual C1 chart source.
- `lowerSemicontinuousOn_chart_derivativeRatio`: the full supremum over all tangent vectors is lower semicontinuous on that source.
- `lowerSemicontinuous_angularSlope_regularSet`: the actual frozen angularSlope, restricted to the regularSet subtype, is lower semicontinuous.
- `measurable_angularSlope_regularSet`: that same subtype function is Borel measurable.
- `aemeasurable_angularSlope_regularVolume`: for all d, n, and r without hypotheses, `AEMeasurable (angularSlope (d := d) (n := n) r) (regularVolume d n r)`.

## Proof logic

C1 regularity on the open chart source implies continuity of each Frechet differential. At nonzero fixed direction v, injectivity of the input differential makes its applied-vector norm nonzero, so division is continuous. At v=0 both maps vanish and the quotient is the constant zero according to the existing definition. ENNReal.ofReal is continuous. The full arbitrary supremum is lower semicontinuous by the topological supremum theorem; no arbitrary measurable-supremum assertion is used.

MetricSlope's exact chart derivative theorem identifies this supremum with angularSlope at every chart source point. Continuous chart inversion gives lower semicontinuity on the chart target. This target is open in the whole identifiable set, so a witnessed point has ordinary local lower semicontinuity there. Composing with the continuous regularSet inclusion proves lower semicontinuity on the regular subtype. Its Borel measurability, together with already-proved ambient Borel measurability of regularSet, gives almost-everywhere measurability for the Hausdorff restriction exactly defining regularVolume.

## Trust and scope

Final pinned Lean 4.33.1 compilation exited 0 without warnings or errors. All five exports have only `propext`, `Classical.choice`, and `Quot.sound`; all five `#assert_trust kernel` checks passed. No Challenge import, sorry/admit, added axiom, native computation oracle, desired-conclusion hypothesis, genericity, or full-measure premise is used.

The actual final log is `evidence/AngularMeasurability.log`; the command, environment paths, timestamp, source/dependency hashes, plan hash, and scope are in `evidence/AngularMeasurability-receipt.json`. This is local supporting-lemma evidence, not Linux Comparator completion or full TR-06 verification.

In particular, measurability under tensorVolume remains unavailable until a separate full-measure regularity theorem is proved. No induced-volume formula, nullity, normalization bounds, finite angular-link integral, or finite expectation follows from this module alone.

Source references: [canonical TR-06](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/tensor-computations/TR-06/README.md), [Matthew J. Colbrook's original manuscript](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/references/colbrook-unclaimed-2026-09-11/manuscripts/TR-06.md).
