# TR-06 chart-locus measurability extension

Author: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Original proof attribution: Matthew J. Colbrook. The canonical source statement and attribution remain unchanged.

## Pre-proof approval and exact statements

The root independently approved the following bounded extension before implementation: prove ambient `MeasurableSet` for `regularSet`, `sourceSmoothSet`, and `smoothRegularSet`, for all finite d, mode-size function n, and r, without hypotheses. Prove the three inclusions into `identifiableRealSet` and `smoothRegularSet ⊆ sourceSmoothSet`, reusing existing RankOneCharts results where available. Show relative openness via actual chart targets, not an uncountable union of Borel sets. No full measure, volume equality, chart existence, or genericity consequence is assumed or concluded.

The finished `NLA/TR06/LocusMeasurability.lean` has SHA-256 `f58190fde65b4c1e0d5465e75e86c23c34b8ccc6f46c972f2bba7391fe95b034`.

Exports:

- `regularSet_subset_identifiable`
- `smoothRegularSet_subset_sourceSmoothSet`
- `smoothRegularSet_subset_identifiable`
- `regularSet_relatively_open`
- `smoothRegularSet_relatively_open`
- `measurableSet_regularSet`
- `measurableSet_sourceSmoothSet`
- `measurableSet_smoothRegularSet`

The source-smooth inclusion and relative-openness results are imported from RankOneCharts, without redefining them.

## Logic and verification

A locus point has an actual OpenPartialHomeomorph chart and a source point. That chart's target is an open neighborhood of the point in the full identifiable locus; every target point belongs to the same chart locus via the inverse. This proves relative openness. For each locus the image under measurable subtype inclusion of this relatively open set is exactly the ambient locus, using its proved inclusion into the Borel identifiable set. The inherited SourceSmoothChart gives the smooth-regular to source-smooth inclusion.

Pinned Lean 4.33.1 final compilation exited 0, with no warnings. All eight exports print only `propext`, `Classical.choice`, and `Quot.sound`; all eight LeanCert `#assert_trust kernel` checks passed. No Challenge imports, sorry, admit, custom axioms, native computation oracle, or imported desired conclusion is used.

The actual final command, dependency source and olean hashes, environment paths, timestamp and output are retained in `evidence/LocusMeasurability-receipt.json` and `evidence/LocusMeasurability.log`. This is local development evidence for supporting lemmas, not full TR-06 or Linux Comparator verification.

Canonical source: [TR-06](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/tensor-computations/TR-06/README.md); original proof: [Matthew J. Colbrook manuscript](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/references/colbrook-unclaimed-2026-09-11/manuscripts/TR-06.md).
