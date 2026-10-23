# Actual normalized annular graph charts

The four new `NormalizedGraphCharts*.lean` files are authored by campaign
subagent `solved_inventory`. Their exact hashes and the separately root-authored
`NormalizedGraphDefinitions.lean` are bound in
`normalized-graph-charts-source-lock.json`. The actual graph definition was
read and approved for fidelity before these proof bodies were written. It
retains every ordered decomposition, the genuine Hilbert product norm, the
actual smooth regular input locus, and the open annulus `1/2<‖A‖<3`, which
contains the Gaussian annulus including both boundaries.

The final theorem is
`NLA.Proofs.TR06.NormalizedGraphCharts.exists_normalizedGraph_chart`.
For every actual graph point and positive tensor order it constructs an
`OpenPartialHomeomorph` from the exact `expectedDimension` Euclidean coordinate
space into the **whole** normalized annular graph. The point lies in its
target. The ambient inclusion is C∞, its full derivative is injective at every
source point, and its actual input-projection derivative is injective too.
The returned chart retains a literal formula using an original smooth
decomposition chart on its entire source.

## Proved branch and topology obligations

`NormalizedGraphChartsRadial` constructs every radial multiple of an actual
rank-one summand as a frozen intrinsic rank-one tangent. Frozen regularity
then proves actual linear independence of all summands. Linear independence
excludes proportional normalized summands and proves that the normalized
tuple's permutation orbit has trivial stabilizer.

`NormalizedGraphChartsSeparation` defines an open Voronoi cell about the chosen
normalized tuple against every other finite permutation output. Actual
continuity gives an open coordinate neighborhood where the chosen branch lies
inside that cell and all other branches lie outside. Reordering a genuine
smooth decomposition chart is also proved to give a genuine smooth chart.

`NormalizedGraphChartsBasic` constructs the literal continuous linear input
and output projections in the Hilbert ambient product, proves smoothness of
the actual paired branch map, and aligns a chosen genuine chart branch with
every ordered graph point by actual identifiability.

`NormalizedGraphCharts` restricts the original input chart to the open
separating coordinate neighborhood. Its graph target is explicitly the
intersection of the inverse image of the open input target with the open
output cell. This target is open in the entire graph subtype. Every graph
point in it has some actual ordered decomposition; actual identifiability
permutes this to the chart branch, and the separating cell forces that
permutation to be the identity. This proves the right inverse in the whole
graph, rather than assuming local uniqueness or using only the branch image's
own topology. The inverse is the actual original input-chart inverse composed
with graph input projection. All continuity and smoothness premises are proved.

Input derivative injectivity follows from the exact original branch formula
on an open source neighborhood. Full derivative injectivity follows by the
actual linear input projection and chain rule. No projection rank or local
Lipschitz inverse is inferred merely from setwise injectivity.

## Evidence and scope

All four final source files directly compile with LeanCert `kernel` mode and
their trust assertions. The only printed axioms are `propext`,
`Classical.choice`, and `Quot.sound`.

The separate author checker under `normalized-graph-charts-local-check`
snapshots the full import closure into read-only sources and builds into fresh
output, using only pinned dependency objects. Its consumer also checks the
literal embedded-chart existence statement at C1 order. See its `result.json`
for command counts, compiler version, source/log/object hashes, and the final
live-source stability check. This author evidence is not independent approval;
the campaign verifier performs a separate source review and fresh replay.

The author replay passed: **20 actual source inputs plus its literal chart
consumer, 21 successful commands**, including all four new chart sources.
No project-local objects were reused and all live source hashes remained
unchanged. The result receipt SHA256 is
`605dccee676828ff1008740767a367734afd2236bc555154db1c1270fff9360e`.

Reproduce in a new output directory:

```sh
python3 docs/lean/proofs/TR-06/campaign-2026-10-18/normalized-graph-charts-local-check/check.py \
  --repo-root "$PWD" \
  --lean-bin /absolute/path/to/pinned/lean \
  --dependency-root "$PWD/lean-statements/.lake/packages" \
  --output /private/tmp/tr06-normalized-graph-charts-fresh-replay
```

No earlier frozen model or G2 source, retained support, original mathematical
artifact, problem ID, canonical path, or live/frozen target was edited. These
charts do not prove finite graph volume or finite angular mean by themselves.
