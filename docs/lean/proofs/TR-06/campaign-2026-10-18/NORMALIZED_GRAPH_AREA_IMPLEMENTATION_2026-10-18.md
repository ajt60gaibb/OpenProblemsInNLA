# Actual normalized graph weighted area

The six new `NormalizedGraphArea*.lean` sources are authored by campaign
subagent `solved_inventory`. Their final bytes are recorded in
`normalized-graph-area-source-lock.json`. This author report and its source
replay are not independent mathematical approval. The campaign verifier
reviews these sources and replays their import closure separately.

The main theorem
`NLA.Proofs.TR06.NormalizedGraphArea.annular_angularIntegral_le_graphVolume`
proves, for positive tensor order, that the literal `angularSlope` integral on
`HomogeneousGaussian.annulus (smoothRegularSet d n r)` is at most the
`expectedDimension` Euclidean Hausdorff measure of the actual
`normalizedAnnularGraph d n r`. It does not assume annular integrability.

`actualAnnularBounds_of_graphVolume_lt_top` therefore returns both finite
actual annular input volume and finite actual annular slope integral from one
explicit premise: finite `expectedDimension` Hausdorff volume of that literal
graph. The separate algebraic/projection gate must prove this premise before
the full target can be claimed.

## Exact area and measurability obligations

`NormalizedGraphAreaVolume` proves that the literal input projection from the
Hilbert product ambient space is 1-Lipschitz. Every smooth annular input has an
actual ordered decomposition and hence a point of the actual graph. The
Lipschitz Hausdorff image inequality gives input annular volume at most graph
volume. It uses the induced dimension throughout.

`NormalizedGraphAreaJacobian` differentiates the exact paired graph map,
retaining the actual Hilbert norm. The proved chart-operator equality for
`angularSlope` and the retained rectangular graph-Jacobian inequality give
`slope * input Jacobian <= graph Jacobian`. Actual graph chart formulas on
open source neighborhoods transport this inequality to the constructed graph
charts. A global Borel function equal to the actual slope on the smooth locus
is constructed by measurable extension from the regular-locus subtype.
Global measurability of arbitrary exceptional-point slope values is not
assumed.

`NormalizedGraphAreaWeighted` proves the weighted rectangular area formula
for an actual C1 injective immersion on an open chart source and any
measurable subordinate subset. A global measurable extension of the map is
constructed from its continuous restriction. Its derivative on the relevant
source is proved by eventual equality. The actual Jacobian is continuous on
the source and hence measurable for the restricted measure. These discharge
the retained weighted-area theorem's hypotheses.

`NormalizedGraphAreaPartition` bundles actual graph charts with the original
smooth decomposition chart and literal branch formula. Input images are
measurable and relatively open in the actual sampling set. A Lindeloef
subcover produces a countable input cover, and `disjointed` produces a
measurable pairwise disjoint partition of the entire smooth annulus. Each
partition piece lies in one actual chart's input image; no partition by the
ambient dimension or assumed global chart is used.

`NormalizedGraphAreaPiece` pulls each input piece back to its actual graph
chart source. It proves the exact input-image equality, measurability of both
the parameter subset and its actual graph image, and the weighted-area bound
on that piece. The graph Jacobian uses the genuine ambient inclusion, while
the input Jacobian uses the original smooth input chart; their equality with
the literal projection derivatives follows on an open source neighborhood.

`NormalizedGraphArea` sums these inequalities. The selected graph images are
pairwise disjoint because their literal input projections lie in disjoint
input pieces. They are measurable subsets of the whole graph. Countable
additivity therefore bounds the sum of their volumes by graph volume. The
empty-annulus case is handled directly.

## Source preservation and evidence

`normalized-graph-area-prior-source-preservation.json` rechecks all 58
retained supports, the twelve earlier authored model modules, the five
actual algebraic-locus modules, and the four graph-chart modules plus the
separately root-authored actual graph definition. Every earlier frozen hash
still matches. No live or frozen target, original mathematical artifact,
problem ID, or canonical path was changed.

Each final new source directly compiles under LeanCert `kernel` mode and
asserts the kernel trust of its declarations. The printed main-theorem axioms
are only `propext`, `Classical.choice`, and `Quot.sound`.

The checker in `normalized-graph-area-local-check/check.py` snapshots the full
38-source import closure into read-only files and builds it plus a literal
annular-bounds consumer into fresh output using only pinned dependency
objects. It refuses to reuse existing project output objects. Its final
`result.json` records every source, log, and object hash, exact compiler
version, command results, and a live-source stability comparison.

Reproduce with a new output directory:

```sh
python3 docs/lean/proofs/TR-06/campaign-2026-10-18/normalized-graph-area-local-check/check.py \
  --repo-root "$PWD" \
  --lean-bin /absolute/path/to/pinned/lean \
  --dependency-root "$PWD/lean-statements/.lake/packages" \
  --output /private/tmp/tr06-normalized-graph-area-fresh-replay
```

The receipt is pending while its initial fresh source replay runs. This
report claims the exact area reduction above, not finite graph volume or the
full intrinsic target.
