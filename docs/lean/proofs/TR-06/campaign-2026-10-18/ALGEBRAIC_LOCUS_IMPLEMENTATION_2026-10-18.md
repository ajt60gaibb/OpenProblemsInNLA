# TR-06 actual algebraic regular-locus construction

The five frozen new sources in `algebraic-locus-authored-source-lock.json`
implement the actual G2 gate. They preserve all 58 retained sources, the
intrinsic live/frozen target, canonical ID, paths, and original artifacts.
Their author is campaign subagent `solved_inventory`. This implementation
report and its author compilation receipt do not count as independent approval
of the author's own sources.

## Exact conclusions

The three generic conclusions require only positive mode count, positive mode
sizes, `r≥2`, and the original retained `GenericComplexIdentifiable`. These
follow from the full problem's admissibility hypotheses. Actual equivalence of
that genericity predicate to the frozen intrinsic one is proved separately in
`ModelSemantics`.

- `AlgebraicLocusFullMeasure.generic_smoothRegular_full_measure` proves
  `∀ᵐ A ∂tensorVolume d n r, A ∈ smoothRegularSet d n r`.
- `AlgebraicLocusFullMeasure.generic_smoothRegular_nonempty` constructs an
  actual real point with a genuine smooth decomposition chart.
- `AlgebraicLocusPositiveVolume.generic_smooth_annular_volume_pos` proves
  strict positivity of the literal expected-dimensional Hausdorff measure of
  `smoothRegularSet ∩ {A | 1≤‖A‖ ∧ ‖A‖<2}`.

No properness, unramifiedness, Jacobian-rank, real-rank, nonzero-polynomial,
chart-existence, or nullity certificate remains a hypothesis of these three
theorems. They do not prove a finite annular volume upper bound or a finite
annular angular integral, and do not assert the full TR-06 target.

## Proof route and fidelity

`AlgebraicLocusPolynomial` extends the retained complex-polynomial real-zero
nullity theorem from `Fin m` coordinates to arbitrary finite coordinates and
their actual Euclidean-space volume. Coordinate changes are explicitly volume
preserving. It proves the actual real Segre sum map smooth by its evaluated
coordinate polynomials.

`AlgebraicLocusPullback` starts with a nonzero pullback to the genuine integral
Segre source algebra. Multiplying the literal raw-factor polynomial by all
prescribed anchor variables produces an actual nonzero evaluation with every
summand pivot nonzero. The evaluated source/addition-character identity gives
an actual complex decomposition on which the ambient polynomial is nonzero.
The retained exact representation theorem then proves nonzero pullback in
**every** prescribed exact-dimensional Segre pattern.

`AlgebraicLocusNull` proves a Lebesgue-null polynomial exceptional set in each
Segre source. The retained C1 null-image theorem sends it to an expected-
dimensional Hausdorff-null tensor image. Every actual length-r decomposition
has some nonzero pivot at each nonzero summand, so the finite family of all
pivot patterns covers the bad decomposable tensors. The resulting conclusion
is actual sampling-volume nullity. It uses neither ambient-dimensional
Lebesgue nullity nor homogeneity of the exceptional polynomial. The retained
real polynomial-density theorem also constructs actual real decompositions
off this exceptional set.

`AlgebraicLocusFullMeasure` multiplies the root author's actual proper,
identifiable ambient denominator with the other author's actual unramified
real-pivot-derivative denominator. Nonvanishing of their product in the actual
source algebra is proved. On that genuine open set, all hypotheses of the
retained full-target-topology proper-immersion chart theorem are supplied by
proved results. The just-proved sampling nullity removes its complement. A
real good decomposition lies in the exact identifiable good base and therefore
gives an actual regular witness.

`AlgebraicLocusPositiveVolume` rescales that nonzero actual witness to norm
3/2 using the proved scaled embedded chart. At this point a continuous linear
left inverse of the chart's injective derivative gives a locally invertible
projection into its k-dimensional coordinate space. Its nonempty open image
has positive k-dimensional volume. A zero k-dimensional Hausdorff measure of
the original chart image would force that projected image to be null by the
actual Lipschitz Hausdorff bound, a contradiction. This obtains positivity in
the induced dimension `k=expectedDimension`, with no ambient-volume shortcut.

## Authorship and verification boundary

The actual proper/finite good-base sources are authored by the root agent;
the actual unramified and real-pivot differential sources are authored by
`fr05_statement`. Those sources and the 58 retained sources are dependencies,
not claims of new authorship here. The previously separate independent
statement reviews remain unchanged.

All five final sources directly compile under LeanCert kernel mode with their
explicit trust assertions. Every printed axiom set contains only `propext`,
`Classical.choice`, and `Quot.sound`.

The separately retained `algebraic-locus-local-check` checker snapshots the
entire actual import closure of `AlgebraicLocusPositiveVolume` and
`ModelMeasureRestoration`, makes source snapshots read-only, and builds into
fresh isolated output. It never reuses project-local objects; only the pinned
Mathlib/LeanCert dependency objects are reused. The original eleven-model
28-command replay remains preserved separately. The final status and exact
source/log/object hashes are in that checker's `result.json`.

The frozen replay passed: **80 actual source inputs plus the consumer,
81 successful commands**, including all twelve authored model modules and
all five authored G2 modules. Live source hashes remained unchanged. The
result receipt SHA256 is
`c2cd49c72f0a8fa16c80ffdae588b9022b3d4560ccbc045418e9e307496564e7`.

To reproduce, use a new output directory:

```sh
python3 docs/lean/proofs/TR-06/campaign-2026-10-18/algebraic-locus-local-check/check.py \
  --repo-root "$PWD" \
  --lean-bin /absolute/path/to/pinned/lean \
  --dependency-root "$PWD/lean-statements/.lake/packages" \
  --output /private/tmp/tr06-algebraic-locus-fresh-replay
```

The independent verifier conducts its own source review and fresh replay.
