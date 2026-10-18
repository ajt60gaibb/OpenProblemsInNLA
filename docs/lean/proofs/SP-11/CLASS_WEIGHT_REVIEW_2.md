# Independent review 2: class histogram weights and local color bounds

Reviewer: `/root/solved_inventory`, independent AI agent, 17 October 2026.
Verdict: **APPROVE HistogramRigidity, ColorBounds and ColorWeights at the hashes below, within their explicit helper scope. No graph-specific noncancellation or full Target proof is certified.** I did not author or edit these modules.

I read their complete sources and independently ran fresh pinned Lean elaborations. The actual output, successful return codes and unchanged-source hashes are retained in [new-gates-review-2-evidence/result.json](new-gates-review-2-evidence/result.json) with individual logs. All selected LeanCert kernel checks passed and axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`. These are local development checks, not isolated Linux Comparator results.

`HistogramRigidity` applies the actual natural-semiring linear combination map to equal exponent histograms. Thus equal histograms preserve any additive natural-valued variable weight, including weights supported in a single vertex class. A per-occurrence one-sided lower bound plus strict improvement at one occurrence would strictly increase the whole finite sum; equal totals therefore force equality at each occurrence. The proof remains valid with repeated variable names and empty occurrence sets. It explicitly requires the one-sided bounds and does not manufacture them from aggregate equality.

`ColorBounds` is a pigeonhole argument at a single injective incident tuple. If other slots already cover every color below a threshold, the distinguished color cannot be below it. Its sibling corollary uses only genuinely earlier fixed sibling colors; its output corollary uses precisely the known inputs `0,...,k-1`. No completeness of an arbitrary garden coloring or unproved greedy property is assumed.

`ColorWeights` takes the sum of every coordinate in an actual increasing subset, then uses the proved sorting permutation to identify it with the original incident-tuple sum. Its variable weight filters by the original vertex label. Applied to the actual single-node colorExponent, the natural linearCombination reads exactly that node's incident sum in the matching class and zero elsewhere. Injectivity is an explicit premise because repeated-color terms have zero exponent by convention. The arity argument is the full number of incident slots; callers with a tree's child arity must pass `arity v + 1`.

The remaining graph-specific obligations are obtaining injectivity from actual nonzero term coefficients, summing these weights over the real finite occurrence model, deriving the pointwise lower bounds from earlier fixed classes, and reconstructing every conduit from equal class sums. None is already a full SP-11 witness in these three modules. Canonical sources, permanent IDs, originals and frozen targets were unchanged.

| Reviewed source | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP11/HistogramRigidity.lean` | `93d252876b92c2ab6e72033ffe982f92e88bc93f265d24f2832be6273bb110ca` |
| `lean-statements/NLA/Proofs/SP11/ColorBounds.lean` | `0f3e13a608d409542a5548571dbf71c507f034460edcaf282db12bead71ee3d8` |
| `lean-statements/NLA/Proofs/SP11/ColorWeights.lean` | `fa45af958015992d5a01ad224e4318ee7e65b20e7a8390fb5c3227f2ee8dbf93` |
