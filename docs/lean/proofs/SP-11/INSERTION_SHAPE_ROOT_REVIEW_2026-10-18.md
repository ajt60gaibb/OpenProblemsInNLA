# Independent insertion and actual-occurrence review

Reviewer: `/root`, OpenAI Codex AI agent, 18 October 2026. Verdict:
**APPROVE for the stated support results.** I did not implement these five
modules. This review does not assert the full SP-11 theorem.

`PriorInsertion` uses the actual sorted predecessor lists. Its insertion
position counts precisely the old entries below the inserted label. The
adjacency premise ensures that the inserted root is absent from the old
nonneighbor list, so the augmented length is exactly one larger. Counting
smaller elements identifies the inserted slot, and strict monotonicity plus
equality of ranges identifies every remaining slot with `succAbove`. This
includes insertion at either end and does not replace graph labels.

`AugmentedColors` is the literal `Fin.insertNth` reindexing of the cap-first
tuple. The two slot identities and injectivity proof cover the cap/child and
child/child cases. No new color or occurrence variable is introduced.

`CanonicalPair` joins the actual early and late trees with one shared cap.
The early tree uses ordinary sibling positions, the late root skips the cap
position, and all lower subtrees use ordinary positions. The greedy count
inequality supplies the early cap bound, while the actual arity bounds make
every color inhabit `Fin d`. Local injectivity gives a nonzero product of
alternating signs. This also covers equal roots: their insertion count is
the entire predecessor-list length. Sign nonvanishing alone is correctly
separated from cancellation in the Gram polynomial.

`CanonicalOutputs` proves exact output values at every ordinary child
occurrence, the skipped values at the exceptional top root, and ordinary
values below that root. Its occurrence maps retain the dependent outer path;
the root-arity cast only transports a proved equality of natural numbers.

`DoubleOccurrenceShape` supplies the actual child map on each side of the
pair, proves the parent-input/child-output identity, and splits the literal
incident sum into output plus actual children. Equal exponent histograms
therefore give the exact filtered class sums used by the generic recovery
theorem. Strict child-label descent is proved from the actual recursion.
The final theorem still explicitly requires the local blocker/tie shape;
it neither assumes the desired matrix nor hides a noncancellation oracle.
Coloring extensionality converts the recovered outputs to equality of the
actual finite summand indices.

I read the complete sources and independently compiled each unchanged file
with the pinned Lean 4.33.1 runtime. Source kernel assertions passed; printed
axiom closures were subsets of `propext`, `Classical.choice`, and `Quot.sound`.
This is supporting macOS evidence using previously built pinned imports,
not a fresh dependency-closure audit or Linux Comparator run. Exact hashes,
return codes and raw compiler logs are in
[`insertion-shape-root-evidence-2026-10-18/result.json`](insertion-shape-root-evidence-2026-10-18/result.json).
