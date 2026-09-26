# Independent review of exact projection-atlas boundary C

Reviewer: `/root/tr06_statement_referee_2`, independent of the six-module proof author. Verdict: **APPROVE at the hashes below**. No mathematical, target-correspondence, or trust change is requested. No candidate source was edited by this reviewer.

| Module | Inspected and rebuilt SHA-256 |
| --- | --- |
| ProjectionAtlasDefinitions | `481f8b0d1ee4b287c211f40732426ae02aade21c6c45cdcf8b0f530c7763607c` |
| ProjectionLinear | `1ae22bcc80dece8bdf062271f0aa069f317b968867e4401b8905eddae73ab1c3` |
| ProjectionCompact | `734f393a019910ae16ef118eb5b0210e5318033dfaf51d01eddd621734c9c5dc` |
| ProjectionTangent | `a0011efb7391841bada86e76836b1996e4f57378b496cf748cf681efa2a10cdd` |
| ProjectionLocal | `6d49880d1d4cb0e780bd20ba044a2f9aa8b855fef7f3c3df158543c1c2d0fa2d` |
| ProjectionAtlas | `0ba7af681082fb8ed6617865db33246490fb8ab9c932915d4f5786ffac7fc5a9` |

The boundary declaration file and the original approved `proposals/ProjectionAtlasBoundary.lean` are byte-identical, with SHA-256 `481f8b0d1ee4b287c211f40732426ae02aade21c6c45cdcf8b0f530c7763607c`. The final theorem directly has type `UniformProjectionAtlasStatement`; the proposition is not assumed or replaced. Its historical Proposed namespace and before-approval comments remain frozen; the separate current README and manifest correctly state that boundary C is proved while algebraic obligation D remains open.

## Exact mathematical review

The hypothesis supplies genuine OpenPartialHomeomorph charts into the subtype of the **whole set S**, C1 input maps, and injective ambient differential everywhere on each chart source. It does not grant a ready-made projection atlas, fiber bound, volume bound, or finite chart cover.

ProjectionLinear obtains an injective row restriction of a rectangular matrix by choosing a basis from its spanning rows and transports the result through exact Euclidean coordinate equivalences. The chosen map really selects m distinct coordinates of the N-dimensional ambient Euclidean space. The family `Fin m ↪ Fin N` is finite because both index types are finite; no infinite arbitrary linear-projection family is substituted.

ProjectionCompact proves compactness of all norm-preserving linear m-frames as a closed operator-norm-bounded subset of a finite-dimensional operator space. An elementary perturbation argument gives a positive inverse bound on an operator neighborhood of each frame. A finite compact subcover and a finite supremum of its bounds produce **one K depending only on m,N**, before a manifold, point, or input chart is selected. ProjectionTangent replaces each input derivative by an orthonormal frame of its actual range and transfers that bound to the inverse coordinate projection composed with the derivative. It therefore removes dependence on the conditioning or scaling of the original parametrization. No unjustified uniform supremum over an arbitrary atlas occurs.

ProjectionLocal applies the inverse function theorem to the square map obtained by composing the selected coordinate projection with an existing input chart. Its inverse followed by the original chart has differential norm bounded by K at the selected point, so the strict derivative estimate gives a local Lipschitz bound 2K after restriction to an open neighborhood. That same dimension-dependent constant is used for every resulting branch. The map remains an actual OpenPartialHomeomorph into S, with open target in S, and projection composed with the inverse chart is exactly the identity on its source.

The local-injectivity conclusion is checked on the **full set `S ∩ ball z epsilon`**. Openness of the chart target in S supplies a relative metric ball. Any two S-points in that ambient ball lie in the target; their chart inverse is their coordinate projection, so equal projections force equal points. This is stronger than merely asserting injectivity along a chosen sheet and has exactly the later fiber-bound meaning needed here.

ProjectionAtlas uses second countability/Lindelof of the S subtype to select a countable open-target cover. Each branch image is Borel by continuous injective image of its open Euclidean source; this uses the applicable standard-Borel injective-image theorem, not an arbitrary continuous-image measurability rule and not prior ambient measurability of S. Disjointing those measurable images preserves their full union S. Each disjoint image piece is projected into a measurable base piece using actual injectivity of the coordinate projection on the enclosing branch image. The inverse image identity is proved in both directions, so restriction has not lost any points. The Lipschitz and projection-right-inverse properties pass to these base subsets.

Grouping by coordinate embedding activates a piece only when its branch's selected embedding equals that group. Thus different `(embedding,index)` pairs have disjoint images even when an index is repeated under several groups: only one group at that index can be nonempty. The final two-sided union identity covers **all S**, not just almost every point or a previously regular subset. Branch images retain membership in the full-S local-injectivity locus.

The empty-S case is proved explicitly with empty base pieces and positive K. For m=0 the linear/frame/IFT arguments remain well-typed and valid; the separate auxiliary theorem also proves that the chart hypothesis makes S discrete and countable. No unjustified finiteness of a zero-dimensional smooth set is inferred. The unused m≤N assumption in the final proof does not weaken the conclusion: actual nonempty chart derivatives already enforce the dimension restriction, while empty S is harmless.

## Independent rebuild and trust

I checked every manifest source hash before copying all six modules into this isolated review directory, then rebuilt them in dependency order using pinned Lean 4.33.1, pinned Mathlib, and pinned LeanCert. All six exited 0 without warnings or errors. Previously built Area dependencies were imported from the author's pinned cache and their source/olean hashes are recorded; this is a fresh rebuild of the six reviewed Projection modules, not a claim to re-review or rebuild unrelated area foundations.

The modules' existing kernel assertions passed. I additionally compiled `ExportAudit.lean`, checking all 18 new public definitions/theorems individually. Every complete transitive axiom closure contains only `propext`, `Classical.choice`, and `Quot.sound`; all 18 explicit `#assert_trust kernel` commands passed. No Challenge import, custom axiom, sorry/admit, native-decide proof, or imported finite-volume/fiber conclusion is used by this contribution.

Actual snapshots, commands, dependency hashes, environment, timestamps, exit codes and logs are in `evidence/receipt.json`, per-module logs, and `evidence/ExportAudit.{json,log}`. Root-level `rebuild.py` and local `audit.py` retain the exact review runners. No Linux Comparator run or complete TR-06 verification is claimed.

The contribution proves the geometric projection-atlas boundary C. Uniform algebraic or semialgebraic fiber cardinality bounds, and their application to the actual TR-06 graph, remain separate obligations. This approval does not establish finite bounded graph volume, the regular full-measure locus, or the finite angular mean. George Stepaniants and the Caltech department affiliation are present in the new modules; the frozen canonical original proof attribution remains untouched.
