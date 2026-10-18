# SP-11 relabeling and coefficient expansion — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 17 October 2026.
**Verdict: approve GreedyRelabel, MinorBasis, and GardenExpansion at the hashes
below.** I did not implement these three modules. I authored MonomialProducts
and therefore make no independent mathematical-review claim for that module;
its independent review is assigned to other agents. The runtime audit below
covers all eleven support modules without claiming a complete SP-11 proof.

| New module under `lean-statements/NLA/Proofs/SP11/` | SHA-256 |
| --- | --- |
| `GreedyRelabel.lean` | `7e2cfe0f41f619bae813d77469bba03c80dac43885e47c652e7e59b0fd09ee0a` |
| `MinorBasis.lean` | `98e16d2efb9f604e6df3c2e86f3a0544d9f21b12a91808a9051673d5a142dab6` |
| `GardenExpansion.lean` | `1784dd6cfe2ae886781bd21599998439b5572f288287ec4df95cd4ba99d5d4ae` |
| `MonomialProducts.lean` (runtime audit only) | `734d5fa56b38d4b082b82b2312b668fa64cc88ee16dac3e12e931c47680ee915` |

The original seven support modules and frozen SP-11 statement remain at their
previously reviewed hashes. All sources and actual commands are recorded in
`sp11-eleven-gates-review/result.json` and its frozen-source directory.

## GreedyRelabel

`OrderedGreedy` uses the literal earlier prefix `Finset.Iio i` and compares
the actual earlier-nonneighbor counts. `minimumDegree_comap` uses the graph
isomorphism of a genuine vertex permutation. Pattern transport reindexes both
axes by the same equivalence and proves the off-diagonal iff using its
injectivity. Reverse transport uses the inverse permutation, and the rank is
unchanged by this simultaneous reindexing.

The count transport proves equality with the actual image of each finite
prefix. `prefix_image_of_listing` then identifies that image exactly with the
chosen duplicate-free list prefix. The constructed permutation is obtained
from the full greedy listing, not an arbitrary supplied ordering oracle.
Consequently `exists_orderedGreedy_comap` supplies the actual naturally greedy
relabeled graph, dimension bound `d + MinimumDegree ≤ n`, and all contraction
arities strictly below `d`. Positive `n` handles the last-index boundary.

`priorNonneighbors_filter_lt_length` correctly identifies the sorted input
list's count below an earlier index with the later vertex's nonneighbor count
at that stage. Its `i ≤ j` restriction ensures the earlier prefix lies inside
the later one. The resulting strict insertion bound applies to both an actual
nonneighbor child and an earlier adjacent inserted root. It does not use the
source's invalid unrestricted later-root version of that inequality.

The final theorem applies an explicitly quantified polynomial noncancellation
premise to this relabeled graph, specializes its actual polynomial vectors,
and transports the real matrix witness back. Minimum degree and rank
invariance preserve the exact original weak nullity bound. This completes the
ordering/transport bridge conditionally; the noncancellation premise remains
unproved and visible in the theorem type.

## MinorBasis

Different increasing coordinate tuples of the same finite length cannot have
one range contained in the other: the induced injective self-map of `Fin r`
would be surjective, forcing equal ranges and hence equal strictly increasing
tuples. Thus a differing tuple has an omitted coordinate. The zero-length case
is handled correctly because no distinct empty tuples exist.

On matching ordered coordinate basis vectors, the selected coordinate matrix
is exactly the identity, so the determinant is one. On a different subset,
the omitted coordinate gives a literal zero row, so the determinant is zero.
Finite summation therefore reads an arbitrary weighted-minor coefficient
exactly. The universal polynomial form consequently reads the actual shared
`MvPolynomial.X (name s)`. The argument works over any commutative ring,
including degenerate dimensions, and introduces no genericity hypothesis.

## GardenExpansion

The coordinate expansion applies actual multilinearity to the standard basis
decomposition in every slot. The finite sum is over one color per slot, and
the scalar coefficient is the product of the corresponding vector coordinates.
The empty arity and empty coordinate endpoints follow from the genuine finite
sum/product formulas.

The contraction expansion curries its fixed first output basis vector and
expands only the remaining inputs. It does not sum the output coordinate a
second time. `polynomialLSS_coordinateExpansion` unfolds the reviewed
well-founded recursion and proves one exact expansion step of that same
polynomial, with the same vertex-indexed coefficient family at every recursive
occurrence. It is not yet a global tree-coloring expansion.

The permutation lemma uses Mathlib's actual alternating-form permutation sign.
Combined with the ordered basis-coefficient identity, each injective color
tuple presented in sorted-permutation form contributes the signed shared
variable. A noninjective color tuple yields zero by alternation. No fresh
occurrence variables, sign-free determinant replacement, or unproved
faithfulness fact is introduced.

## Reuse, runtime evidence, and limits

The new modules use existing Mathlib graph isomorphism, matrix rank, finite
permutation, determinant, standard-basis, and alternating multilinear APIs.
Their wrapper declarations keep the actual graph and tensor semantics exposed.
I found no blocking mathematical, fidelity, API, or scope issue in these three
reviewed modules.

The fresh eleven-module closure build passed all **14 Lean commands** in a new
private prefix, compiling every local source dependency from its frozen bytes.
The independent audit consumer covered **85 explicitly declared constants,
including 61 theorem exports**. Every theorem passed a theorem-kind check;
every constant passed LeanCert `#assert_trust kernel`; printed transitive
axioms were only subsets of `propext`, `Classical.choice`, and `Quot.sound`.
All ten dependency pins and tracked sources passed before and after, and all
frozen owned sources remained unchanged during the run.

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-eleven-gates.py
```

The machine result, raw logs, consumer and frozen sources are in
`sp11-eleven-gates-review/`. This is local macOS elaboration/kernel-trust
evidence using pinned compiled dependencies. The earlier Linux receipt covers
only its seven-module snapshot and statement identities, not these additions.
The full shared-variable coloring expansion, admissible canonical coloring,
classwise unique-exponent/noncancellation proof, and unconditional SP-11
assembly remain outside the established scope. No full-target status change
is supported by this report.
