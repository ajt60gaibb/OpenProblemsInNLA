# SP-11 support gates — independent final source review

Reviewer: `/root/lean_verification`, independent Codex AI agent, 17 October
2026. I did not implement these modules. **Verdict: approve these seven support
modules at the hashes below. This does not certify an unconditional SP-11
proof.** The earlier Gram/polynomial review remains valid for its unchanged
source bytes.

## Frozen source and execution

All paths below are under `lean-statements/NLA/Proofs/SP11/`.

| Module | SHA-256 |
| --- | --- |
| `AlternatingContraction.lean` | `5470ac391cec624ed4a11bc3fe5ff271dccbc2446db8a4aac44053c01407b6ca` |
| `AlternatingPolynomial.lean` | `d1ece1a3defce0f4cae49af934548c2bad20d7273a7df91b29111787d8c876f7` |
| `GramBridge.lean` | `e3ff1bd936a820a58ac005dd50487464e8d5a56b231268bd1e1b5d9936ab1aed` |
| `GreedyOrdering.lean` | `89dfbb2d808ea85cf2a68e4e1790665a40ed3c55a860abd23309801ce0f19c21` |
| `PolynomialFaithfulness.lean` | `e1214cdc4072420c86006538cc9465bf29e9dda5a5e72dd1a0eb9ace4fd7928c` |
| `PolynomialLSS.lean` | `12f18f17f1d74e03cd14a9b42bf9dfc45f67a0239f5cc8e0e405f45a267efd66` |
| `UniformLSS.lean` | `485ffa227d00a09bc93b8fe244815e8e7dc912064edffa6cadc8f09fc52bd431` |

The frozen imported statement remains
`NLA/Statements/SP11.lean`, SHA-256
`7de112a24cb0b78894d495b840a77a58572cce574d5d77eda15381410c65b131`.
Its statement-checker source remains SHA-256
`8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37`.

The independent checker froze these sources, compiled their complete local
closure from source into a new private prefix, and ran a separate consumer
covering **57 explicitly declared public constants, including all 35 theorem
exports**. Every theorem was required to be a theorem constant; every constant
passed `#assert_trust kernel` and retained its `#print axioms` output. The only
transitive axioms are subsets of `propext`, `Classical.choice`, and `Quot.sound`.
All ten manifest dependency revisions and tracked-source cleanliness passed
before and after. All ten Lean commands succeeded, and every frozen source
remained unchanged throughout the run.

## Mathematical and scope review

**Alternating contraction.** `contractionFunctional` is the actual linear
functional obtained by placing its variable in the first slot of an alternating
form. `alternatingContraction` takes its coefficients on the standard coordinate
basis. Expanding an arbitrary vector in that basis proves the exact bilinear
dot-product identity over any commutative ring. Substitution of an input vector
then creates two equal slots, so alternation gives zero. This does not require
an inner-product positivity assumption, division by a factorial, nonzero
dimension, or linear independence. Arity zero/empty coordinate cases are
handled by the finite types; no nonedge or faithfulness fact is inferred yet.

**Polynomial alternating forms.** Each increasing coordinate tuple selects a
literal determinant minor using Mathlib's `Matrix.detRowAlternating`. The
displayed entry theorem confirms the exact row/column convention. Summing those
forms against coefficients gives the advertised finite sum, including the
empty-tuple and unavailable-arity cases. Polynomial forms use actual
`MvPolynomial.X` indeterminates and the same alternating contraction. A general
`name` function need not be injective; this module correctly proves only the
formula and orthogonality. Independence is supplied by the vertex-tagged
construction below, not by an unstated premise here.

**Greedy order.** `localNonneighbors` counts actual nonadjacent vertices in a
prefix finset. A complete duplicate-free listing from empty prefix therefore
uses ordinary earlier nonneighbors, with no self-neighbor counted. Strong finite
induction chooses a real minimizing remaining vertex and removes it, giving a
complete greedy list and a genuine vertex-order equivalence. The stagewise
inequality compares the chosen vertex with a still-listed vertex. Monotonicity
in the prefix gives the source's nondecreasing counts. The zero-based
`nonneighborPosition` is explicitly identified with filtered-list length for
duplicate-free listings, and the bound applies to an earlier vertex before
insertion; it does not use the source's invalid unrestricted later-vertex case.

At the last stage, all other vertices occur in the prefix, so the exact count
identity is `k_last + 1 = n - degree(last)`. Consequently the selected dimension
satisfies `d + minDegree ≤ n`, and every earlier count is strictly below `d`.
The positive-`n` premise ensures the last index exists. The new
`greedyListing_length` theorem supplies the exact listing cardinality. These are
combinatorial ordering/dimension results only, with no assertion that an
arbitrary tensor choice is faithful.

**Uniform recursion.** `priorNonneighbors` is the sorted finset of exactly the
strictly earlier nonneighbors in the fixed numeric vertex order. Every recursive
argument is proved smaller in its natural label; the well-founded fixpoint and
its unfolding theorem supply a genuine finite construction. Substitution into
the contraction identity proves orthogonality to each predecessor. For a
distinct nonedge, one endpoint is later; graph symmetry and commutativity of
the bilinear pairing cover the reversed case. No diagonal or edge is silently
forced to be nonzero, and no probabilistic or genericity assumption appears.

**Actual polynomial recursion.** `LSSVariable` is the dependent sum of vertex
labels and their increasing coordinate subsets. `Sigma.mk j s` gives a
different indeterminate to each distinct vertex/coefficient pair, while every
recursive occurrence of one vertex uses the same family. Thus the construction
retains the shared-variable cancellation problem in Hall's proof. It does not
replace occurrences by independent tensors. `polynomialLSS_nonedge` is the
literal zero Gram polynomial of this concrete recursion. The matrix-existence
corollary uses the previously reviewed simultaneous real evaluation and Gram
rank bound, with explicit `hd` and diagonal/edge nonvanishing premises. It does
not discharge those premises.

The Gram and polynomial-specialization modules retain the mathematical checks
in `SP11-GRAM-POLYNOMIAL-INDEPENDENT-REVIEW.md`. In particular the full original
off-diagonal iff, unrestricted diagonal, ordinary real symmetry, weak nullity
bound, all positive dimensions, and all finite graphs remain the target.

## Reuse and remaining obligations

The implementation uses Mathlib's alternating maps, determinant, finite graph
degrees, finite/list enumeration, polynomial funext, and matrix rank APIs.
The custom wrappers expose the source construction rather than introducing
opaque semantic oracles. The generic commutative-ring algebra is appropriate
for its later polynomial specialization. Source credit remains with H. Tracy
Hall; the new conditional proofs make no claim to discovering his theorem.
No artificial interval calculation or extra numerical trust is needed.

For an unconditional SP-11 theorem, the numeric-order polynomial construction
still must be connected to a chosen greedy vertex ordering by explicit graph
relabeling/transport. Most importantly, nonzero diagonal and edge Gram
polynomials must be proved for the exact shared-variable recursion. The
unique-monomial/non-cancellation argument is not established by any of these
modules. Once those facts are proved, the reviewed specialization/rank gates
can finish the original witness statement. These are remaining proof
obligations, not blockers in the truthful conditional support modules.

## Reproduction and preservation

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-all-gates.py
python3 docs/lean/campaign-2026-10-17/verification/check-canonical-preservation.py
```

`sp11-all-gates-review/` retains the exact frozen sources, all raw command logs,
the all-export consumer, source hashes and machine-readable successful result.
The separate preservation manifest confirms that all **217 registered canonical
README pages/statuses**, all **611 original immediate problem artifacts**, the
registry bytes/mappings, and selected SP-11 original/frozen sources are
unchanged against published base
`47006df8b3a6c724a557266c891893d03e69323a`.

This is independent source/mathematical review and fresh macOS Lean/LeanCert
kernel-trust evidence using pinned compiled dependencies. It is not a new Linux
Comparator, exporter, sandbox or raw-kernel replay, nor a complete graph proof,
human peer review, or status promotion. No blocking finding remains within the
reviewed seven-module scope.
