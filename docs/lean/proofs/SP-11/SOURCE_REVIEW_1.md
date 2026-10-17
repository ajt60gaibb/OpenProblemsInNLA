# SP-11 independent support-source review 1

Reviewer: `/root/fr05_statement` (AI agent), 17 October 2026.
Baseline: `47006df8b3a6c724a557266c891893d03e69323a`.
Verdict: **APPROVE the six reviewed support modules within their explicitly
conditional scope.** No defect was found in their mathematical statements,
source correspondence or proof steps. This is not approval of an unconditional
SP-11 theorem: the needed non-cancellation theorem is absent.

## Independence and exact inputs

I independently read all source bytes of the six modules below. They were
written by other agents. I authored `GreedyOrdering.lean`, so I do not claim
an independent review of that module; its build is recorded only as context.
The fresh canonical/frozen statement review is [STATEMENT_REVIEW_1.md](STATEMENT_REVIEW_1.md).

| Reviewed module | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP11/AlternatingContraction.lean` | `5470ac391cec624ed4a11bc3fe5ff271dccbc2446db8a4aac44053c01407b6ca` |
| `lean-statements/NLA/Proofs/SP11/AlternatingPolynomial.lean` | `d1ece1a3defce0f4cae49af934548c2bad20d7273a7df91b29111787d8c876f7` |
| `lean-statements/NLA/Proofs/SP11/UniformLSS.lean` | `485ffa227d00a09bc93b8fe244815e8e7dc912064edffa6cadc8f09fc52bd431` |
| `lean-statements/NLA/Proofs/SP11/GramBridge.lean` | `e3ff1bd936a820a58ac005dd50487464e8d5a56b231268bd1e1b5d9936ab1aed` |
| `lean-statements/NLA/Proofs/SP11/PolynomialFaithfulness.lean` | `e1214cdc4072420c86006538cc9465bf29e9dda5a5e72dd1a0eb9ace4fd7928c` |
| `lean-statements/NLA/Proofs/SP11/PolynomialLSS.lean` | `12f18f17f1d74e03cd14a9b42bf9dfc45f67a0239f5cc8e0e405f45a267efd66` |

The machine-readable [input and command record](review-1-evidence/result.json)
also hashes the frozen/live boundaries, infrastructure, pinned dependency
manifest/toolchain and source originals. No reviewed source changed during
this reviewer's dependency-chain rebuild.

## Mathematical and source correspondence

`AlternatingContraction.lean` uses the ordinary commutative bilinear dot
product, appropriate both for real vectors and for vectors over their
polynomial coefficient ring. Its contraction vector evaluates the functional
on standard coordinate basis vectors. Re-expanding a vector in that basis
proves the exact dot-product identity. Alternation then makes its pairing
with every input zero by two repeated slots. The proof neither assumes nor
claims a nonzero output. It works for all finite coordinate and input sizes,
including empty types.

`AlternatingPolynomial.lean` indexes increasing coordinate tuples by actual
strictly monotone maps. A determinant minor is an alternating multilinear
form, and the sum of those minors weighted by named indeterminates is a
literal polynomial alternating form. This representation has independent
coefficients on increasing coordinate subsets. The output slot is placed
first, whereas the source places it last; moving that slot contributes the
fixed sign `(-1)^k` for a node of input arity `k`. This does not impose a new
orthogonality or faithfulness assumption.

`UniformLSS.lean` uses the exact increasing list of nonadjacent vertices with
smaller indices. The predecessor proof supplies the strict decrease needed
for the finite recursion. Every recursive occurrence of a vertex calls the
same assigned form. Its recursion equation and pairwise-nonedge proof are
exact. The ordering is still the fixed increasing order: a later proof must
transport a graph's greedy order to this indexing. This module promises only
orthogonality of nonedges, not independent predecessors, nonzero rows or
faithfulness of edges.

`PolynomialLSS.lean` instantiates that recursion over one concrete polynomial
ring. Its variable type is a dependent pair of vertex and increasing
coordinate subset. Thus different vertices have distinct coefficient
families, while all occurrences of one vertex share the same family. It
does not replace repeated tree occurrences by fresh independent variables,
which would remove the cancellations the intended proof has to address.
Its proved nonedge identity is exact. The matrix-existence theorem keeps
both the dimension inequality and the edge/diagonal nonzero-polynomial
condition as explicit hypotheses. The latter has not been proved here.

`PolynomialFaithfulness.lean` supplies a valid deterministic specialization
step over the infinite field of reals. A nonzero polynomial has a nonzero
evaluation by polynomial function extensionality. Taking a finite product
makes all required polynomial constraints nonzero at one common assignment.
Evaluation commutes with every finite sum and product in the Gram entries.
The two support directions are proved separately, and diagonal nonvanishing
ensures every row is nonzero. These are deductions from explicit polynomial
hypotheses; the file does not postulate the missing non-cancellation result.

`GramBridge.lean` constructs `R * R.transpose`, with rows rather than columns
representing vertices. Its symmetry proof uses commutativity of real
multiplication. Exact off-diagonal faithfulness supplies both support
directions. Matrix-product rank is bounded by `R.rank`, then by its width,
so no row independence or full-rank assumption is needed. The dimension
inequality gives the frozen natural nullity bound by arithmetic. The final
`target_of_faithful_representations` theorem retains the all-graph witness
hypothesis and hence is a conditional implication to `Target`.

The construction's relevant primary source is [Hall, Sections 4-5](https://arxiv.org/html/2601.01211v1).
This source review checks these implemented local steps. It does not claim
that the unimplemented Unique Monomial Lemma has thereby been formalized.

## Local kernel evidence and remaining proof boundary

I recompiled the dependency chain and [Inspect.lean](review-1-evidence/Inspect.lean)
using Lean 4.33.1 with the pinned dependency cache. Inspect checks literal
live/frozen target equality by `rfl`, displays the reviewed theorem types,
and repeats LeanCert kernel trust assertions. The [result record](review-1-evidence/result.json)
contains every command and exit code; the corresponding logs are beside it.
Selected theorem closures contain only `propext`, `Classical.choice` and
`Quot.sound`. There are no admitted proofs, custom mathematical axioms or
native trust substitutions in the reviewed source.

For a normal pinned checkout, reproduce with `lake build` on each reviewed
module, followed from `lean-statements` by
`lake env lean -R .. ../docs/lean/proofs/SP-11/review-1-evidence/Inspect.lean`. The recorded local commands use the campaign's
cache-aware compilation helper because Lake dependency checkout was not
recreated in this review. This is local kernel evidence; it is not an
isolated Linux Comparator certificate.

No reviewed support theorem supplies the missing nonzero edge/diagonal Gram
polynomial conclusion for every graph in the required dimension. There is
also a remaining interface step from a greedy listing to the fixed-index
polynomial recursion. An unconditional theorem inhabiting the exact frozen
SP-11 target, independently reviewed and then verified by Comparator and
LeanCert kernel mode, remains required before any Lean-verified promotion.
The canonical problem, permanent ID and current catalog status are unchanged.
