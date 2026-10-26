# Independent RA-05 hyperplane bridge pre-proof review

Reviewer: OpenAI Codex AI agent `/root/inventory`, 23 October 2026. The packet
author is `/root/proof_route`. I did not author its definitions, signatures,
contract or proof implementation. I separately authored the campaign source
inventory, which supplies no mathematical assumption to this bridge.

**PASS for implementation of the three exact support signatures.** Approval
binds the final corrected constructor `1 - Matrix.vecMulVec x x` and these
SHA-256 hashes:

| Input | SHA-256 |
| --- | --- |
| `NLA/Proofs/RA05/HyperplaneDefinitions.lean` | `03c589f029a146203487f4d5ed5982eb67e4a91d64c0ab8f817baf1de898a276` |
| `Challenge.lean` | `0049b6258325a138e0579fd26fcacc772758996f77c3cc9211a3e58a3663ff12` |
| `SUPPORT_CONTRACT.md` | `c2d08bf28f286bf6fa5c9c5e66b8bdf7aceeaa5435377e626051483e4f661552` |

I read the actual RA05 and RA06 copied definitions, the complete canonical
RA-05 page and preserved exact specification from published commit
`5487945e5a72abd952b0c89915915de8cc9b3e65`, the displayed strong-coreset model
and hyperplane lemma in Part I, and the exact support contract and signatures.
I independently byte-compared **all ten** SOURCE_LOCK destinations with their
claimed immutable published source objects, and verified their SHA-256 entries;
every comparison passed. This includes both manuscripts and their retained
informal review, but I do not claim here to rederive their complete rate
classification or endorse any new informal proof.

`unitHyperplane_projector` is the exact real Euclidean projector onto the
orthogonal complement of the same unit vector. Outer-product entries are
`x i * x j`. Symmetry and idempotence use the actual sum of squared coordinates
equal to one. That identity also makes `x` nonzero; the projector kills it, so
its rank is strictly below `d`, giving the natural bound `d - 1`. The explicit
`0 < d` premise covers natural subtraction faithfully, and the `d = 1` case
correctly has rank zero. No input-matrix rank condition is involved.

`rowCost_unitHyperplane` preserves the row and transpose conventions exactly:
the actual RA05 residual coordinate is
`(∑ h, A i h * x h) * x j`, using the very same RA06 `RowValue`. Its squared
Euclidean norm is the square of this real row action. Taking the nonnegative
square root gives its absolute value, before taking the same arbitrary real
power. Thus this identity needs no restriction on `p`. It does not substitute a
column norm, assume an approximate projection, or normalize the input rows.

`strongCoreset_implies_allVectorEmbedding` is a necessary consequence of the
actual simultaneous projector guarantee at rank `d - 1`. Unit vectors use the
two preceding statements. Every nonzero real vector has a positive Euclidean
norm; normalization gives the unit case, and both actual energies scale by the
same positive real power of that norm. Cancellation is valid for either
inequality regardless of the sign of `1 - ε`. For the zero vector, `p > 0`
gives zero row energies. The result keeps the same arbitrary nonnegative
original-row weights supplied by `StrongCoreset`, and the same matrix,
exponent and accuracy, for **every** test vector. Empty row sets, rank-deficient
matrices, dimension one and all real accuracies remain covered.

There is no hypothesis assuming the desired all-vector result, a lower-bound
obstruction, a numerical certificate, a chosen sampler, prescribed weights or
finite-dimensional restriction beyond the theorem's actual arbitrary `n,d`.
`WeightedInputEnergy` is a literal finite sum of the copied row actions with
arbitrary supplied real weights; the hcore premise supplies their required
nonnegativity. RA06's sampler-specific final theorem is not imported as an
arbitrary-weight obstruction. The contract's separate graph-rate discussion
correctly records the strict `2 < p < 3` range and does not present that
discussion as one of the three Lean conclusions.

These lemmas do not prove `Classification`, the universal `NegativeAnswer`, or
their conjunction `Target`. The original question also ranges over all
`k < d`, whereas this necessary-test bridge uses legal hyperplanes at rank
`d - 1`. That is appropriate support, not a full replacement target. The
canonical status must remain Solved. The Challenge holes are intentional
reference statements, not accepted proofs. This is a source/semantic review;
implementation, kernel trust, axiom closure and actual Comparator evidence
require separate checks. No numerical certificate is needed for this exact
linear algebra and real-power homogeneity.
