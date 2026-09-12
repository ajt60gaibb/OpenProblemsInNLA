# SP-08 — exact finite cases and a general reduction

**Author:** Sidney Holden  
**Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.  
**Submission date:** 12 September 2026.  
**Editorial record:** [Attribution, independent review and scope](../README.md).

The review statements below describe the supplied draft; the linked submission record records subsequent independent review.

**NEW PARTIAL RESULT** relative to the cases explicitly listed in the pinned
canonical README; broader publication novelty is not established.

The original target: for every n>=2 and a in [-1,1), among all real symmetric
n x n matrices with **every** entry (including the diagonal) in [a,1], there
exists a rank-exactly-two matrix with entries in {a,1} whose spread
lambda_max-lambda_min equals the maximum over the whole continuous box.

`proof.md` establishes the general reduction to 2^(2n-1) signed-threshold
patterns and the following computer-assisted **subcase** proofs:

| n | a | Maximum spread | Block size of the rank-two attainer |
|---:|---:|---:|---:|
| 8 | 1/2 | sqrt(73) | 2 |
| 10 | 0 | sqrt(133) | 3 |
| 11 | 0 | sqrt(161) | 4 |

The finite upper bounds depend on exact integer certificates plus exhaustive
coverage, not numerical eigenvalue estimates. The written proof explains why
the finite family suffices for the continuous problem. The certificates are
proof data for those three subcases, not permission to replace the all-n target
by finite experimentation.

**Status proposal: retain PARTIAL; add the proved cases and reduction after
independent audit.** No conclusion for every n or every interval parameter is
established, so PARTIAL -> SOLVED is not justified.
