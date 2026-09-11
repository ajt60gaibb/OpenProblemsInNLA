# [AC-12] Exact restricted permanent-range certificates through order 10

### Affected entry

AC-12, “Same permanent with negatives above the diagonal.”

https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/arithmetic-and-complexity/AC-12

### Correction or result

This is a **finite special-case result, not an all-orders resolution**. For every `1 <= n <= 10`, the attached exact computations establish

`{per(A): A in {-1,+1}^(n x n)} = {per(B): B is a sign matrix and B[i,j]=+1 for i>j}`.

Negative diagonal entries are allowed. The entries below the diagonal are **+1, not zero**.

**Proposed status: “Partially resolved” after reviewer confirmation**, should the maintainers use that label for the certified finite range. Retaining “Open” for the general statement is also consistent with the mathematical scope. No closure as solved is requested, and no new entry for each finite order is proposed.

The catalogue sizes are:

| Order | Absolute values | Signed values |
|---:|---:|---:|
| 1 | 1 | 2 |
| 2 | 2 | 3 |
| 3 | 2 | 4 |
| 4 | 5 | 9 |
| 5 | 8 | 15 |
| 6 | 16 | 31 |
| 7 | 36 | 72 |
| 8 | 158 | 315 |
| 9 | 506 | 1,011 |
| 10 | 1,933 | 3,865 |

### Evidence

The attached note, *Exact finite cases of two sign-matrix permanent problems*, Theorem 2 and Section 5, supplies the coverage proof, the completion bound, and the sign-symmetry argument. Every value has an explicit restricted-family witness in `data/ac12`, checked with arbitrary-precision subset dynamic programming.

Completeness does **not** rely on sampling. Every unrestricted matrix can be normalized and moved to a lexicographically minimal core representative covered by the enumeration. For a fixed prefix H of k rows, every completion has absolute permanent at most

`(n-k)! * sum_{|I|=k} |per(H[:,I])|`.

Together with universal divisibility, this proves that certain whole branches lie in an already witnessed initial progression. The remaining representative leaves are checked explicitly against the catalogue. Both the witness-membership and unrestricted-inclusion checks are performed by `./reproduce.sh`. The unrestricted range being a subset of the witnessed restricted range, and the restricted family being a subset of the unrestricted family, establish equality. Negating the first row proves the corresponding signed statement.

The question is Problem 4 of §6 in DeVon Ingram and Alexander Razborov, *On the Range of the Permanent of (±1)-Matrices*, arXiv:2507.09433.

https://arxiv.org/html/2507.09433v1

**Priority has not been established.** The attachment is an AI-assisted, unreviewed computational note. A submitter should verify the existing finite-case literature, rerun the certificates, and supply appropriate authorship and an archival link before posting. No proof of the statement for all orders is included.

### Rating implications, if any

None proposed. The finite data and coverage certificates do not support marking the general problem solved or changing its difficulty/importance ratings.
