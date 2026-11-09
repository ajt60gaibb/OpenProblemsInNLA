# IE-03 numerical targets and exact statement

The sources are the canonical IE-03 page and Matias Andia's *A Hadamard
matrix with growth factor greater than its order*, Theorem 1 and Section 2,
at catalog revision `3017ea813328900a812c0c105ca16ad6f694857e`.

| Source | SHA-256 |
| --- | --- |
| `linear-systems-and-elimination/IE-03/README.md` | `370f171c362ab381d996b3dd23ec7cc420638a5f82f91a520f6ef7fc0f5a7c57` |
| `references/andia-ie03-2026-10-31/main.tex` | `014ee5727ce8794d3b32d237bb393a24569201f2f2376e9a2878c99e2b9da698` |
| `references/andia-ie03-2026-10-31/verify_construction.py` | `f9cd356dbfdb0505737d24155be86eb09d47a8ccfdb7d1808b31ca1e3c27a5b1` |

The original target is the equality of the real element-growth factor to
the matrix order for every positive Hadamard order and every complete-pivoting
path in exact arithmetic. `IsHadamard` requires sign entries and the real row
Gram identity on all indices below the order. These conditions imply
nonsingularity at positive order. `IsPivot` selects any active entry of
maximal absolute value and requires it to be nonzero. Its inequality permits
ties. `schur` deletes the selected row and column after applying the scalar
Schur update to every surviving entry. The increasing index map is one
choice of how to store the survivors. Any next row and column can be picked
from that order. This encodes row and column interchanges through the selected
positions in the active matrix.

`CompletePath` requires the active order to reach zero. At each step the
pivot magnitude is the maximum of the current active matrix, so the maximum
of those magnitudes is the largest magnitude encountered during elimination.
At positive Hadamard order the initial maximum is one, making this maximum
the element-growth factor without a further division. Entries outside the
active index range never enter a pivot comparison, Schur update on a surviving
entry, or Gram sum.

The witness starts from the Sylvester sign matrix. Four successive lifts
by the order-four Sylvester factor move from order 16 to 64, 256, 1024 and
4096. Each lift consists of two order-two lifts. The directly checked active
matrix sizes at the starts of the five stages are 16, 24, 32, 40 and 48.
Their local sequences have respectively 10, 16, 22, 28 and 48 pivots, for
124 local choices in all. At each step the certificate must verify the pivot
bounds across the entire active square, its nonzero value and the Schur
recurrence. A separate algebraic proof must preserve these properties through
the lifts. A sign and Gram proof must cover the full order-4096 input.

The intended output `counterexample` binds all these facts to one real
matrix and one complete path of order 4096 with exact growth 4608. Then
`cryer_false` refutes the universal equality because 4608 exceeds 4096.
The paper's first overshoot index and larger-order corollary are supplementary
to the catalog target.
