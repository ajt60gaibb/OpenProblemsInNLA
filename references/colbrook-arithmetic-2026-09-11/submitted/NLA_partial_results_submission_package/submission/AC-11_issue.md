# [AC-11] Explicit minimum-permanent certificates through order 35 — finite cases only

### Affected entry

AC-11, “Minimum positive permanent of a sign matrix.”

https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/arithmetic-and-complexity/AC-11

### Correction or result

This is a **finite special-case result, not an all-orders resolution**. The attached matrices attain `2^(n - floor(log2(n+1)))` for every `1 <= n <= 35`. In particular, explicit witnesses are supplied for orders 21–35. Combining each witness with the established universal divisibility bound gives the exact least positive permanent at that order.

**Proposed status: retain “Partially resolved.”** No solution claim for arbitrary order is made, and no closure of the entry is requested. This concerns the minimum-positive conjecture, not the different rank-dependent maximum-permanent conjecture.

Suggested progress note, conditional on review of the attachment:

> Exact finite-order certificates are available through order 35. They include explicit attaining matrices, full-matrix exact-arithmetic verification, and source code. The all-orders attainment question remains unresolved by these computations.

### Evidence

The attached note, *Exact finite cases of two sign-matrix permanent problems*, Theorem 1 and Sections 2–4, gives the lower-bound proof, the last-row construction, and the verifier's deterministic arithmetic justification. The data are `data/ac11/min1.txt` through `min35.txt`. `src/verify_permanent.cpp` checks each complete matrix, without reading its cofactor file, modulo `2^128` and `2^61 - 1`; an explicitly checked factorial bound makes agreement a proof of the exact integer value rather than a probabilistic hash test. `./reproduce.sh` performs the required checks.

Wanless's cited paper supplies constructions through order 20: I. M. Wanless, *Permanents of matrices of signed ones*, Linear and Multilinear Algebra 53(6) (2005), 427–433, §3, pp. 430–431, DOI 10.1080/03081080500093990.

https://users.monash.edu.au/~iwanless/papers/wangconjLAMA.pdf

**Priority has not been established.** The order-20 literature reference is not proof that later orders have not been treated elsewhere. The attachment is an AI-assisted, unreviewed computational note, not an existing peer-reviewed publication. Before posting, the submitter should supply appropriate reviewed authorship and a stable archival link; none is invented here.

### Rating implications, if any

None proposed. These finite cases do not justify marking the all-orders problem solved or changing its difficulty/importance ratings.
