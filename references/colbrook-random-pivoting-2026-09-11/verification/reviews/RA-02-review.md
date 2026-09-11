# Independent complete-manuscript review: RA-02

Date: 2026-09-11. Verdict: **PASS for the full canonical RA-02 target, with a negative answer.** The sharp universal same-rank RPCholesky trace-error factor is 2^r as a supremum for every r>=1. Hence no constants C>0 and p>=0 independent of n, r and A give the proposed Cr^p bound. Recommend **Solved (disproved)**. No mathematical source repair is required.

This is independent Codex-agent proof review, not external human peer review or formal verification. I did not edit the source or canonical problem. The assigned focus was RA-02; I also read and checked the shared LU calculations and the correlation-matrix extension for consistency. A separate reviewer handles the dedicated RA-03 assessment.

## Exact source identity and coverage

I read all 632 lines of `.cache/ra02-ra03/nla_submission_RA02_RA03/manuscript/sharp_random_pivoting.tex`: abstract, algorithm definitions, all theorem/corollary statements, both lower-bound arguments, every intermediate lemma, replication, the finite certificate derivation and bibliography. Complete UTF-8 source SHA256, with CRLF replaced by LF and no trimming or other normalization:

`f149e240af5827bbf4598fe3df144826254e17773cb23fb2851dad383410c69d`

The review is tied to this source, not merely to a submitted PDF or claimed validation label. Source locators and shared theorem numbering:

| Result | Locator |
| --- | --- |
| Theorem 1, sharp lower-bound family | line 112, equation `main-limits` |
| Corollaries 2 and 3, suprema and conjecture consequences | lines 127 and 139 |
| Lemma 4, prefix-row minors | line 198 |
| Lemma 5, Cauchy–Binet scale dominance | line 234 |
| Lemma 6, binary limiting rule | line 276 |
| Lemma 7, asymptotic normalizers | line 314 |
| Lemma 8, exact history identities | line 368 |
| Counting and spectral denominator | section beginning line 398 |
| Proposition 9, correlation-matrix sharpness | line 469 |
| Exact rational certificate derivation | section beginning line 531 |

## Canonical model and primary references

The actual `randomized-and-low-rank-approximation/RA-02/README.md` was read in full. It specifies Hermitian PSD inputs, diagonal residual sampling proportional to diagonal/trace, exact arithmetic, exactly r pivots, and comparison with the sum of eigenvalues after r. The displayed question asks for constants uniform over dimensions, ranks and inputs. The submission uses exactly that pivot rule and residual. A real positive-definite family is an allowed subclass of the canonical complex Hermitian PSD class. It has n=r+1 and positive optimal tail, so no zero-tail or early-termination ambiguity arises in the lower bound.

Primary sources accessed on 2026-09-11:

- [Chen–Epperly–Tropp–Webber, published RPCholesky article](https://onlinelibrary.wiley.com/doi/10.1002/cpa.22234), Lemma 5.5, explicitly supplies the expected trace bound with factor 2^k for PSD inputs. Its algorithm agrees with the residual update and diagonal/trace probabilities used here. Thus the matching upper bound is applicable; it is not an oversampling theorem.
- [Epperly, Make the Most of What You Have](https://tropp.caltech.edu/dissertations/Epp25-Making-Most.pdf), §11.1, Conjecture 11.2, printed page 182 (PDF page 202), proposes the polynomial r-step factor and cites Lemma 5.5. Its residual/approximation notation and omitted expectation have the defects already disclosed in the canonical source normalization. This audit uses the canonical corrected residual expectation, not a literal erroneous trace of the approximation.
- [Gilles–Wilber, primary manuscript v1](https://arxiv.org/html/2601.22344v1), equations (1) and (3), Theorem 3 and its following paragraph, confirms the LU rule and 4^k bound, conjectures its reduction to 2^k, and reiterates the PSD polynomial-factor conjecture. Its separately stated oversampling result is not substituted for the same-rank comparison.

These checks establish source scope and model agreement. They do not establish priority or authorship of the submitted manuscript, whose author field is empty.

## Independent audit of the all-r lower-bound proof

### Construction and prefix minors: PASS

For fixed r, let n=r+1 and epsilon=t^(n^2). L is real unit lower triangular, so LDL^T is positive definite for every t>0, with exact determinant epsilon^(r(r+1)/2). The contribution of column one to each off-diagonal entry is positive; all other contributions are nonnegative. Thus the examples are also entrywise positive and are rational whenever t is rational.

For a size-s row set S, partition rows into P=S intersect [s] and I=S outside [s], and missing columns into J=[s] minus S. After reordering and multiplying each missing column j by t^(-j), the prefix matrix tends to a block matrix with identity upper-left, zero lower-left and Cauchy block [1/(i+j)] for i in I, j in J. The upper-right block remains finite because P and J are disjoint, so no diagonal one is divided by a positive power of t. Distinct row and column labels give a nonzero Cauchy determinant; the signs from reordering do not affect nonvanishing.

It follows that det M_s(S) has exact lowest power d_s(S)=sum of the missing column labels and a nonzero leading coefficient. After scaling, the inverse is bounded. Restoring the column scaling places a diagonal factor with entries at most t^(-s) in the inverse, giving ||M_s(S)^(-1)||=O(t^(-s)). This bound is needed later and is justified even if the determinant has a much higher vanishing order. The empty-set conventions are consistent.

### Cauchy–Binet relative asymptotics: PASS

In a size-s minor of A, the unique least epsilon exponent in the Cauchy–Binet sum comes from columns 1 through s and is s(s-1)/2. Every other exponent is at least one greater. All L minors stay bounded. The leading coefficient product has nonzero lowest t power at most s(s+1), since each prefix determinant has degree at most s(s+1)/2. For s<=n-1,

`n^2 - s(s+1) >= n > 0`.

Consequently the O(epsilon) remainder divided by the leading product tends to zero. This is relative control, not merely an absolute expansion that could fail for small minors. For s=n there is only one term, so the identity is exact. Finitely many minors exist at fixed n, giving simultaneous nonvanishing below a positive dimension-dependent threshold. No uniform threshold in r is asserted or required.

### Interpolatory vectors and normalizers: PASS

The vector w_s(S) is L times (-c_s,1,0,...,0), so L tending to the identity gives h_s(S)>= (1+||c_s||^2)/4 eventually. If s+1 is absent from S, the restricted column l_(s+1)[S] is O(t^(s+1)); multiplication by the O(t^(-s)) inverse gives c_s=O(t), hence w_s tends to e_(s+1) and h_s tends to one. If s+1 is in S, the corresponding row of M_s has norm O(t), while its right-hand side is exactly one. Therefore ||c_s|| is bounded below by a positive constant/t, and h_s diverges. This proves the binary inverse limit and also bounds all reciprocal h_s uniformly.

The interpolatory residual after a history is independent of the order within its selected row and column sets. Its nonzero block entries equal appended bordered minors divided by the selected minor. Applying the preceding relative expansion to both minors, and a second bordered identity for L, gives

`residual_ij = epsilon^s w_s(I)_i w_s(J)_j (1+o(1))`.

The bordered prefix minors are nonzero eventually, including when s+1=n, so each indicated leading component is nonzero. There are only finitely many sets and entries at fixed n, allowing a uniform relative error. For Cholesky, each diagonal leading term is epsilon^s times a square; summing has no cancellation. For LU, squaring entries likewise prevents cancellation. These facts justify T_s~epsilon^s h_s and Q_s~epsilon^(2s)h_s(I)h_s(J) even when the h_s diverge. Inverting uses the established positive lower bound, and introduces no unsupported limit of an unbounded reciprocal.

### Pivot probabilities and exact cancellation: PASS

At a Cholesky history j_1,...,j_r, the product of pivot values is det A[S_r,S_r]. Therefore its probability is that determinant divided by the product of the r successive trace normalizers. Since n=r+1, the final zero-padded residual has exactly one potentially nonzero diagonal entry, equal to det A/det A[S_r,S_r]. Multiplication cancels the selected determinant exactly. The expected trace is consequently det A times the sum over all ordered histories of the reciprocal normalizer products. These are actual conditional pivot probabilities, not probabilities assumed independent across stages.

For LU the same argument uses the squared modulus of the product of pivots, with the determinant taken in the actual ordered row and column lists. Reordering only changes a sign; squared moduli remove it. The final residual has one remaining entry and the exact analogous cancellation applies. No independence of row and column histories is needed. All histories used in the small-t family have nonzero pivots by simultaneous minor nonvanishing.

### Exact denominator, limits and history count: PASS

The optimal rank-r trace tail equals lambda_n because n=r+1. The exact scaled inverse is

`epsilon^r A^(-1) = L^(-T) diag(epsilon^r,...,epsilon,1) L^(-1)`.

Since L and L^(-1) tend to I, this tends in norm to e_n e_n^T. Its top eigenvalue therefore tends to one. That eigenvalue equals epsilon^r/lambda_n(A), proving lambda_n/epsilon^r -> 1. This argument properly controls the small eigenvalue despite all the other scales; it does not approximate it by the final diagonal entry without justification. For the shared LU argument, positive definiteness makes the optimal squared Frobenius tail lambda_n^2.

The determinant exponent splits as r + sum_(s=0)^(r-1) s. Hence each normalized Cholesky path contribution is the product of epsilon^s/T_s times the common prefactor epsilon^r/lambda_n. It tends to one precisely when s+1 is absent from S_s at every s=0,...,r-1; otherwise it tends to zero. All factors have finite limits, so there is no zero-times-infinity ambiguity.

A surviving list cannot select any q in {2,...,r} before position q. At position u it may select exactly the unused members of {1,...,u,n}. That set has u+1 elements and contains all u-1 earlier choices, leaving two choices. This gives exactly 2^r ordered histories, including r=1. The label n is unrestricted because there is no normalizer with s=r. The sum has finitely many terms at fixed r, so summing limits is valid with no dominated-convergence issue. The resulting trace ratio tends to 2^r. Separately, the limiting LU indicators factor by row and column lists and give (2^r)^2, consistent with the manuscript's joint result.

### Quantifiers and the negative answer: PASS

For each fixed r and each positive gap eta, a sufficiently small t gives ratio greater than 2^r-eta. The primary universal upper bound gives the reverse supremum bound. For any proposed C,p, first choose r with 2^(r-1)>Cr^p and then choose t so the actual ratio exceeds 2^(r-1). This produces an allowed positive-definite counterexample with positive tail. It correctly refutes constants uniform in r and does not interchange the order of the two limits. The r=n zero-tail case cannot rescue a universal assertion already refuted at n=r+1.

## Unit-diagonal extension: PASS

For rational positive diagonal entries one can choose a positive rational c with each A_ii/c a positive integer m_i. Replicating row i with m_i copies scaled by 1/sqrt(m_i) gives an isometry P and unit-diagonal C=c^(-1)PAP^T. The entries of P need not be rational; the proposition only requires a real matrix. The nonzero spectrum is that of A/c, with additional zeros. Thus the optimal rank-r tails scale correctly.

For Cholesky, the m_i copies have equal diagonal masses B_ii/(c m_i), whose sum gives the original group's probability B_ii/tr B. For LU, the m_i m_j copies give total squared mass |B_ij|^2/c^2. The update cancels the copy normalization factors and restores precisely c^(-1)P B_new P^T. Norm preservation under the isometry gives exact ratio preservation. Repeated selections from eliminated groups have zero probability and do not alter the argument.

C is initially PSD, not positive definite in the larger space. The manuscript explicitly addresses this with C_delta=(C+delta I)/(1+delta). It is positive definite, strictly positive entrywise and unit-diagonal for delta>0. Fixing C and r first, every history with positive probability at delta=0 continues through nonzero denominators for sufficiently small delta. Its probability times terminal error therefore converges. Summing these finitely many contributions and discarding new nonnegative contributions gives a lower limit at least the old expectation. The positive optimal denominator is continuous. This is sufficient to approach the same supremum and does not assume full LU expectation continuity at vanishing pivots. The dimension may increase without bound as t decreases, exactly as disclosed.

## Finite certificates and shared consistency checks

I inspected `verification/exact_certificate.py`, `rational_linalg.py`, `exact_enumeration.py` and `verify_replication.py` in full. They use Python standard-library rational arithmetic for mathematical comparisons. The construction's zero-based implementation correctly uses t^(j+1)/(i+j+2). Schur residuals, inverse row norms and recursive updates agree with the manuscript. The code returns only the remaining block, which has the same trace/norm as the zero-padded block used in the proof.

With v=L^(-T)e_n and nu=||v||^2, the scaled inverse dominates vv^T, giving lambda_n<=epsilon^r/nu. Its trace gives the matching lower enclosure epsilon^r/tr(epsilon^r A^(-1)). The certificate maxima range over all size-s subsets of {1,...,s,n}; every surviving prefix lies there. Bounding each reciprocal normalizer from below and retaining 2^r positive histories proves the displayed finite trace lower bound. Terminal block inverses are checked as well as intermediate prefixes, so the final selected pivots are not silently assumed valid. Omitted histories are nonnegative.

The recursive enumeration computes actual transition expectations rather than using the determinant cancellation formula. Its exact eigenvalue enclosures are directed correctly when converted into ratio bounds. The 2-by-2 LU calculation is independently correct: each pivot's squared probability numerator cancels its reciprocal squared residual factor, giving 4 det(A)^2/||A||_F^2 and the stated value 18/5 for [[2,1],[1,2]]. The replication diagnostic checks the same group identity on a fixed rational isometry; it cannot prove the general proposition by itself.

The parent agent is coordinating fresh diagnostic runs and their final output record; this reviewer did not duplicate those runs or treat supplied PASS labels as evidence. The universal proof verdict above is based on the complete arguments and primary theorem checks, not on finite certificates or numerical eigenvalue estimates. Supplied table values are supporting claims to be cross-referenced with the fresh run record at integration.

## Acceptance scope and remaining questions

**RA-02 is fully negatively resolved by the reviewed proof.** Its exact same-rank factor is 2^r as a supremum, attained in the limit already along real positive-definite, entrywise-positive examples of order r+1. The correlation-matrix extension is also proved when dimensions are unrestricted.

The result does not assert that a finite member attains the supremum, give a uniformly conditioned example, establish a stable floating-point certificate, or refute oversampling guarantees. At r+1 pivots the original family is recovered exactly. In particular, no change to the separate RA-01 target follows. The complete manuscript is consistent about these distinctions. Preserve the original RA-02 statement and permanent ID when recording the resolution.
