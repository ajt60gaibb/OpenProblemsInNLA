# RA-03 — independent full-manuscript review

Reviewer: independent AI mathematical audit, 11 September 2026. This is not external human peer review, formal verification, or a priority determination.

**Verdict: PASS. The canonical RA-03 inequality is false.** The explicit real positive-definite matrix [[2,1],[1,2]] has expected one-step RPLU squared Frobenius error 18/5 and optimal rank-one squared error 1, refuting the asserted factor 2 at k=1. The stronger manuscript result is also valid: for every fixed positive integer r, the exact worst-case squared-error factor is 4^r as a supremum, already on real entrywise-positive positive-definite matrices. The supplementary unit-diagonal sharpness statement is valid when dimension is unrestricted. No material mathematical gap was found in the shared proof or its supplementary claims.

**Recommended canonical status: Resolved — disproved.** Preserve RA-03's exact conditional squared-entry sampling rule, squared Frobenius norm, same-rank comparison and canonical path. The sharp factor 4^r is stronger supporting information; the finite 2-by-2 counterexample alone settles the full universal conjecture.

## Full source binding and reviewed material

Read the complete shared TeX manuscript `.cache/ra02-ra03/nla_submission_RA02_RA03/manuscript/sharp_random_pivoting.tex`, including all sections, both algorithms, the correlation-matrix proposition, finite certificates, table and references. Also read the complete current canonical `randomized-and-low-rank-approximation/RA-03/README.md` (Open, last checked 2026-09-10).

The manuscript's complete UTF-8 source, replacing CRLF with LF and performing no trimming or other normalization, has **27,565 bytes** and SHA-256:

`f149e240af5827bbf4598fe3df144826254e17773cb23fb2851dad383410c69d`

This hash was computed independently and confirmed by the separate reviewer diagnostic. It includes the complete original source, not merely the LU part or a rendered derivative.

Read the supplied verification programs in full: `rational_linalg.py`, `exact_certificate.py`, `exact_enumeration.py`, `verify_replication.py`, `verify_ra03_2x2.py`, and `test_suite.py`. Their claimed correctness was not taken as proof of the manuscript. The independent checks described below import none of them.

Principal locators in the reviewed TeX:

- **Theorem 1**, `thm:main`, line 112: both limiting sharpness claims and eventual nonvanishing of every square minor.
- **Corollaries 2–3**, `cor:sup` and `cor:negative`, lines 127 and 139: suprema and impossibility of smaller uniform factors.
- **Section 2**, lines 155–184, `eq:small` and `eq:small-expectation`: finite RA-03 counterexample.
- **Lemmas 4–5**, `lem:prefix` and `lem:CB`, lines 198 and 234: prefix minors and scale separation.
- **Lemmas 6–7**, `lem:h` and `lem:normalizers`, lines 276 and 314: limiting normalizers, including arbitrary row/column sets.
- **Lemma 8**, `lem:paths`, line 368: exact adaptive-history cancellation.
- **Section 6**, lines 398–461: optimal-error scale and surviving-history count.
- **Proposition 9**, `prop:correlation`, line 469: unit-diagonal sharpness.
- **Section 8**, line 531 onward, `eq:cert`: retained-path certificates, numerical displays and scope.

## Exact primary-source match

Opened [Gilles–Wilber, arXiv:2601.22344v1](https://arxiv.org/html/2601.22344v1). Equation (3) and Algorithm 1 sample a pivot with conditional probability equal to its squared modulus divided by the current squared Frobenius norm; the update matches the canonical residual formula. Theorem 3, equation (10), gives the 4^k bound for expected squared error, and the following paragraph explicitly conjectures replacement by 2^k. This is the manuscript's exact target. The source's PSD-preserving rank-two variant is a different algorithm and is not being substituted here.

The shared Cholesky upper bound was also checked against [Chen–Epperly–Tropp–Webber, primary journal text, Lemma 5.5](https://tropp.caltech.edu/papers/CETW25-Randomly-Pivoted-CPAM.pdf), which gives the same-rank 2^k trace bound used in the shared proof. The subsequent audit reconstructs the new lower-bound argument independently.

## 1. Finite counterexample, including off-diagonal pivots

For A=[[2,1],[1,2]], the orthogonal eigenvectors (1,1) and (1,-1) have eigenvalues 3 and 1. A is positive definite, so its singular values are 3 and 1 and the best rank-one squared Frobenius error is exactly 1. The squared-entry normalizer is 10.

Each diagonal pivot has probability 4/10 and leaves the complementary residual entry 3/2. Each off-diagonal pivot has probability 1/10 and leaves the complementary residual entry -3. The pivot row and column are zero after the update. Therefore each of the four paths contributes 9/10 to the expectation, giving 18/5>2. Dropping the off-diagonal paths would omit half the expected error and would analyze the wrong distribution.

For any nonsingular 2-by-2 matrix with no zero entries, each one-pivot residual has squared norm |det(A)|²/|A_ij|². Its probability cancels the denominator exactly, yielding four copies of |det(A)|²/||A||_F². Dividing by sigma_2² produces 4*sigma_1²/(sigma_1²+sigma_2²). The nonzero-entry restriction is necessary for this four-path formula and is correctly stated. The formula applies to complex matrices with squared moduli as well as real matrices. Its limit at large singular-value ratio is 4, consistent with the general theorem.

## 2. Family and prefix-minor estimates

L(t) is unit lower triangular, D has strictly positive diagonal entries, and A=L D L^T is positive definite for every positive t. For each off-diagonal entry, the first column contributes a strictly positive amount; diagonal entries are positive too. All entries are rational for rational t.

In a prefix minor of the first s columns, split the row indices into P inside {1,...,s} and I outside, and let J be the missing prefix column labels. Scaling precisely the J columns by t^(-j) leaves a matrix with limit [[I,F],[0,C]], where C_ij=1/(i+j). The scaled upper-right block is finite: rows in P and columns in J have no common label, so no diagonal 1 is amplified. The lower-left block tends to zero. The Cauchy determinant is nonzero because its row and column labels are distinct positive integers. Thus the prefix determinant has a nonzero coefficient at exactly the claimed power of t, with possible ordering sign harmless. The scaled inverse remains bounded; undoing the scaling costs at most t^(-s). This proves both statements of Lemma 4.

Cauchy–Binet for A[I,J] has a unique least epsilon exponent at the prefix spectral set {1,...,s}. Every other spectral set has exponent at least one greater and bounded L-minors. The leading product of prefix minors has nonzero coefficient and t-degree at most s(s+1). Because epsilon=t^(n²) and n²>s(s+1) for s<=n-1, the O(epsilon) remainder is little-o of that leading product. The full n-by-n determinant has only one term and is exact. All fixed-dimensional row and column sets are finite in number, so one sufficiently small positive threshold gives simultaneous nonvanishing of every square minor. This is crucial for arbitrary off-diagonal LU histories and is established, not assumed from positive definiteness.

All limits in this argument fix r and n first. No estimate uniform over growing r is needed for the theorem or its later impossibility corollaries.

## 3. Residual normalizers with arbitrary row and column sets

The interpolating vector w_s(S)=L times (-c_s(S),1,0,...) has norm squared at least (1/4)(1+||c_s(S)||²), since the smallest singular value of L tends to 1. If s+1 is not selected, the right-hand side defining c_s has entries zero or O(t^(s+1)); the inverse bound therefore gives c_s=O(t) and w_s tends to e_(s+1). If s+1 is selected, its interpolation row has norm O(t) while its target entry is 1, forcing ||c_s||>=constant/t. This proves that h_s tends to 1 or infinity according to the stated indicator rule, and always stays bounded below. The empty-prefix case is included.

For an arbitrary LU state with equally sized selected row and column sets I,J, the interpolatory residual equals the zero-padded Schur complement. Holding the selected orders fixed, its unselected entry is the bordered determinant divided by det(A[I,J]). Gaussian elimination gives this same residual after every legal history with those sets. Its value does not depend on ordering inside the selected sets.

Applying the previous determinant asymptotics to this quotient, with appended indices and their signs retained, gives the leading outer product epsilon^s*w_s(I)*w_s(J)^T. Each unselected component of w is nonzero for small t by the bordered prefix-minor result. Thus relative, rather than merely absolute, entrywise errors tend to zero. Finitely many entries and sets make their maximum relative error tend to zero.

For Cholesky, the leading diagonal terms are nonnegative squares. For LU, taking squared absolute values similarly gives nonnegative leading weights. Summing is therefore legitimate even when some components of w diverge: the error in the finite weighted sum is bounded by the maximum relative error times its positive leading sum. This proves Q_s~epsilon^(2s)h_s(I)h_s(J) and the trace analogue. The uniform positive lower bound on h makes inversion safe in both finite and diverging cases. The resulting normalized LU factor is bounded and tends to the product of two 0/1 indicators.

There is no assumption here that an off-diagonal LU residual is positive semidefinite. Positive definiteness is used for the original family and Cholesky branch; arbitrary LU residuals are treated by their Frobenius squared norm.

## 4. Adaptive joint histories and exact cancellation

Every legal pivot annihilates its current row and column. Consequently positive-probability histories have distinct row labels and distinct column labels separately. The eventual nonvanishing of all square minors guarantees that every separately distinct ordered pair of lists in the displayed sums is legal for this family.

For an LU history, conditional probabilities multiply to the product of squared pivot moduli divided by the product of current Q_s. The product of pivots is the determinant of the selected block in the ordered row and column lists. After n-1=r steps only one residual entry remains, whose squared modulus is |det A|² divided by the squared modulus of that block determinant. Multiplication by the history probability cancels that determinant exactly. Row/column permutations only change signs before taking modulus. Thus each individual history contributes

`|det A|² / product_(s=0)^(r-1) Q_s(I_s,J_s)`.

This identity accommodates arbitrary adaptive dependence. It neither samples row and column lists independently nor replaces the joint conditional probabilities by marginals. Summing the finitely many contributions gives Lemma 8. The same argument with principal determinants and trace gives the Cholesky formula.

The family determinant is epsilon^(r(r+1)/2). Moreover epsilon^r*A^(-1) tends to e_n e_n^T because L^(-1) tends to I. Its largest eigenvalue tends to 1, so lambda_min(A)/epsilon^r tends to 1. Since n=r+1 and A is positive definite, the optimal same-rank squared Frobenius error is lambda_min². The normalized LU identity consequently has prefactor epsilon^(2r)/lambda_min² tending to 1 and the factors epsilon^(2s)/Q_s stated in the proof. The exponents cancel correctly: r(r+1)-2*sum_(s=0)^(r-1)s=2r.

For a single index list, survival is exactly the rule that no label q in {2,...,r} appears before position q. Label n has no such constraint because the last normalizer index is r-1. At position u, the allowed labels {1,...,u,n} contain all u-1 previously selected labels and have size u+1, leaving exactly two choices. There are exactly 2^r surviving lists. Both the row list and the column list must satisfy this rule, giving 4^r ordered pairs. This is a factorization of the limiting indicator, not of the sampling law.

Every factor has a finite 0/1 limit, the number of histories is finite for each fixed r, and the optimal-error prefactor tends to 1. Hence the limit of the full ratio is exactly 4^r. The universal upper bound supplies the opposite supremum inequality. The lower-bound family is already real, positive definite and entrywise positive; restricting to that class does not change the supremum.

## 5. Unit-diagonal replication and omitted histories

Choose a rational c>0 so that m_i=A_ii/c are positive integers. The replication matrix P has orthonormal columns because group i contains m_i copies of e_i^T/sqrt(m_i). Thus C=c^(-1)P A P^T has unit diagonal, positive entries and the nonzero eigenvalues of A/c. Its best same-rank error scales exactly as claimed, with additional zero eigenvalues harmless.

For a residual c^(-1)P B P^T, all m_i*m_j entries in block (i,j) equal B_ij/(c*sqrt(m_i*m_j)). Their total squared-entry probability is |B_ij|²/||B||_F². Direct substitution into the rank-one update returns c^(-1)P B_new P^T for every representative pivot in that block. For diagonal Cholesky pivots the m_i entries similarly aggregate to B_ii/tr(B). Repeated group selections have zero probability once the corresponding group row or column has been annihilated. This establishes exact aggregation of the entire adaptive process, not only the first step. Frobenius norm and trace are preserved by the isometric embedding up to the stated powers of c.

C is initially only semidefinite if replication increases dimension. The perturbation (C+delta*I)/(1+delta) is positive definite, still entrywise positive and exactly unit-diagonal. Fixing the finite dimension and stopping rank, every history with positive probability at C has nonzero pivots and normalizers along its path. Its probability and weighted terminal error therefore converge under the perturbation by rational continuity. There are finitely many such histories.

All other histories have nonnegative squared-error contributions. Discarding them proves the required lower limit for the expectation. It is not necessary to prove that newly possible histories have contributions tending to zero; the manuscript correctly makes no such assertion. The positive optimal-error denominator converges by eigenvalue continuity. This justifies the claimed liminf for the ratio even where the full expected LU error might not be continuous at zero pivot entries.

Choose the rational small t first, then its finite replication, then sufficiently small delta. Arbitrarily large replication dimensions are permitted. The universal upper bound completes the supremum statement. The proposition does not supply fixed-dimension correlation examples or bounded conditioning, and does not claim either.

## 6. Supplementary certificate and scope claims

With v=L^(-T)e_n, the matrix epsilon^r*A^(-1) is positive semidefinite and dominates vv^T. Its maximum eigenvalue is at least nu=||v||² and at most its trace. The reciprocal eigenvalue bounds on lambda_min are therefore correct, including their directions.

Every surviving history has its s-element prefix in G_s, the subsets of {1,...,s,n}. The maxima m_s and q_s bound the normalizers for every retained history. At each fixed finite parameter, retaining these valid paths in the expectation and using epsilon^r/lambda_min>=nu gives exactly equation `eq:cert`. Histories outside the retained set need not satisfy any extra nonsingularity assumption for this lower bound; their contributions are nonnegative. Retained prefixes and terminal blocks must be invertible, and the supplied certificate checks them.

The program `exact_certificate.py` uses exact Fraction arithmetic for these maxima and block inversions. Its s=0 good set correctly contains only the empty tuple. Terminal retained sets are all n choices of n-1 labels, and their row/column pairs are checked explicitly. The ordinary matrix helpers use exact elimination, and their scaled inverse trace uses the row norms of L^(-1), which is the correct trace formula.

The separate `exact_enumeration.py` uses actual residual updates and conditional pivot probabilities, rather than the history identity, to compute small-dimensional expectations. Its deletion of the annihilated row and column preserves the residual norm and all subsequent nonzero pivot probabilities. Squaring real entries is correct for the real family used by these diagnostics. Its stated PSD-input precondition and zero-residual treatment agree with its uses.

The three displayed downward decimal bounds were checked by exact Fraction comparisons against the corresponding stored lower fractions: the r=2 and r=3 enumeration records and the r=8 retained-history record all strictly exceed the printed decimals. This is a consistency check on the displayed numbers, not independent regeneration of the stored high-rank certificate; the analytic all-r proof above does not depend on them.

The shared Cholesky sharpness and polynomial-impossibility arguments have no extra gap: the same normalizer and counting proof gives 2^r, and for each proposed polynomial factor one chooses r first and then sufficiently small t. The LU impossibility of C*2^r or polynomial(r)*2^r follows in the same way from 4^r. The matrices are recovered after r+1 steps, and zero-padding preserves the nonzero-pivot process but gives no oversampling lower bound. The manuscript correctly leaves RA-01 outside its conclusion.

## 7. Independent exact checks

Created and executed `.cache/ra02-ra03/reviews/reviewer_ra03_exact.py`, with results in the sibling `reviewer_ra03_exact.json`. It uses standard-library `Fraction`, keeps full zero-padded residuals with original labels, and imports no submitted code. This differs from the supplied compressed-residual enumeration.

All checks passed:

- The four literal 2-by-2 pivot paths have total probability 1 and expected squared error 18/5.
- For the separate positive-definite matrix [[4,1,2],[1,3,1],[2,1,5]], all 36 two-step adaptive LU paths individually satisfy the determinant cancellation identity. Their probabilities sum exactly to 1.
- For a rational 3-by-3 positive-definite input and its 6-by-6 unit-diagonal replica with multiplicities (4,1,1), full path enumeration gives the same expected squared error: 23/6 after one step and 7296/6325 after two. At two steps the original has 36 positive-probability paths and the replica has 324; the equality is not an accidental identification of individual labels.
- Exhaustive ordered-list counts for r=1,...,7 agree with 2^r surviving lists and hence 4^r pairs.

These finite checks supplement, rather than replace, the uniform argument. The source hash in their output matches the complete-source binding above.

## Final disposition

**PASS — full negative resolution of RA-03, with the stronger sharp 4^r supremum theorem verified.** The finite counterexample matches the canonical algorithm exactly. The higher-rank theorem handles adaptive off-diagonal histories, the retained-path lower bounds legitimately omit only nonnegative contributions, and unit-diagonal positive-definite sharpness is valid in unrestricted dimension.

No original manuscript, supplied verification file, or canonical problem file was edited. This review makes no claim about historical novelty, external journal acceptance, alternative pivot distributions, unsquared expected norms, or oversampling guarantees.
