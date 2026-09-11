# Independent computational review: RA-02 / RA-03 package

Date: 2026-09-11.

**Verdict: PASS for the inspected exact computations and their stated finite certificate scopes.** All ten tests and the four requested fresh standalone computations passed. Their mathematical JSON fields reproduce the supplied records exactly, excluding elapsed timing. The exact \(2\times2\) calculation independently refutes the literal canonical RA-03 inequality. The finite rank-three and rank-eight certificates alone do not establish the manuscript's universal sharpness claim or refute the existence of unknown polynomial constants in RA-02; those conclusions require the separate all-rank proof review.

A minor command-line documentation issue is recorded below. It does not affect any mathematical result.

## Source inspection and preservation

Before execution, read all six executable mathematical Python files in full, plus the verification README and the canonical RA-02 and RA-03 statements. No network calls, shell execution, or unrelated filesystem effects occur in the mathematical code. Output writes are explicit JSON files chosen by the caller. Timing uses floating point, but all mathematical comparisons use exact Fraction arithmetic or integers. Decimal conversions are display-only.

The entire 14-file verification directory was copied byte-for-byte to .cache/ra02-ra03/rerun. The copied supplied results remain in rerun/results for regression comparison. All fresh outputs were directed to rerun/fresh-results. No submitted source or original result was modified. Execution used bundled Python with -X utf8 -B, without third-party dependencies.

Complete source hashes, including the supplied result files and README, appear in source-hashes.json next to this report. SHA-256 normalization is complete UTF-8 text with CRLF replaced by LF, without trimming or other transformations.

| Executable source | Complete UTF-8/LF SHA-256 |
| --- | --- |
| exact_certificate.py | f48cc1e8bf0c97b28296ec9ffac907d4aaf39b571e00f8f04f89b6c6cee23187 |
| exact_enumeration.py | 5667c97127519ffa4607b7a85dc675a7367604c27f524226b4cb6b8e578c4e88 |
| rational_linalg.py | 2d0200a8ee48dd3a88243309392ee79611ff4ec35a6561a355b8bb0c46415495 |
| test_suite.py | db3c22ee8ad19f0fa12644d85398b8e99175a2c9492056f29abf710b88dfde99 |
| verify_ra03_2x2.py | 360faf4b7c11bc4158fe1621c7634a46a15c4ba04b49ddb9c20717d84a02e653 |
| verify_replication.py | 150e3e08dbf22ec8663e298c75ea3892d9551f5a9b57e6b1f14251db159491d9 |

## Fresh execution

The run manifest is .cache/ra02-ra03/rerun/fresh-results/run-manifest.json. It records exact argument vectors, return codes, timings, stdout and stderr paths, and supplied-output comparisons.

| Run | Outcome | Fresh artifact |
| --- | --- | --- |
| test_suite.py | 10 tests, all PASS | fresh-results/test_suite.stderr.txt |
| exact_enumeration.py --r 3 --t 1/100 | PASS, 15 Cholesky states and 63 LU states | fresh-results/enumeration_r3.json |
| exact_certificate.py --r 8 --t 1/100 | PASS, 285 pivot blocks | fresh-results/exact_r8.json |
| verify_ra03_2x2.py | PASS, exact expected squared error 18/5 | fresh-results/ra03_2x2.json |
| verify_replication.py | PASS for one and two pivots | fresh-results/replication.json |

The suite also freshly regenerates both supplied small enumerations at ranks 2 and 3, both certificates at ranks 3 and 8, and all its other checks. It does not accept stored status labels as verification.

At rank three, the rigorous ratio lower endpoints have decimal displays approximately
\[
 7.99957072522610699038,\qquad
 63.99313178789454334698.
\]
At rank eight, the exact fractions strictly imply the downward-truncated bounds
\[
 \text{Cholesky ratio}>255.85420697,\qquad
 \text{LU squared-error ratio}>65461.37522779.
\]
Both rank-eight comparisons against \(99/100\) of \(256\) and \(65536\) are exact rational comparisons, not rounded decimal tests.

All fields of the four fresh standalone JSON results agree with the supplied JSON records after deleting the elapsed_seconds field. The standalone \(2\times2\) and replication records have no varying timing field.

## Exact linear algebra and enumeration

The family is
\[
 A=L\,\operatorname{diag}(1,\epsilon,\ldots,\epsilon^r)L^\top,\quad
 \epsilon=t^{(r+1)^2},\quad n=r+1.
\]
The matrix \(L\) is unit lower triangular, with its entry formula correctly translated from one-based mathematical indices. For \(0<t<1\), all diagonal weights are positive, so \(A\) is real SPD. Because all its lower-triangular nonzero entries are positive and the first column is positive, \(A\) is also entrywise positive. This construction supplies positive definiteness; merely checking positive residual diagonal entries would not prove it for a general matrix.

Gauss–Jordan inversion, multiplication, submatrix selection and the Schur residual formula use exact fractions. Singular pivot blocks are rejected, rather than regularized or approximately inverted.

The actual-update enumeration uses the prescribed conditional probabilities and rank-one updates. Previously selected rows and columns become exactly zero, so deleting them from the stored residual does not change the trace or squared Frobenius error. Cholesky residuals stay PSD, and their diagonal probabilities sum exactly to one. LU residuals need not be PSD; squared entries still give the correct nonnegative probabilities. Zero entries have zero probability and are omitted. Exactly zero residuals terminate with zero error, matching the canonical convention.

Memoization saves the conditional continuation value for identical residual matrices and remaining step counts. It does not discard incoming probability masses: each caller still weights the cached continuation by its own transition probability.

The routines use real squares rather than complex absolute squares. This is correct for these real inputs and is enough to test or refute assertions quantified over all complex matrices. They are not claimed as a generic complex-matrix implementation. The enumeration function explicitly requires PSD input for its Cholesky half; it does not comprehensively validate that caller precondition.

## Eigenvalue enclosure

Writing \(v_i=L^{-\top}e_i\), the scaled inverse is
\[
 G=\epsilon^rA^{-1}
   =\sum_{i=0}^{r}\epsilon^{r-i}v_i v_i^\top .
\]
The code computes its exact trace from the squared row norms of \(L^{-1}\), and
\(\nu=\|L^{-\top}e_n\|^2\) from the last row. Since \(G\succeq v_rv_r^\top\succeq0\),
\[
 \nu\le\lambda_{\max}(G)\le\operatorname{tr}G,
 \qquad
 \frac{\epsilon^r}{\operatorname{tr}G}
 \le\lambda_{\min}(A)
 \le\frac{\epsilon^r}{\nu}.
\]
The family has order \(r+1\), so the optimal rank-\(r\) trace error is exactly \(\lambda_{\min}(A)\), and the optimal squared Frobenius error is its square. Dividing the exact expected errors by these positive rational bounds gives the correctly oriented rigorous ratio intervals. No numerical eigensolver is involved.

## Retained-history certificate logic

The rank-eight certificate does not enumerate every LU history. Its lower bound remains valid for the following reasons.

At step \(j\), a retained one-based history selects from \(\{1,\ldots,j,n\}\) excluding previously selected indices. There are precisely two choices at every step: the earlier selected set has \(j-1\) elements in that domain of size \(j+1\). Therefore there are \(2^r\) retained Cholesky histories and \(4^r\) retained ordered pairs of row/column histories for LU.

After \(s\) steps, every retained prefix is an \(s\)-subset of \(\{1,\ldots,s,n\}\). The code enumerates all these sets, computes all their principal trace normalizers and all row/column-paired Frobenius normalizers, and takes exact maxima after removing the stated powers of \(\epsilon\). It checks all necessary prefix blocks by exact inversion. It also inverts every final retained \(r\times r\) block, ensuring the last retained pivot is nonzero. The block count is
\[
 \sum_{s=0}^{r-1}(s+1)^2+(r+1)^2,
\]
which gives \(285\) at \(r=8\).

For a complete history leaving a scalar residual, determinant telescoping gives its probability-weighted trace contribution as
\[
 \frac{\det A}{\prod_{s=0}^{r-1}\operatorname{tr}R_s},
\]
and its probability-weighted squared LU error as
\[
 \frac{(\det A)^2}{\prod_{s=0}^{r-1}\|S_s\|_F^2}.
\]
These identities follow from the Schur determinant identity along invertible pivot blocks. Sorting the selected row and column sets in the normalizer calculation does not change the residual Schur complement. LU determinant signs disappear after squaring.

Here \(\det A=\epsilon^{r(r+1)/2}\). Removing the prefix scales therefore leaves \(\epsilon^r\) for Cholesky and \(\epsilon^{2r}\) for squared LU error. Summing only the retained nonnegative contributions, dividing by the normalizer maxima and using the eigenvalue upper bound gives exactly the code's two rational lower bounds
\[
 \frac{2^r\nu}{\prod_s T_s},\qquad
 \frac{4^r\nu^2}{\prod_s E_s}.
\]
The checks against the known universal upper factors are consistency assertions, not premises used to derive these lower bounds.

The suite tests the determinant-cancellation formula on another exact SPD matrix and compares it to actual-update enumeration. Its history-count tests through rank seven corroborate, but do not replace, the elementary two-choice argument.

## Standalone RA-03 counterexample

For \(A=\left(\begin{smallmatrix}2&1\\1&2\end{smallmatrix}\right)\), the squared Frobenius normalizer is \(10\). Each diagonal pivot has probability \(2/5\) and leaves squared error \(9/4\). Each off-diagonal pivot has probability \(1/10\) and leaves squared error \(9\). Every one of the four pivots contributes \(9/10\), giving
\[
 \mathbb E\|S_1\|_F^2=18/5.
\]
The orthogonal eigenvectors \((1,1)\) and \((1,-1)\) have eigenvalues \(3\) and \(1\); hence the optimal rank-one squared error is \(1\). Thus \(18/5>2\), directly refuting canonical RA-03 at \(k=1\). This is a complete counterexample to the stated universal inequality and does not depend on scale separation, limiting eigenvalues, or the all-rank argument.

## Replication scope

The source \(3\times3\) matrix has leading principal minors \(4,3,2\), so it is SPD. The explicit \(6\times3\) replication matrix satisfies \(P^\top P=I\). Its replicated matrix \(PAP^\top\) is unit-diagonal, entrywise positive, PSD and rank three. The norm and trace checks, and the exact one- and two-pivot expected errors, pass.

The two-pivot values are \(4/5\) for expected trace and \(7296/6325\) for expected squared error. This verifies the particular replication identity and example. The \(6\times6\) replica is rank deficient; this computation does not by itself certify any limiting perturbation to an SPD correlation matrix or the general continuity argument.

## Documentation issue and precise limitations

The README documents verify_ra03_2x2.py with an --out option, but the actual script has no argument parser and only prints JSON. Supplying --out is silently ignored. For this rerun, its JSON stdout was captured to fresh-results/ra03_2x2.json; the source was left untouched. A packaging note or corrected command using output redirection should explain this behavior.

No mathematical failure was found. The finite computations certify the displayed rational matrices and bounds, not an all-rank asymptotic theorem. In particular, a ratio near \(256\) at rank eight alone cannot exclude a bound \(Cr^p\) with unspecified constants. Likewise the output labels containing the word “supremum” rely on the separate manuscript proof, not on a finite exhaustive search over matrices. This review makes no independent all-rank manuscript verdict or eligibility/literature-priority determination.
