# IE-19 independent proof review

Date: 2026-09-11. **PASS — the canonical entrywise inverse-norm inequality is false; the manuscript also proves the sharp replacement infimum for the full stated class.** Recommend **Resolved (counterexample)** for IE-19. No proof correction is required. The stronger problem involving bounds on diagonal-dominance margins is expressly outside this disposition.

## Complete source and target

Read the full standalone recovered `proofs/IE-19.tex`, including its preamble, counterexample, theorem and proof, limiting family, gap formula, and source/scope statements. Full UTF-8 source normalized by CRLF-to-LF replacement only, without trimming: **4313 bytes**, SHA256 **`c55e67662b003622b05d736b7c05556659ca392f7dbc437ef9d3897a99b8bbe7`**.

The recovered provisional label matches the exact current `linear-systems-and-elimination/IE-19/README.md`: n>=3, m>0, alpha>=(n-2)m, S=alpha I+m11^T, J real symmetric with all entries positive, J<=S entrywise, and nonnegative row diagonal-dominance margins. The objective is the induced infinity norm, namely maximum absolute row sum. No Loewner inequality or additional upper bound on the margins appears in that canonical target.

Locators: counterexample Section 1, line 30; Theorem 1 and its proof in Section 2, line 44; source/scope Section 3, line 71. No external TeX file is required.

## Explicit counterexample — PASS

At n=3, m=alpha=1, S has diagonal two and off-diagonal one. J has diagonal two and off-diagonal one-half. All entries are positive, J<=S entrywise, and every diagonal-dominance margin of J equals one, so J is strictly diagonally dominant. These parameters include the allowed boundary alpha=(n-2)m.

The two inverse formulas follow directly from the rank-one inverse formula or matrix multiplication: S^{-1}=I-(1/4)11^T has diagonal 3/4 and off-diagonal -1/4, giving norm 5/4. J^{-1}=(2/3)I-(1/9)11^T has diagonal 5/9 and off-diagonal -1/9, giving norm 7/9. Hence 7/9<5/4 strictly violates the asserted inequality. A single admissible example resolves its universal truth value and invalidates the associated claimed extremizer.

The example does not satisfy a margin inequality Delta_i(J)<=Delta_i(S): its margins are one, whereas those of S are zero. It also has S-J with zero diagonal and positive off-diagonal entries, an indefinite matrix. Thus it must not be relabelled as a counterexample under either that stronger margin hypothesis or a Loewner-order hypothesis.

## Sharp replacement Theorem 1 — PASS for every admissible parameter

For any admissible J, expanding the stated quadratic form yields exactly x^T J x: the row-margin terms and the diagonal contributions from the pairwise squares give J_ii x_i², while the cross terms give 2J_ij x_i x_j. Every coefficient is nonnegative, and each off-diagonal coefficient is strictly positive. If the form vanishes, x_i+x_j=0 for every distinct pair. For n>=3, three indices force each of those coordinates to be zero, and the remaining pair equations force all coordinates to be zero. Hence J is positive definite even if some or all row margins vanish. This proves nonsingularity without importing the generally false assertion that irreducible weak diagonal dominance alone always suffices.

Cauchy–Schwarz applied to J^(1/2)e_i and J^(-1/2)e_i gives `1<=J_ii (J^{-1})_ii`. Equality requires those two vectors to be linearly dependent, equivalent to J e_i being a multiple of e_i. Every off-diagonal entry in that column is positive, so equality is impossible. Thus `(J^{-1})_ii>1/J_ii>=1/(alpha+m)` for every i. The infinity norm is at least any positive diagonal inverse entry, proving the strict universal lower bound and nonattainment at 1/(alpha+m).

Set D=alpha+m. The parameter condition implies D>0 and D>=(n-1)m. For every 0<epsilon<=m, the family `J_epsilon=(D-epsilon)I+epsilon 11^T` has diagonal D and off-diagonal epsilon, obeys the entrywise upper bounds, and is diagonally dominant because D>=(n-1)epsilon. Since n>=3, D-epsilon>0 even at the boundary parameters and epsilon=m. The other eigenvalue D+(n-1)epsilon is also positive.

The inverse is

`J_epsilon^{-1}=(D-epsilon)^(-1)I - epsilon/[(D-epsilon)(D+(n-1)epsilon)] 11^T`.

Its diagonal is positive and its off-diagonal entries negative. The absolute row sum therefore equals the manuscript's numerator `D+(2n-3)epsilon` divided by `(D-epsilon)(D+(n-1)epsilon)`. Taking epsilon down to zero gives 1/D. Every member of the approximating family retains strict entrywise positivity, whereas the limiting diagonal matrix does not belong to the class. This proves that the strict lower bound is exactly the infimum and is not attained.

Putting epsilon=m recovers S. Subtracting 1/(alpha+m) from the proposed value and collecting the numerator gives `(n-1)m(alpha+2m)`, with the positive denominator printed in the manuscript. The gap is strictly positive for all allowed n,m,alpha, including alpha=(n-2)m. Thus an entire admissible family approaches values below the conjectured value, rather than the failure being confined to a special singular or degenerate parameter choice.

## Exact code and independent verification

Read the relevant `ie19` function of `verification/checks.py` and its arithmetic in `exact.py`. The explicit inverses, entry bounds, strict row dominance in the example, parameter-family norm values, and algebraic gap are checked with rational arithmetic. Finite parameter samples are supplementary checks; the universal proof and nonattainment follow from the analytic argument above.

The independent reviewer script `verification/reviewer_ie17_19.py` imports no submitted code and recomputes the three-by-three inverse via Cramer's rule with permutation-expanded determinants. It confirms the exact infinity norm 7/9. Its output is saved in `reviewer_ie17_19.json`. The inverse formula for S and the universal family were also independently expanded during this review. The parent task handles separate supplied-program reruns.

## Primary-source comparison and disposition

The [Hillar–Lin–Wibisono primary preprint, opening notation on p. 2 and Conjecture 8.1 on p. 17](https://arxiv.org/pdf/1203.6812) explicitly distinguishes the Loewner order from entrywise ordering and displays the same entrywise conjecture. The preceding motivation discusses upper bounds on off-diagonal entries and on dominance margins; those stronger assumptions imply the displayed entry bound but are not equivalent to it. The counterexample addresses the displayed conjecture and current canonical as written. It does not settle the potentially intended stronger question, and no claim about the separate determinant conjecture is needed.

**Final scope: PASS for the complete recovered IE-19 proof, a negative resolution of the canonical entrywise inequality, and the sharp nonattained infimum 1/(alpha+m) over its exact admissible class.** Any update should preserve the original hypotheses and make the order distinction explicit. This audit is not a publication-priority determination.
