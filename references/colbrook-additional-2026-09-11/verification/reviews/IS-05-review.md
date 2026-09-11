# IS-05 independent mathematical review

**Verdict: PASS (partial only).** Both stated parity bounds and their consequence `alpha_* <= 1/2` follow from the argument. No mathematical gap was found. This does **not** determine the canonical exact exponent and does **not** justify marking IS-05 solved. Novelty and priority are not certified.

Review date: 2026-09-11. Reviewer: independent Codex review agent, assigned specifically to audit IS-05; this is an AI mathematical review, not external human peer review or a formal proof-assistant certificate. The manuscript and canonical statement were read without editing either file.

## Reviewed objects and identity

- Original manuscript: `.cache/colbrook-additional-submission/nla_additional_submission/manuscripts/IS-05-partial-result.md`, title *Parity obstructions for the conditioning of sign matrices*, 122 lines.
- Canonical target: `eigenvalues-and-inverse-problems/IS-05/README.md`, especially lines 16–38 (definition and exact-exponent target), lines 42–47 (sources), and line 59 (scope of resolution).
- SHA256 of the **full original manuscript**, including YAML metadata, opening disclaimer, all mathematical content and sources, after replacing CRLF by LF and encoding as UTF-8 without adding a BOM:

  `2ec73d60756aa0a50db50187b43b8365cd902e4ed34a3af3cd7fef37d5f7208d`

- Normalized byte count: **5746**. The original already has LF line endings; its raw-byte SHA256 is the same. No trimming, rewriting, Unicode normalization, or final-newline removal was performed.

All manuscript line references below refer to that exact original. A subsequent version with different metadata or prose has a different identity; this report does not certify unreviewed changes. Mathematical sections preserved verbatim retain the reasoning audited here.

## Match to the canonical question

Manuscript lines 17–26 reproduce the repository's class of real square sign matrices, spectral condition number, singular-matrix convention, and supremum with quantifiers `exists C > 0, for all n >= 1`. In particular, the constant can depend on the chosen exponent but cannot depend on dimension. The proof never replaces this uniform target by a favorable subsequence or by a pointwise choice of constant.

Theorem 1 is a lower bound for every matrix at each odd order. Taking the minimum over matrices therefore preserves it. A lower bound along all odd dimensions is enough to obstruct a proposed upper estimate that must hold at every dimension. Exact Hadamard orders, where `h(n)-1=0`, cause no conflict and are not used in a logarithm or denominator.

The interval at manuscript line 111 follows from the proved obstruction and the cited construction bound. It is an interval containing the target, not an exact value. The opening disclaimer (line 13) and remaining-work statement (line 113) correctly describe this limitation.

## Detailed verification of Theorem 1

**1. Spectral setup and variance: lines 44–48, equation (4).** For a nonsingular real sign matrix, `G=A^T A` is real symmetric positive definite. Thus `0 < m <= lambda_i <= M`, and `t=M/m=kappa_2(A)^2 >= 1` is well-defined. Each diagonal entry is the squared norm of a sign column, hence equals `n`; consequently `tr(G)=n^2` and the eigenvalue mean is `n`. The spectral theorem gives

\[
v=\frac1n\sum_i(\lambda_i-n)^2
 =\frac1n\operatorname{tr}\big((G-nI)^2\big)\ge0.
\]

The notation `tr(G-nI)^2` in the manuscript is read as the trace of the squared matrix, consistently with the displayed eigenvalue sum. It is not the square of the trace. Writing the parentheses explicitly would improve typography but is not a proof gap.

**2. Variance bounded by the spectral endpoints: lines 50–53.** Average the nonnegative products. Direct expansion yields

\[
\frac1n\sum_i(M-\lambda_i)(\lambda_i-m)
 =(M+m)n-Mm-(v+n^2)
 =(M-n)(n-m)-v\ge0.
\]

This proves the claimed inequality with the stated direction and normalization.

**3. Optimization at fixed ratio: lines 54–58, equation (5).** Substituting `M=tm` gives the exact identity

\[
(tm-n)(n-m)
=-t\left(m-\frac{n(t+1)}{2t}\right)^2
 +\frac{n^2(t-1)^2}{4t}.
\]

As `t>0`, discarding the nonpositive square is valid. No assumption that an optimizing spectrum is realizable by a sign matrix is required for an upper bound. In fact, the vertex lies in the necessary interval `n/t <= m <= n`, although even this fact is unnecessary for the unrestricted maximum used in the manuscript.

**4. Conversion back to condition number: lines 59–66, equation (6).** Because `t=kappa^2` and `kappa>=1`, equation (5) is

\[
v\le\frac{n^2}{4}(\kappa-\kappa^{-1})^2.
\]

Both sides used in taking square roots are nonnegative, so `kappa-kappa^{-1} >= 2 sqrt(v)/n`. Put `x=sqrt(v)/n >=0` and multiply by positive `kappa`. The resulting quadratic inequality `kappa^2-2x kappa-1 >=0` forces

\[
\kappa\ge x+\sqrt{1+x^2}.
\]

The other root is negative and cannot be the positive condition number. When `t=1`, the same argument yields `v=0` and `kappa=1`; no division by `t-1` occurs.

**5. Odd-order parity and the minimum: lines 70–75, equation (7).** Every off-diagonal Gram entry is a sum of `n` numbers in `{+1,-1}`. For odd `n` it is an odd integer, hence has square at least one. Since `G-nI` is symmetric and has zero diagonal,

\[
\operatorname{tr}\big((G-nI)^2\big)
=\sum_{i\ne j}g_{ij}g_{ji}
=\sum_{i\ne j}g_{ij}^2\ge n(n-1).
\]

There are `n(n-1)` ordered off-diagonal entries, so `v>=n-1`, with no missing factor of two. The right-hand side of equation (6) is increasing in `v>=0`, proving equation (2). Subtracting one and using `sqrt(1+(n-1)/n^2)>=1` proves the first inequality of (3). For `n=1`, this reduces to `kappa>=1` and `h(1)-1>=0`, which are correct.

**6. Supremum obstruction: lines 77–82.** Fix any `alpha>1/2` and suppose its dimension-independent constant exists. Along odd `n`,

\[
C\ge n^\alpha(h(n)-1)
\ge n^{\alpha-1}\sqrt{n-1}
=n^{\alpha-1/2}\sqrt{1-1/n}\longrightarrow\infty.
\]

This is a contradiction for every such fixed exponent. Thus no admissible exponent exceeds `1/2`, and their supremum is at most `1/2`. The proof does not assert that the supremum is attained.

The nonsingular hypothesis is used precisely where `m>0` is needed. Singular matrices have infinite condition number, so their inclusion in the finite set over which the minimum is taken cannot invalidate a lower bound. There are also nonsingular sign matrices in every order: `[1]` for `n=1`, a Hadamard matrix for `n=2`, and `J-2I` for `n>=3` (eigenvalues `n-2` and `-2`). Thus `h(n)` is finite at each fixed dimension; no hidden empty or exclusively singular minimization occurs.

## Detailed verification of Theorem 2

**7. Triangle-free orthogonality graph: line 93.** The graph is simple and has the `n` distinct column positions as vertices. If three columns are pairwise orthogonal, multiplication by a diagonal sign matrix makes the first column all ones and preserves all inner products. Orthogonality forces the second column to split the rows into two sets of size `n/2`. If the sums of the third column on these sets are `s_+` and `s_-`, its orthogonality to the first and second gives `s_++s_-=0` and `s_+-s_-=0`. Both sums must be zero. Each is a sum of `n/2` signs, so `n/2` must be even. This contradicts `n=2 mod 4`. The asserted absence of a triangle is proved for every such dimension.

**8. Edge count: line 95.** For any edge `uv` in a triangle-free graph the open neighborhoods `N(u)` and `N(v)` are disjoint, so `d_u+d_v<=n`. Summing once per edge yields

\[
\sum_vd_v^2=\sum_{uv\in E}(d_u+d_v)\le ne.
\]

Cauchy–Schwarz and the handshake identity yield `sum_v d_v^2 >= (2e)^2/n`. If `e>0`, division gives `e<=n^2/4`; if `e=0`, the assertion holds directly. This is a complete proof of the needed triangle-free edge bound, without an unproved extremal-graph assumption.

**9. Gram-entry count and substitution: lines 97–105.** There are `n(n-1)/2` unordered column pairs. At most `n^2/4` are orthogonal, leaving at least `n(n-2)/4` nonorthogonal pairs. Here `n` is even, so each nonzero inner product is a nonzero even integer and its square is at least four. Each unordered pair contributes twice to the trace sum. Therefore

\[
v\ge\frac{2}{n}\,4\,\frac{n(n-2)}4=2(n-2).
\]

The substitution into equation (6) gives exactly equation (8). For the edge case `n=2`, the bound is `kappa>=1`, consistent with a 2-by-2 Hadamard matrix. For larger dimensions in this residue class, the leading obstruction for `kappa-1` is `sqrt(2)/sqrt(n)`. No claim for positive obstruction at multiples of four is made or needed.

## Primary-source comparison and dated bibliography note

The manuscript's cited [Alexeev–Jasper–Mixon v1](https://arxiv.org/html/2511.14653v1), dated 18 November 2025, has the construction estimate for every positive exponent below `17/92` in §2, Theorem 1 and its following paragraph; the obstruction `c log(n)/n` in §3, Theorem 6; and the interval `17/92 <= alpha <= 1` in §6, Problem 11 and the following paragraph. These support the manuscript's account of its historical starting interval. This review's elementary `n^(-1/2)` obstruction is asymptotically larger than `log(n)/n`, since their ratio tends to infinity. This comparison establishes an improvement over the displayed cited bound, not priority over all literature.

**Currency note, checked 2026-09-11:** [The arXiv record](https://arxiv.org/abs/2511.14653) lists v2 on **18 August 2026**, at 17:21:58 UTC. [Version 2](https://arxiv.org/html/2511.14653v2) preserves the relevant bounds: §2, Theorem 1 and the following paragraph (HTML lines 68–72); §3, Theorem 6 (lines 178–180); and **§5, Problem 11 and its immediately following paragraph** (lines 247–251). The last locator replaces §6 in v1. A dated note citing v2 is appropriate; retaining the original v1 reference as historical provenance is accurate. No conflict with the partial result was found in these current source statements.

For the canonical all-dimensions formulation, any sufficiently-large-dimensions construction estimate with exponent `beta<17/92` extends to every dimension by increasing its constant over the finitely many smaller orders. Finiteness of `h(n)` was established above. Letting `beta` approach `17/92` then proves the lower bound on the **supremum**; it does not require an estimate at the endpoint exponent itself. Consequently the combination with Theorem 1 gives

\[
\boxed{\frac{17}{92}\le\alpha_*\le\frac12}.
\]

The cited Steinerberger PDF could not be retrieved by the browser tool in this review. Its current contents were not independently verified here, and no claim in this verdict depends on that PDF. Searches for later parity/conditioning results did not supply an additional relevant primary source; that limited search is not proof of novelty or of the absence of subsequent work. The external construction theorem was checked as the cited input, not re-proved from its Hadamard-construction dependencies.

## Remaining question and verification limits

The canonical task still asks for the exact value of `alpha_*`. The manuscript gives neither a matching uniform construction nor a stricter obstruction meeting the existing construction bound. To establish `alpha_*=1/2`, upper estimates for every exponent below `1/2` would suffice; an endpoint `O(n^(-1/2))` estimate is stronger than necessary because the target is a supremum. The manuscript proves no such family of upper estimates. Constructions restricted to a favorable infinite subsequence would also be insufficient for that step.

No numerical search, eigenvalue rounding, randomized test, or reported verification-script output was used as a premise for this verdict. Every asserted all-orders step was checked algebraically above. The original verification script was not independently executed as part of this proof audit; small-dimensional tests could only provide implementation checks, not establish either theorem or the exponent obstruction. No formal proof-assistant verification or exhaustive novelty review was performed.

Recommended classification: **Open with an updated bounds notice**, or **Partially resolved** if the repository uses that category. **Solved is not supported.** No mathematical repair is required for the two partial theorems; a current v2 bibliography note and optional explicit trace parentheses are editorial improvements only.
