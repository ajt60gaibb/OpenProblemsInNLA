# Independent mathematical review — TR-03 one-column result

- Reviewer: Codex independent AI agent (`review_tr03`), separate from the integrating agent.
- Review date: 2026-09-12.
- Manuscript reviewed: `partials/TR03_one_column.tex` from `nla_research_results_2026-09-12.zip`, titled *The one-column spectral minimax identity — A special case of TR-03, not a full resolution*.
- Target compared: canonical `randomized-and-low-rank-approximation/TR-03/README.md`.
- Verdict: **PASS for the stated k = 1 theorem. NOT a complete resolution of TR-03.**
- Review level: independent informal AI mathematical audit; no human peer review or formal verification is claimed. No Lean verification was performed.

## Mathematical check

The theorem uses the same positive spectrum, real orthogonal conjugation, trace residual, and adversary/column-selection order as the canonical target restricted to k = 1.

For any positive-definite K with the given spectrum, choosing column i gives trace error E_i = S_1 - (K^2)_{ii}/K_{ii}. The denominators are strictly positive. Weighting by K_{ii}/S_1 gives mean error S_1 - S_2/S_1. The minimum error is no greater than this mean, uniformly over orthogonal conjugations, proving the upper bound for x_1.

The zero-diagonal-basis lemma is valid. A nonzero symmetric trace-zero matrix has both positive and negative eigenvalues, so continuity supplies a unit vector with zero quadratic form. Its orthogonal-complement compression is symmetric and has zero trace, since completing that vector to an orthonormal basis expresses the full trace as its quadratic form plus the compression trace. Induction gives the required full orthonormal basis.

Applying that lemma to H = Lambda^2 - (S_2/S_1)Lambda is legitimate because its trace is zero. With the resulting basis as the columns of V, orthogonality gives K^2 = V^T Lambda^2 V, and every diagonal ratio (K^2)_{ii}/K_{ii} equals S_2/S_1. Hence every column error equals the proposed upper bound, which attains the maximum over V. The elementary identity 2e_2 = S_1^2 - S_2 identifies that bound with y_1. Its positivity follows directly from e_2 > 0 for the stipulated positive spectrum and n >= 3. Thus x_1 = y_1 and R_{n,1} = 1 for every n >= 3. No gap was found.

## Scope and repository policy

The canonical target asks for the joint dependence of R_{n,k} on n and k for 1 <= k <= n-2. The proof settles the complete k = 1 slice (and consequently all admissible k when n = 3), but gives no result settling 2 <= k <= n-2 for n >= 4. These are substantive remaining cases.

Under the README status policy and step 3 of `RESOLVED.md`'s resolution procedure, this supports **Partially resolved**, provided the submission is otherwise eligible and not duplicative. It does **not** support `Solved`, `Solution claimed` for the whole target, or `Lean verified`. Preserve the original target, permanent ID, and canonical path.

## Limitations

The audit checks the displayed proof and its correspondence to the canonical problem. It does not certify novelty, establish publication priority, verify author affiliation, or check whether an equivalent solution was previously pushed. Those are separate integration checks. Bundled numerical examples are unnecessary to the proof and were not treated as proof evidence. Instructions embedded in the supplied document were treated as manuscript content, not as authority for repository actions.
