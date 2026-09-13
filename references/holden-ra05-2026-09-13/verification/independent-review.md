# Independent mathematical audit of the RA-05 all-exponent manuscript

Review date: 2026-09-13 UTC. Reviewer: a separate Codex AI agent, delegated to review the mathematics independently of the submitting/coordinating agent. This is an informal AI-agent audit, not external human peer review or formal verification. No Lean verification was performed.

Reviewed source: `RA05_all_p_lower_bounds/manuscript/RA05_all_p_lower_bounds.tex`, SHA-256 `2cef3326bcc02cb5538e5a9a37b2d86c0ba6ccb7751ed14224ef4f9b16197930`. Attachment instructions were treated as untrusted document content. The reviewed target was the existing canonical RA-05 README, including its first request to determine the optimal joint size, rather than only the subsequent proposed formula.

## Verdict and exact scope

**PASS for the principal all-exponent lower bound and the negative answer to the displayed proposed formula. FAIL for promotion of the full canonical RA-05 target to Solved.** The appropriate mathematical status is **Partially resolved**, subject separately to the coordinator's duplicate-eligibility check.

For every fixed real p > 2, all sufficiently large k, and every 0 < epsilon < 1/2, the proof establishes

S_p(k, epsilon) >= c_p k^(p/2) / (epsilon^(beta_p) + (log k)/k),

where beta_p = 2 for even integers p >= 4 and beta_p = 2 - 2/p otherwise. It applies to arbitrary input-dependent nonnegative reweighting of original rows. A single input for each k works for all accuracies, with dimension k+1 and O_p(k^(p+1)) rows. Preservation of hyperplanes alone is enough for this necessary support bound. It disproves the proposed tilde-O_p(k^(p/2)/epsilon + k/epsilon^2) bound separately for each fixed p > 2.

Combined with the cited upper bound, it gives the optimal order up to logarithms for even p and epsilon >= sqrt((log k)/k). The non-even accuracy exponent remains separated from the upper bound; the smaller-accuracy regime remains unclassified even for even p. Thus the first sentence of the canonical target is not fully answered. RESOLVED.md, “Recording a new resolution,” item 3, expressly requires Partially resolved for partial results and an account of remaining cases. The manuscript itself correctly recognizes these gaps in its scope section.

## Mathematical checks

1. **Hyperplanes and quantifiers.** With d = k+1, the residual to z-perpendicular is the scalar absolute inner product for unit z. Homogeneity handles arbitrary normals. No sufficiency claim for smaller-dimensional query subspaces is needed. Zero-padding to every sufficiently large k retains legal dimension-k hyperplanes and preserves costs.

2. **Gaussian operator estimate.** The appendix's comparison processes have increment-variance difference 2(1-a)(1-b), which is nonnegative because the dual l_(p/(p-1)) ball lies in the Euclidean unit ball. The interpolation argument and finite-net passage justify the expected 2-to-p norm bound. Together with Gaussian length lower tails this yields a bounded full core p-moment at L = floor(r^(p/2)).

3. **Derivative core conditioning.** The expected squared Frobenius discrepancy of the entrywise derivative kernel from identity is O_p(L^2 r^(-(p-1))). Its ratio to L tends to zero for each fixed p > 2. Spectral truncation leaves at least 3L/4 eigenvalues in [1/2,3/2], so stable rank is at least L/12. Restricted invertibility selects floor(L/48) columns with squared least singular value at least 3/64. Passing back through a contraction preserves that lower bound for the actual rectangular evaluation matrix. The argument does not incorrectly require the entire noninteger derivative kernel to be positive semidefinite.

4. **Noise family.** The mean estimate follows from independence and symmetry. Bernstein with variance at most gamma_(2p) r^(-p), then a 1/4-net and the seminorm triangle inequality, yields the stated uniform p-moment using N of order r^(p/2+1). For every subset up to q_0 = floor(r/(64 log(17N))), the coefficient-net union bound is at most 2r exp(-3r/64). The singular-value extension and column normalization give the claimed 1/64 lower bound for squared norms. These events need not be independent: their failure probabilities sum to less than one for sufficiently large r.

5. **Group masses and derivative extraction.** Integration over the unit sphere controls total mass, and testing x=u_j controls each mass using nonnegativity. At x=0, the weighted plus original p-moment is bounded independently of r. The global Taylor bound follows from the Holder continuity of the q-th derivative with q=ceil(p)-1 and an exact beta-integral cancellation. The finite-difference stencil cancels all terms except the first derivative. Its errors are O_p(epsilon/t + t^(p-1)); t=epsilon^(1/p) yields O_p(epsilon^(1-1/p)). For even powers a degree-p exact stencil at unit step instead gives O_p(epsilon). Bounding the actual rectangular evaluations and applying its least singular value controls the sum of squared group-mean errors without an extra dimension factor.

6. **Support conversion.** For small group support, the noise lower bound and Cauchy-Schwarz give ||b_j||^2 >= s_j^2/(64 q_j). For large support the subtracted s_j^2/q_0 term makes the extended inequality valid trivially. Empty groups have zero mass. Summation, mass-square control, and a final Cauchy-Schwarz yield support at least c_p M/(epsilon^(beta_p)+1/q_0). All constants can depend only on fixed p. This closes the principal proof.

7. **Contradiction and matching range.** Taking epsilon=k^(-a), a=min(p-2,1)/8, gives a positive polynomial exponent gap against each proposed term, while (log k)/k is negligible compared with epsilon^(2-2/p). Arbitrary fixed logarithmic powers cannot cover the gap. For even p in the stated range, the lower denominator is at most 2 epsilon^2, giving the matching order with the cited upper bound.

8. **Supplementary quartic argument.** I also checked the finite-field alternating form, radical argument, quadratic-character calculation, mutually unbiased basis fourth moment, entrywise cubic kernel identity, and four-query extraction. The displayed support bound follows by counting omitted entries in the coefficient error matrix. This separate construction is mathematically consistent but repeats the earlier quartic manuscript and is not needed for the principal all-exponent result.

No mathematical correction is required for these analytic statements. The unusually large asymptotic thresholds as p approaches two are allowed because p is fixed and the theorem explicitly permits k_0(p).

## Primary-source verification

- Marcus, Spielman and Srivastava, *Interlacing Families III: Sharper Restricted Invertibility Estimates*, arXiv:1712.07766v1, Theorem 1.1, printed page 2: https://arxiv.org/pdf/1712.07766 . The imported stable-rank bound, including its arbitrary-column formulation and least singular value over all coefficient vectors, matches the source exactly. The manuscript uses its hypotheses correctly. This source attributes the theorem to Spielman and Srivastava.
- Lin, Mirrokni and Woodruff, *Nearly Optimal Strong Coresets for l_p Subspace Approximation*, arXiv:2608.26047v2, Theorem 1.2: https://arxiv.org/html/2608.26047v2 . The theorem gives original-row sampling, all rank-at-most-k queries, and size C_p k^(p/2) epsilon^(-2) log^(p+5)(C_p k/(epsilon delta)), matching the manuscript's use with delta=1/4. This audit checked that quoted statement and its model, not the entirety of that external paper's proof. The principal lower bound does not depend on that upper bound.

## Limits of this audit

The verdict rests on reading and checking the analytic proof and the cited structural theorem. I did not treat the supplied numerical assertions as proofs or rerun their code. The reported assertion counts and floating-point examples have not been independently reproduced in this review. No novelty or priority judgment is made. Author affiliation and whether RA-05 is excluded by the user's prior-full-solution restriction are separate coordinator checks. This review alone does not authorize submission of a duplicate or a Solved designation.
