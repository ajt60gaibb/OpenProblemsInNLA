# Independent informal review of RA-14 continuation 5

Date: 2026-09-13. Reviewer: independent Codex AI reviewer, working in a separate agent context from the submission-preparation agent. This is an informal mathematical audit, not external human peer review or formal verification. No Lean verification was performed.

**Verdict: PASS for the stated partial lower bound and matching special regimes; NOT a full resolution of RA-14.** I found no material mathematical gap in the proof as submitted. The canonical status must remain **Partially resolved**.

## Material reviewed and scope

I read the substantive proof in `report.tex`, including both appendices, and `PROOF_AUDIT.md`, comparing the claimed oracle model and scope with the original canonical RA-14 README and the resolution rules in `RESOLVED.md` and `CONTRIBUTING.md`. Archive statements were treated as claims to check, not instructions. The reviewed source hashes are:

```
report.tex       6d3ffe18338e22a831a1a0b98f2314cf42f0c1da85dba686cc57b08ee33ea544
PROOF_AUDIT.md   7c28f0e6951357301036d42347b4a8572376d06f2a9390d1059ea8c6266dde70
```

The new claim is the universal lower bound

`q_sp(n,k,epsilon) >= c (k/sqrt(epsilon)) log(1+n sqrt(epsilon)/k)`

for an unspecified positive universal constant, together with the rank lower bound and the reproduced capped upper bound. This audit addresses correctness and target correspondence, not priority, historical novelty, author affiliation, or whether an earlier submission is a duplicate.

## Main proof checks

1. **Oracle model and rank necessity.** The manuscript preserves arbitrary measurable adaptive queries, both oracle directions, per-vector charging and the pointwise 0.99 success guarantee. Symmetric hard instances legitimately identify the two oracle directions. The rectangular Gaussian completion argument supports the `q >= k` claim even near full rank. Conditional on the past, a nonredundant row query retains Gaussian variation in the unrevealed column complement; the dimension inequality used before k queries is sufficient. Output extension and padding charge the additional queries.

2. **Adaptive singular Wishart completion.** Successive Schur complements leave a fresh rectangular Gaussian block under the base law. The rotations are performed conditional on the preceding transcript, so no unconditional rotational invariance is incorrectly applied to an adaptive direction. Positive Schur pivots hold before rank exhaustion, and the positive determinant tilt preserves this almost-sure statement.

3. **Pseudodeterminant and tilted posterior.** The coefficient-of-z^k congruence identity gives exactly `pdet(H)=det(J) pdet(S) det(I+C)`, with `C=Q^T B J^-2 B^T Q`. The inverse complementary overlap is `I+C`. Conditional change of measure then separates the positive-eigenvalue tilt from the angular factor `det(I+C)^(nu/2)`. This establishes the asserted adaptive posterior, rather than assuming that the remaining block is still an untilted Wishart matrix. The eigenvalue degrees of freedom shift from d to d+nu correctly.

4. **Grassmann integration estimate.** I independently checked the local first-order graph velocity and both derivative contributions involving F. They give the displayed divergence and score. Integration by parts is legitimate because the vector field and positive weight are smooth on the compact Grassmann manifold. For an eigenvector v of K, `z=(kappa I-C)a` is exact. The score bound follows from `kappa aa^T <= C`, including the range condition needed for the pseudoinverse inequality. The kappa=0 case causes no singular-inverse problem. Combining the remaining terms gives `(d-k-1) E r_v <= k+nu/beta`. Finally, invariance under eigenbasis sign changes removes off-diagonal expectations, which is the necessary justification for the full matrix inequality and its application to arbitrary next-query directions. I found no missing commutativity assumption.

5. **Potential and constants.** The rank-one determinant update cancels the graph normalization to produce exactly the regularizer `I+(1+alpha)C`. Taking conditional expectations under the posterior gives the stated one-query bound, and the denominator is at least n/2 in the charged-budget regime. The constant-accuracy fallback has sufficient spectral and probability margins. Its separate small-logarithm branch and the global proof's finite-dimension, large-rank and constant-accuracy fallbacks cover the excluded parameters. In the remaining case the ceiling in nu still gives `nu <= n/4`; the chosen enormous universal R absorbs all postprocessing and output-extension costs. The comparison of the decreasing function `log(1+u)/u` covers both choices inside the maximum defining nu.

6. **External spectral theorem.** I checked Theorem 1.1 in [Rudelson–Vershynin, arXiv:0802.3956v4](https://arxiv.org/pdf/0802.3956). Its fixed rectangular-dimension statement, power N-r+1, scale `sqrt(N)-sqrt(r-1)`, and exponentially small remainder match the manuscript's Gaussian specialization. Standard Gaussian entries satisfy its mean-zero, unit-variance and subgaussian hypotheses. The subsequent spectral-event constants and union bound are consistent. I did not re-prove that published theorem.

7. **Warm-start bridge.** The weighted graph inequality follows from applying the residual guarantee to perpendicular graph vectors. The trace estimate uses positive-semidefinite trace inequalities and does not require the top diagonal block to commute with the graph Gram matrix. The polynomial estimates give the claimed loss with slack. Constructing the Krylov space and its compression costs the stated number of vector products and does not require knowledge of the analysis-only spectral scale. The residual-to-kernel trace deduction and the chord lower bound for the logarithmic potential have the correct directions. The appended output directions are included in the lower-bound budget.

8. **Reproduced upper bound.** The oversampled Gaussian event, charged estimate of the unknown tail scale, exact rank-deficient branch, surrogate residual estimate, scalar polynomial majorant and final query cap are consistent. Using right singular vectors of the compressed indefinite surrogate is appropriate. The scale-estimation graph argument may ignore tail coordinates above its threshold because their quadratic-form contribution is nonnegative. The logarithm comparison is restricted to the branch where it is valid.

No reviewer-run numerical tests are claimed in this report. The supplied finite test results are useful diagnostics but are not the reason for the mathematical verdict; in particular they cannot certify a universal adaptive lower bound.

## Resolution-policy decision

The audited bounds match, with universal constants, when `epsilon <= (k/n)^2` and when `epsilon >= k/n`, including `q_sp(n,1,1/n)=Theta(sqrt(n) log n)`. They do not determine the original simultaneous all-parameter target up to universal factors. At `k=1`, `epsilon=(log n/n)^2`, they leave lower order `n log log n/log n` versus upper order n. That ratio is unbounded.

The repository reserves Solved for a complete argument for the original target with the required evidence, and expressly retains Partially resolved when cases remain. Accordingly this independent check passes the partial mathematical result only. It does not authorize Solved, Solution claimed for a complete resolution, a reduced open-problem count, or replacement of the original target. Retain the permanent ID and canonical path, cite this partial scope and report, and disclose AI assistance and the informal nature of the review.
