# Independent review of MD-03 and MD-04

Date: 11 September 2026. Reviewer: a separate Codex agent assigned to audit the submitted note, independently of the agent preparing the repository changes. This is an AI-agent mathematical review, not external human peer review or a formal proof certificate.

## Verdict

**PASS for both exact catalog targets, at the level of independent agent review.** The submitted applications are correct. I also audited the substantive argument in the cited primary manuscript and found no blocking mathematical gap. This is stronger than checking only that two theorem statements match, but it is not a guarantee that subsequent scrutiny will find no error.

A repository status of **Solved — independent agent review** is supportable under the present `RESOLVED.md` definition, provided the entry credits the original authors and explicitly describes the verification level. George Stepaniants is the author of the explanatory application note; he is not the author of the two original discrepancy theorems. The supplied note's qualification about relying on a preprint should remain.

## Materials and exact scope

I read the local canonical README statements for MD-03 and MD-04 and the supplied LaTeX note. At this review's local snapshot, MD-03 is Open and MD-04 is Partially resolved; the unrestricted targets survive. Repository-network status and duplicate-submission checks are being handled separately by the submission agent.

The [current arXiv record](https://arxiv.org/abs/2609.11189) identifies Shengtao Guo, Ethan X. Fang and Junwei Lu, with only version 1 displayed, submitted 10 September 2026, and no withdrawal notice. The [versioned PDF](https://arxiv.org/pdf/2609.11189v1) places Theorem 1.1 on page 1 and Corollary 1.2 on page 2. The constant is 3√(2π). The paper discloses Odin AI use. Its [full text](https://arxiv.org/html/2609.11189v1) was read through Sections 2–4 and Appendix A.

For MD-03, setting each vector equal to the corresponding matrix column checks the entire hypothesis; the signed sum is exactly the matrix-vector product. The conclusion is stronger than the requested non-strict inequality. For MD-04, the incidence-column assumption matches the corollary exactly. Independently, dividing the matrix by √t verifies the reduction to MD-03 since each normalized squared column norm is at most one. All positive dimensions and allowed sparsities are covered; no algorithmic claim is needed.

## Checks beyond theorem matching

I checked the source argument's dependency chain, including support boundaries, degenerate directional energies, simultaneous rather than direction-dependent density selection, and the preservation of one numerical bound during every finite transform. No step requires a uniform constant in auxiliary approximation parameters where only a fixed-parameter compactness argument is available.

In particular, the reciprocal-power eigenvalue theorem used in the convexity step was checked against the actual [Wang–Xia author manuscript](https://www.researchgate.net/profile/Chao-Xia-9/publication/292488182_A_Brunn-Minkowski_inequality_for_a_Finsler-Laplacian/links/56b3f93508ae636a540d2222/A-Brunn-Minkowski-inequality-for-a-Finsler-Laplacian.pdf), Theorem 1.2, with matching normalization and hypotheses. Its conclusion implies ordinary convexity: apply the decreasing function r↦r^(-p) and the convexity of that same function to the weighted mean of the two reciprocal-power eigenvalues. The regularized integrands satisfy the published theorem's smoothness and convexity assumptions. Thus the crucial step has a published independent input and does not depend exclusively on the new appendix.

I checked the p→1 limit using fixed smooth test functions for the upper bound and the normalized |f|^p test for the lower bound; these are taken before the integrand regularization limit. I checked the finite-dimensional separation argument and the subsequent coordinate-BV compactness argument, which together provide one density for every direction. Slice normalization uses slice mass as its weight, and the mean height lies strictly within the projection interval, so the equality case does not select an empty section.

The rearrangement calculation was checked for its level-variable and overlap normalizations; the scalar integrals giving the height loss are consistent. The transform containment and reverse sign reconstruction cover every vector. The cube-density calculation keeps the global boundary derivative and gives the advertised dimension-independent estimate. The resulting strict cube containment yields the announced constant.

## Attribution and limitations

Retain Guo, Fang and Lu as the original theorem authors in each canonical resolution entry and the shared submission record. Credit George Stepaniants for the application note only. Retain the source's AI provenance and the supplied note's preprint qualification. Do not describe this as a refereed resolution, a formal verification, a polynomial-time construction, or a new discrepancy theorem by George.

No numerical experiment can establish the universal statements here, so this review used mathematical and primary-source checks rather than treating examples as proof. I did not re-prove the published Wang–Xia theorem from first principles or independently establish external community acceptance. Those limits do not expose a mathematical gap in the supplied applications or the reviewed new argument, but they must not be concealed when recording the status.

## Attributed source check and mathematical core fingerprint

I re-read `references/stepaniants-2026-09-11/manuscripts/md03_md04_proofs.tex` after attribution and independent-review statements were added. Both theorem applications remain correct, and the attribution correctly makes George Stepaniants the application-note author while retaining Guo, Fang and Lu as the original theorem authors. The mathematical core is byte-identical to `md03_md04_original_user_source.tex`.

The hashed byte range starts at the first `\section{MD-03` and ends immediately before the first `\paragraph{Attribution and scope`; it includes all intervening source bytes and whitespace. Its length is 2052 bytes. SHA-256: `f600ec82ae76dcc6c9cbb9f9ce067066032de70864e532403614f0583bc4ab4f`. This fingerprint excludes title, author, review-status and layout material outside that range. Any subsequent layout change inside the range requires a new hash, even if the mathematics is unchanged.

## Author-contact redaction — 11 September 2026

At the author’s request, the contact-address line was removed from the public byline. George Stepaniants, the Department of Computing and Mathematical Sciences and the California Institute of Technology remain. Only the source’s author block changed; every byte from `\begin{document}` through the end of the document is unchanged. The previously reviewed mathematical-core hash above therefore remains valid.

Previous complete source SHA-256: `22e421f243a61c6b56275e8e3d27366ad0517c5e0f9e45401850e69ee4f530c6`.

Current complete source SHA-256: `8bad48796fd3608e65c12123db561c9f29d41d912edfe4c5d024540465030f2b`.

Unchanged complete document-body SHA-256: `4610299e6267c35035b3a84154cee7492952d619c3e31eb432a35b0d4a30aa8e`.

The PDF was rebuilt twice with pdfLaTeX without warnings, and all 2 pages were independently visually inspected after the edit. Text extraction, PDF metadata, annotations and decoded PDF objects were checked for the author’s email address, with no matches. The full branch-added text and PDF inventory was also checked. These metadata-only edits do not alter the mathematical PASS verdict. Historical source hashes are retained explicitly here and in the document-check record.

Redaction and preservation reviewer: independent Codex agent `/root/prepare_manuscripts`, 11 September 2026.
