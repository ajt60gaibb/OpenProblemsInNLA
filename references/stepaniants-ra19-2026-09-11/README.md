# RA-19 submission record - 11 September 2026

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

**Affirmative resolution:** the complex smooth-locus critical-point count is exactly $5n-7$ for every integer $n\ge3$. The complete proof has passed a separate independent Codex-agent review without a required mathematical correction.

- [Original canonical target and resolution](../../randomized-and-low-rank-approximation/RA-19/README.md).
- [Complete proof: Theorem and Sections 1-5](../../randomized-and-low-rank-approximation/RA-19/solution.md), [standalone XeLaTeX source](../../randomized-and-low-rank-approximation/RA-19/solution.tex), and [PDF](../../randomized-and-low-rank-approximation/RA-19/solution.pdf).
- [Frozen reviewed proof](verification/reviewed-proof.md) and [original canonical page](verification/original-target.md).
- [Independent complete-proof review](verification/independent-review/review.md), [review manifest](verification/independent-review/review-manifest.json), and [separate coordinating-agent audit](verification/RA-19-root-math-review.md).
- [Reviewer-written universal polynomial checker](verification/independent-review/universal_algebra_check.py) and [its exact output](verification/independent-review/universal-algebra-check.json).
- [Supplementary finite exact checker](verification/exact_check.py) and [output](verification/exact-check.json).
- [Primary-source scope check](verification/primary-source-check.md), [bounded public-network audit](verification/network-check.json), and [read-only reproduction script](verification/network_check.py).
- [Portable source and target checker](verification/check_submission.py), [source-check output](verification/source-checks.json), and [document verification record](verification/document-checks.json).

## Exact result and attribution

The proof addresses the original variety of complex square singular matrices with $x_{11}=0$, the bilinear squared Frobenius distance, generic complex input data, and critical points on the smooth locus. It constructs the spectral polynomial $P=h-2gz-fz^2$ and stationarity equation $E=P_z/2+zP_\lambda$. The exact resultant has degree $5n-7$. A critical-point bijection, the translated normal-bundle argument for generic reducedness, and a simultaneous nonempty-open-set witness in every dimension ensure that this degree counts distinct valid critical points. Section 6 explains the pre-existing dimension-two exception.

The conjecture and finite supporting computations remain attributed to Kubjas, Sodomaco and Tsigaridas, *Exact solutions in low-rank approximation with zeros*, Linear Algebra and its Applications 641 (2022), 67-97, [DOI 10.1016/j.laa.2022.01.021](https://doi.org/10.1016/j.laa.2022.01.021). The exact locator is Conjecture 5.1 and Table 2, printed page 19 of [arXiv:2010.15636v2](https://arxiv.org/pdf/2010.15636v2); Section 2 establishes the distance and critical-point conventions. The canonical target already excludes the reducible dimension-two endpoint. Counts of real critical points and other zero patterns are not claimed.

## Authorship, assistance and review level

The proof was developed with substantial ChatGPT/Codex assistance at the author's request. The discovery agent, independent mathematical reviewer, and coordinating reviewer are distinct roles. The independent reviewer reconstructed the complete proof and implemented its own symbolic check of the universal reduction and resultant identities, without reading, importing or executing the discovery agent's checker for that audit. These informal automated reviews do not establish external human peer review, formal proof-assistant verification, or novelty and priority.

The frozen full candidate has 19,069 bytes and SHA-256 `475e29760333fc215e80eed33e4729649383d112d585d7cca88a8b669b618c22`. Its original preparation-stage status and pending-public-audit wording remain as historical text. Publication metadata records the subsequently completed checks. The mathematical core is Sections 1-6, 17,059 bytes, SHA-256 `9b7c3293548e04b0dc474ac6de34499b398e07d2a98500fa2c7ba892c6981cb5`. The canonical Markdown preserves that core exactly apart from explicit raw page-layout directives.

The signed independent review is 12,398 bytes with SHA-256 `ddb4ecca8fe6b2844a6559dcefe13462291d165c43076d05ce25b47b94de7da4`. Its signed textual review bundle is preserved intact, with byte-identical `verification/RESULT.md` and `verification/canonical-target.md` in the parent directory so its relative links and checker source binding remain valid. The two third-party primary-page inspection images remain private; their hashes and source location are in [the inspection-image record](verification/private-primary-images.json), and no unverified reuse license is assumed. The coordinating audit is 8,943 bytes with SHA-256 `3dcc41bab81d059b851570e8ef86d44faa7f4cdc83376929de6a1a0b17a98095`. The separate [publication-conversion review](verification/RA-19-publication-conversion-review.md) is complete: all 281 ordered core formulas and the full retained target are unchanged, and all nine final PDF pages passed coordinating-agent inspection.

The reviewer's standard-library checker works over the formal ring $\mathbb Z[f,g,h,f',g',h']$. It independently expands all four coefficients in the remainder identity and the 120-term permutation determinant of the Sylvester matrix. This confirms the universal polynomial identities, not the geometric proof as a formal theorem. The discovery agent's separate finite checker verifies explicit integer examples in orders 2-6; only orders 3-6 exclude the singular-completion point, as predicted. These finite examples are supplementary, not an all-dimension argument. The original finite checker is retained unchanged; the portable copy changes only the adjacent source filename and its descriptive scope string.

## Eligibility and repository procedure

At 00:40:42 UTC on 12 September 2026 (11 September locally), the read-only audit covered five recursively discovered public repositories, all 37 branch heads, and every canonical or RA-19/corank-one-named selected text file. The 35 distinct heads contained two distinct relevant text blobs. Every existing canonical RA-19 page was Open; older branch heads predated its admission. The only matching issue/PR discussion was merged admission PR 111, which admitted RA-19 as Open and resolved the different RA-20 target. No full RA-19 resolution was found. The snapshot contains branch and blob identities, canonical contents, and discussion metadata with body hashes; unrelated profile fields and discussion text were removed. The original private snapshot hash is retained.

This is a bounded public check. Private, deleted, unpublished, or unidentifiably named work is outside its scope. The current arXiv record still lists version 2, and bounded exact-title, conjecture-number, single-zero and later-proof searches found no subsequent complete resolution. The portable network checker uses GitHub CLI from `GH` or `PATH`, makes only read calls, and requires an explicit new output path.

The isolated branch starts directly at upstream `main` commit `1f22006bdaa4659fcaa0bb775a887685cd3cc566`. It preserves all 217 permanent ID mappings, the canonical path, the complete original Statement-through-history suffix, and historical ratings. The intended submission is a correction-or-resolution issue and a new pull request into upstream `main`, with maintainer review requested. Packaging alone performs no commit, push, issue creation or pull-request creation.

Reproduce the document builds with `python3 tools/render_solutions.py RA-19` and `python3 tools/render_problems.py RA-19`, using Pandoc and XeLaTeX. Both generated TeX files compile standalone. The portable source checker verifies the frozen proof and review hashes, unchanged mathematical core, ordered TeX formulas, complete original target suffix, registry mappings and local evidence links. The document verification record records the completed builds, safeguard tests and all-page visual inspection.

## Final publication check

A [fresh public eligibility scan](verification/network-prepublication-2026-09-12.json) completed at 01:03:45 UTC on 12 September 2026. All 37 branch heads across five repositories still had RA-19 Open wherever present; the only matching discussion remained admission PR 111. The [completed publication-conversion review](verification/RA-19-publication-conversion-review.md) and [final verification record](verification/final-publication-checks.json) supersede the earlier packaging-stage pending review. All six canonical artifacts are unchanged from the frozen handoff.
