# MF-06: current public eligibility and primary-source audit

**Disposition: no already-public full resolution of the original MF-06 target was found in this bounded audit.** The complete canonical target remains marked **Partially resolved** at every returned public branch head. The reviewed manuscript is eligible to proceed to submission on this evidence, subject to the maintainer's assessment. This is not an exhaustive novelty or priority certification.

Audit by the separate Codex agent `review_aa01`, 12 September 2026. This report supplements, and does not replace or modify, the frozen independent full mathematical review. It concerns the clarified candidate of 15,842 bytes with SHA-256 `11fce1e0012b8e514890fa6a116b8d91b91f56f5b7cd0ae20199006b4a18ca94`.

## Public network and exact target

The live retrieval finished at **2026-09-12 05:04:43 UTC**. Starting from `ajt60gaibb/OpenProblemsInNLA`, the GitHub API returned six public repositories after recursive fork enumeration:

- `ajt60gaibb/OpenProblemsInNLA`
- `MColbrook/OpenProblemsInNLA`
- `bonans/OpenProblemsInNLA`
- `k1monfared/OpenProblemsInNLA`
- `sgstepaniants/OpenProblemsInNLA`
- `yuningyang19/OpenProblemsInNLA`

The check retrieved all **49 public branch heads**, representing 43 distinct commit heads. The upstream `main` was `1f22006bdaa4659fcaa0bb775a887685cd3cc566`. Every MF-06 canonical README had Git blob SHA `9f4b0b2ba3cbaf0e4721bde49a4d5d78b4c45736`, 2,607 bytes, SHA-256 `fe32efa1f84a750039f65695f3cadbf615ead558826490e53329ca26704df741`. I compared that content byte-for-byte with the canonical target used in the independent proof audit; it is unchanged. [Exact upstream canonical version](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/1f22006bdaa4659fcaa0bb775a887685cd3cc566/matrix-functions-and-stability/MF-06/README.md).

The target is the pointwise, one-sided exponent-one perturbation estimate for every fixed nonempty compact family of complex matrices and arbitrary sufficiently close nonempty compact families. Constants may depend on the fixed reference. The recorded partial case is irreducible families; a local exponent-$1/d$ two-family theorem, a polynomial trajectory estimate, or a result about the *lower* joint spectral radius does not settle this assertion.

## Documents and discussions examined

Recursive Git trees were checked for truncation. The audit retrieved and searched **153 distinct text blobs**, comprising the canonical pages, root catalog/status indexes, and text files whose paths identify MF-05/06/07, JSR, joint spectral radius, marginal growth, product boundedness, nonresonance, Barabanov norms, exterior powers, or Lipschitz estimates. There were 42 non-root path/version entries in this selection. All immutable cached text was verified against its Git blob object SHA-1; forks, branches and discussions were fetched afresh. Thirty-seven text blobs required new retrieval.

All issue/PR bodies and repository issue comments and review comments returned by paginated API endpoints were searched: **177 records**, plus **32 PR review bodies from 39 PR review endpoints**. The nine matching discussion items were read and classified. The repositories all reported GitHub Discussions disabled. The sanitized record retains the URL, title, body length/hash and my disposition for each match, without its retrieved body.

The relevant existing submission is [PR 110](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/110), with issues [107](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/107), [108](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/108), and [109](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/109). It concerns Matthew J. Colbrook's MF-05/MF-07/MF-12 results. I inspected the repository manuscript's theorem and scope statements as well as the related discussions: MF-05 is an exponent-$1/d$ Hölder estimate, MF-07 is a uniform trajectory bound, and MF-12 concerns prescribed growth exponents. The submission and its review expressly exclude MF-06. Its existence and attribution should remain visible; it is not a competing full solution here. [Attributed JSR/growth submission record](https://github.com/MColbrook/OpenProblemsInNLA/blob/7d00fde9b72f55268dca3c61cd57e93085aeec87/references/colbrook-jsr-growth-2026-09-11/README.md).

The remaining matches were an MF-05/07/12 merge request, its scope-qualified review, MI-28 determinant/exterior-power material, and a KE-03 eigenvalue-query result. None asserted the MF-06 conclusion. No MF-06 solution manuscript or resolution claim was found among the selected branch documents.

This scope does not cover private, deleted, unpublished, unreturned or unidentifiably named work. Keyword inspection is a bounded search, not a proof that no other public document could contain the result. The recorded timestamp matters because branches and discussions may subsequently change.

## Primary sources and overlap

The source query log and precise locators are in [source-check.json](source-check.json). The technical conclusions below use primary papers rather than search-result summaries.

**Original target.** The latest arXiv record for [Epperlein–Wirth, *The joint spectral radius is pointwise Hölder continuous*](https://arxiv.org/abs/2311.18633) still lists v2, 25 February 2025. Its [§2, Conjecture 3(P2)](https://arxiv.org/html/2311.18633v2) states the full pointwise exponent-one lower bound. Its §3 also records the standard extremal-norm input. The journal reference is *Linear Algebra and its Applications* 704 (2025), 92–122, DOI [10.1016/j.laa.2024.09.016](https://doi.org/10.1016/j.laa.2024.09.016).

**Standard norm theorem.** I directly inspected Wirth's [author-hosted primary manuscript](https://www.fim.uni-passau.de/fileadmin/dokumente/fakultaeten/fim/lehrstuhl/wirth/Publikationen/gsr.pdf), Theorem 1.1 on manuscript page 4, with the real/complex field convention on page 2. It credits Barabanov and gives precisely the compact irreducible extremal/Barabanov norm used in Lemma 5. Cite Fabian Wirth, *The generalized spectral radius and extremal norms*, LAA 342 (2002), 17–40, DOI [10.1016/S0024-3795(01)00446-3](https://doi.org/10.1016/S0024-3795(01)00446-3). The manuscript's positive-radius irreducible blocks meet that input's required scope.

**Prior nonresonance theory requires credit.** Chitour, Mason and Sigalotti's [*On the marginal instability of linear switched systems*](https://www.ljll.fr/sigalotti/doc/chitour_mason_sigalotti-SCL.pdf), SCL 61 (2012), 747–757, DOI [10.1016/j.sysconle.2012.04.005](https://doi.org/10.1016/j.sysconle.2012.04.005), already develops nonresonance as a boundedness mechanism. Relevant locators are Definition 6/Proposition 9, pp. 749–750; Theorem 10, p. 750; the discrete-time §6/Theorem 20, p. 754; and Appendix Lemma 28, p. 757. The appendix controls transition sums through decay of pairwise products, closely overlapping the role of Lemmas 2–4. These are prior ideas, even though the candidate supplies a direct complex, paired-tensor formulation. I found no maximal-critical-exterior-power perturbation conclusion in that paper. This comparison does not substitute its real-system theorem for the candidate's independently checked complex proof.

**Resonance must not be reversed.** [Protasov–Jungers, arXiv:1411.0497v1](https://arxiv.org/html/1411.0497v1), §§1–3, disproves general sufficiency claims for resonance and gives a criterion under additional dominant-word hypotheses. It does not undermine the necessity/nonresonance direction used here, and it does not establish MF-06. The candidate never infers instability merely from a paired radius equal to one.

**Earlier exterior-power techniques.** [Morris, arXiv:0909.2800v1](https://arxiv.org/pdf/0909.2800), §3.3, Lemma 3.2 on PDF page 10, characterizes a rank-one property by a second-exterior spectral gap *assuming relative product boundedness*. That assumption distinguishes it from the candidate's critical-power existence step. [Berger–Jungers, HSCC 2020](https://guberger.github.io/assets/papers/10.1145_3365365.3382195.pdf), §3, uses exterior-family JSRs for switched-system entropy. Exterior-power lifting itself should not be presented as newly invented. Neither inspected source supplies the full target or the candidate's maximal-degree allocation argument.

**Later work by the target's authors.** The latest observed arXiv version of [*Auerbach bases, projection constants, and the joint spectral radius of principal submatrices*](https://arxiv.org/abs/2504.17505) is v1, 24 April 2025. Its Theorem 4.1 supplies a principal-compression obstruction over the real field, rather than a full lower-Lipschitz resolution. It is not a premise of the reviewed proof.

The additional targeted searches in the source log did not identify a later full result. In particular, work about continuity of the lower joint spectral radius, finite-word attainment, or entropy representations was not mistaken for this specific lower estimate on the upper joint spectral radius.

## Publication wording and artifact handling

The publication should attribute the target to Epperlein–Wirth, the irreducible norm theorem to Barabanov/Wirth, and the nonresonance background to Chitour–Mason–Sigalotti. A suitable concise note is: “The nonresonance argument is related to Chitour–Mason–Sigalotti's discrete-time resonance theory and transition-sum estimates. Self-contained paired-tensor proofs are supplied here.” Avoid a claim that all auxiliary ideas, exterior lifting itself, or the first use of nonresonance are new. The bounded search does not certify priority of the critical exterior-power reduction.

[network-check-sanitized.json](network-check-sanitized.json), 127,231 bytes, SHA-256 `b7fc71ddc53d93bcdfa67804368fc763eeb8000f1e73febfafc110b682b6be1a`, is suitable for the publication record. It contains metadata and hashes, status fields and reviewer-written dispositions. It contains no retrieved full document/discussion body or contact email. The raw retrieval, 6,403,268 bytes with its exact fingerprint recorded in the sanitized JSON, is retained under `private/` and must not be copied into the public package. No third-party primary PDFs or page images have been added to the public artifacts.

The portable read-only [audit_public.py](audit_public.py) accepts `GH` or a GitHub CLI from `PATH`, requires an explicit output path, and optionally reuses only immutable blob contents from earlier snapshots. [sanitize_audit.py](sanitize_audit.py) produces the publication metadata from the private raw snapshot and rejects unexpected unreviewed discussion matches. No repository, branch, proof, commit or public discussion was modified by this task.

Signed by Codex agent `review_aa01`, 12 September 2026. Full target remains unresolved in the bounded public/source scope checked above; the separate reviewed candidate may proceed without duplicating a located full resolution.
