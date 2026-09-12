# RA-13: absolute-error Gaussian trace-tail comparison

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.  
**Resolution date:** 11 September 2026.  
**Outcome:** affirmative resolution of the complete retained RA-13 target, with independent Codex-agent review.

[Canonical target and resolution](../../randomized-and-low-rank-approximation/RA-13/README.md) · [Complete proof](../../randomized-and-low-rank-approximation/RA-13/solution.md) · [Proof PDF](../../randomized-and-low-rank-approximation/RA-13/solution.pdf) · [Standalone XeLaTeX](../../randomized-and-low-rank-approximation/RA-13/solution.tex).

## Exact scope and attribution

Sections 1-8 prove both probability comparisons for every nonzero real symmetric matrix, including indefinite and zero-trace matrices, every positive integer sample count, and every deviation at or beyond the exact displayed threshold. Equation (1) proves the stronger one-sided comparison for all common Gamma shapes; equation (2) controls the absolute error; Section 8 matches the canonical matrix parameters. No optimality claim is made for thresholds below the one requested.

The new proof derives an inflection identity for signed Gamma convolutions, transfers all equally most-negative coefficients together, and then concentrates positive coefficients through a minimum-scale transfer. Infinite divisibility supplies the Gamma endpoint. Kwaśnicki's published weak bell-shape theorem and Hallman's centered coefficient-derivative method retain explicit attribution. Matthew J. Colbrook's earlier mode/inflection counterexamples retain their authorship, links, historical scope and validity on the canonical page; they did not resolve this final probability chain.

The manuscript was developed with substantial ChatGPT/Codex assistance and is submitted under George Stepaniants's authorship at his request. An independent Codex agent that did not develop the proof rederived its identities and checked its precise target, published prerequisite and endpoint cases. This verification is independent agent review, not external human peer review or formal proof certification. The user's contact address is not included.

## Frozen proof and independent review

The [original reviewed draft](verification/reviewed-proof.md) is preserved byte-for-byte, including its historical candidate-status preface. That preface records the stage before the independent review below; it does not describe the current resolution status.

- Frozen source SHA-256: `6ee4efe2bf23c91276db20bb2bf67ca05c5fa659f30f50b6f8670fd8507d5dff`.
- [Independent full-target PASS review](verification/RA-13-independent-review.md), SHA-256: `86f795530bec85ac00e93c6a1fd88b0a2985d49ac38606c2db3c5662b7784b99`.
- Original mathematical-body SHA-256: `602c7f1b61ee93e8a8c9a328488d61c681ff1167819acdb8a59e194a816a276d`.
- Published mathematical-body SHA-256: `7a8fbbfbd4cddeed20e7ff4ff8a11854fcaefac34309aa153fc807513581e87f`.

The mathematical-body conversion replaces two literal `,quad` strings in the definition of mean, variance and total shape by `,\quad`, and changes the sole definition `u(t)=1-g(z-t)/g(z)` to `\nu(t)=1-g(z-t)/g(z)`, matching every subsequent kernel integral. The independent reviewer explicitly permitted these typesetting/notation corrections, recorded in a separate [conversion addendum](verification/RA-13-packaging-review.md). Every other body byte from Section 1 through Section 8 is preserved. Title, author/affiliation metadata, verification preface and closing source/audit material were prepared for publication outside that body. [Machine-readable source identity](verification/source-identity.json) also records the original target hash. PDF layout changes, if any, are separately documented in the final checks.

## Public status and source checks

The [read-only public network audit](verification/network-check.json) completed at **22:44:19 UTC on 11 September 2026**. It recursively enumerated all **five public repositories and 29 branch heads**, inspected their retained RA-13 status and 82 distinct relevant text documents, and searched issue/PR bodies, issue comments and inline PR review comments in every repository. Every branch still recorded RA-13 as Open. The relevant earlier RA-13 discussions were the auxiliary-result [issue 31](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/31) and [PR 32](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/32). The separate [RA-12 issue 92](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/92) and [PR 93](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/93) concern the relative-error target, not RA-13. Additional broad keyword matches concerned other problems and did not supply a full RA-13 resolution.

The supplementary [discussion audit](verification/network-discussions.json), completed at **22:47:21 UTC**, read all **16 PR review bodies** across those repositories. Its only relevant match was the existing [auxiliary-result PR review](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/32#pullrequestreview-5180633654), which explicitly left RA-13 Open. GitHub Discussions was disabled in all five repositories; the script would paginate every thread, comment and reply where enabled. [Main audit script](verification/network_check.py) · [Supplementary script](verification/network_followup.py). Public contact-address strings in retained audit text are redacted; no mathematical or status content is changed. Private, deleted, unpublished and unidentifiably named work is outside these checks. They are dated status checks, not a claim of universal historical priority.

The coordinating agent's [final pre-publication check](verification/network-before-push.json) at **22:57 UTC** confirmed all **30 public branch heads** in the same five repositories still recorded RA-13 as Open. The additional head was the separate MF-18 submission; no full RA-13 solution appeared in the checked discussions.

The pinned primary sources were read directly: [Hallman, arXiv:2411.15454v1, Theorem 7, Conjecture 4 and Appendix A.2](https://arxiv.org/html/2411.15454v1), and [Kwaśnicki, arXiv:1710.11023v3, Corollary 1.2 and Section 2](https://arxiv.org/html/1710.11023v3). Hallman's current record still lists only v1. The precise threshold is the numbered conjecture's formula, whose inconsistency with its following prose was already disclosed on the retained problem page.

## Checks and submission procedure

The [limited exact-algebra and numerical check script](verification/check_reductions.py) and its [output](verification/check_reductions.txt) are retained. They contain 27 rational grouped-transform derivative checks, four rational signed single-scale inflection identities, and 15 chosen actual tail comparisons at common shape one. The floating-point tail checks are diagnostics only; the complete proof and independent review establish the resolution.

[Final document and repository checks](verification/document-checks.md) record source/target preservation, permanent-ID validation, catalog regeneration, safeguard tests, PDF rendering, all-page visual inspection and artifact hashes. The branch is prepared from published upstream/main `aaa88c4`; it changes no problem number, canonical path or original mathematical target. The correction-or-resolution issue and a new pull request against main will link this complete evidence and explicitly request review and inclusion in main. Publication is handled separately from this local preparation.
