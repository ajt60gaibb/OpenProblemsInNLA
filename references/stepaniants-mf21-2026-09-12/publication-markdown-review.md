# MF-21 independent publication Markdown conversion review

Reviewer: separate Codex agent `/root/prepare_manuscripts`.
Date: 12 September 2026.

**Verdict: PASS.** The public Markdown retains the complete mathematical content of the independently reviewed candidate. This addendum does not alter the frozen mathematical review.

Reviewed publication source: `matrix-functions-and-stability/MF-21/solution.md` in `/tmp/nla-mf21-worktree`, 19,864 bytes, SHA-256 `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.

Original source: 19,393 bytes, SHA-256 `98eb74a858ad3d2bf5fd0055a92d9c96b9a5e4f4f531972cd429462acb2b44f5`. Its archived `references/stepaniants-mf21-2026-09-12/reviewed-proof.md` is byte-identical. The full independent mathematical report remains frozen at SHA-256 `3c7611724de24ce996ea313041a3d2962134e356ffa776ceef8a3df5560f6c3a`.

I independently generated and read the entire unified diff and confirmed it exactly matches `editorial-conversion.json`. The mathematical body, Sections 1–5, is byte-identical after exactly the three recorded editorial repair groups:

- Remove decorative plain parentheses around the scalar values 0 and 4 in the double-root sentence.
- Replace malformed bare delimiters around the interval $(0,\pi]$, $g(\theta)$, and $A_n$ in Lemma 3 with proper inline mathematical delimiters.
- Remove decorative plain parentheses around 0 in the spectral-interval sentence.

These changes preserve the same interval endpoints, quantities, hypotheses, assertions, and proof steps. Nothing is excluded by introducing the proper mathematical delimiters.

The other differences are the author/date presentation, the introductory attribution and review disclosure, and the verification-scope paragraph. They accurately preserve George Stepaniants's Department of Computing and Mathematical Sciences, California Institute of Technology affiliation, disclose substantial AI assistance, identify the independent AI audit, and avoid any claim of external human peer review or formal verification. No contact email is introduced. The conjecture, prior cases, and external inverse-kernel theorem retain their attribution. The complete all-$m$ target and the bounds proved have not been weakened or enlarged.

The source links point to the intended manuscript-relative review and submission-record locations; their final packaging and the public-eligibility evidence remain the coordinator's responsibility. This addendum does not claim PDF visual inspection or approval of later source changes. [publication-markdown-comparison.json](publication-markdown-comparison.json) records the exact comparison and normalized mathematical-core fingerprint.

Signed electronically by the separate Codex reviewing agent `/root/prepare_manuscripts`, 12 September 2026.
