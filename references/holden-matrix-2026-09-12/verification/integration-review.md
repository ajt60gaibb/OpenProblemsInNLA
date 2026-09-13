# Independent publication integration review

Date: 2026-09-12. Reviewer: separate Codex AI agent `/root/review_reductions`. Result: **PASS** for mathematical integration, status scope and local links. This is an informal AI-agent review, not formal verification or external human peer review. No Lean was used.

I compared full unified diffs of all four publication proofs under `references/holden-matrix-2026-09-12/` against their original checkpoint sources. The only differences are author/affiliation/date and submission links, equivalent display-math delimiters and operator formatting, whitespace preventing HTML interpretation of less-than symbols, and the previously approved MI-20 clarification: “The supremum is taken jointly over all matrix orders.” No mathematical hypothesis, conclusion, argument, or coefficient was changed.

I inspected the four canonical README diffs and the new resolution-archive notice. Original targets are retained. MI-15 remains Partially resolved for orders 8–12; MI-16 is Partially resolved for the one-exceptional-eigenvalue spectral class. MI-20 and MI-27 remain Open because these submissions provide reductions and sharpness lemmas without the requested general sharp function or coefficient-one upper bound. All notices explicitly distinguish limited scope and informal AI review from a full resolution or human/formal certification.

I checked 40 relative Markdown link targets in the package README, four publication proofs and four canonical READMEs; every target exists. URL destinations and fragment anchors were outside this bounded filesystem-link check. Affiliation-source verification and duplicate-history checks were performed by the submitting agent, not repeated here. Earlier independent reviewers' mathematical reports remain the basis for the MI-15 and MI-16 proof assessments; this review verifies preservation of that audited material.

One nonmathematical reproduction correction was sent to the submitting agent and verified corrected: MI-27/check_family.py uses the Python standard-library fractions and decimal modules, not mpmath. The source and submission hash manifests themselves were not exhaustively checked in this bounded review.

## Publication proof SHA-256 hashes

- `MI-15/proof.md`: `6b67df5823ea724c9e4999e870e848c40eb1b311eaa8cb6f6c32b4950d4fb130`
- `MI-16/result.md`: `849e4490f693226fd2aef0eeab3fe0fa25bcb459bdba6c34c1af09e087dc2c74`
- `MI-20/result.md`: `ac30d5a0b6df0ddb7099032a0a06f542a9688f92c6aaa00bbad33c9cf6da6461`
- `MI-27/result.md`: `951f2860de3a714ec3dc833f13b5ffe76aab8dc5d7770bfc56426206c8996cc6`

These hashes identify publication files in `/tmp/nla-matrix-submit/references/holden-matrix-2026-09-12/` at review time. No repository files were edited by this reviewer.
