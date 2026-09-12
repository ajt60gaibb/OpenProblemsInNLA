# MF-22 independent source-conversion and scope addendum

Reviewer: Codex agent `/root/review_aa01`  
Date: 11 September 2026  
Verdict: **PASS for the exact publication-source conversion, canonical target preservation, and the path-only checker adaptation.**

This is an addendum to the independent full-proof review. It preserves that original review and does not claim external human peer review, formal verification, or independent visual PDF inspection. The packaging agent separately reports successful rendering and all-page visual QA.

## Exact publication files reviewed

The following paths are relative to `/tmp/nla-mf22-worktree`.

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `matrix-functions-and-stability/MF-22/solution.md` | 12647 | `a274a6401b27037bb5034cbffe87f02204fdcb663c40a9a7adfe033a19283edb` |
| `matrix-functions-and-stability/MF-22/solution.tex` | 14650 | `1456bf2df421bb039f33bf32a6f7670975e724a89dd3e885dc946ffe024dd5b7` |
| `matrix-functions-and-stability/MF-22/README.md` | 5909 | `4d771daf9f3d55299f5e465ceb2dbbc95bc54ddf3f62bc342612139ed1a3ebac` |

The original 11,201-byte reviewed proof has SHA-256 `4b2b030d0284014d2eabfc79ce56c4293bc83be7cb80f86deda31d3dddab5f4f`. The original 9,317-byte independent review has SHA-256 `256c61373b594db549bf5aef4c62a0f996b3d812d4b797cb47a7a8122e5fd1d8`. Their copies under `references/stepaniants-mf22-2026-09-11/verification/` were checked to be byte-identical.

## Mathematical content preserved

I compared the complete publication Markdown from `## 1. Statement and exact transfer recurrence` through the end, including Sections 1–4 and Scope/source, with the same range of the frozen reviewed proof. It is byte-identical after removing exactly seven standalone `\Needspace{...\baselineskip}` directives and 42 standalone `\nopagebreak[4]` directives. These commands only control page layout. No mathematical notation, coefficient, hypothesis, proof step, bound, or source attribution changed.

I then compared every ordered inline and display mathematical expression in that Markdown range with the generated TeX. All 144 expressions are identical after whitespace normalization. I read the converted TeX prose, including the special parameter, the root noncancellation argument, and the finite Green estimate; the argument is faithfully retained. The final header correctly reports the completed independent review and distinguishes it from external human peer review or proof-assistant verification.

The author and affiliation metadata name George Stepaniants and the Department of Computing and Mathematical Sciences, California Institute of Technology, with geographical affiliation. No personal email is introduced. The added plain page style and display-spacing instructions are outside the mathematical body and affect presentation only.

## Canonical target and resolution scope

The README's entire range from `## Statement` inclusive through immediately before `## Numerical significance` is byte-identical to the retained pre-resolution canonical statement. This includes all eight explicit coefficient blocks, the j−k Toeplitz orientation, the absence of corner corrections, the spectral condition-number convention, and every quantifier of the fixed-positive-parameter eventual polynomial bound. The problem ID and canonical path are unchanged.

The resolution paragraph correctly states the proved stronger result: eventual invertibility and a linear bound with exponent one for each fixed positive parameter, including sqrt(10). It does not claim uniformity in the parameter or invertibility at every small size. The source authors retain credit for the family, symbol/root classification, and question. The updated historical ratings and significance text do not replace or narrow the original target.

This addendum does not independently certify the submission's public-network status audit; that evidence is recorded separately by the parent/packaging agents.

## Portable exact-checker adaptation

The private independent checker is 4,277 bytes with SHA-256 `3b66b5f6e1a0f7709e16972cd626455ebb4ffbae9ea083fa506b11fccd3df63b`. The publication copy `references/stepaniants-mf22-2026-09-11/verification/independent_exact_check.py` is 4,278 bytes with SHA-256 `0f1128af72db7a0332f88c86784b5eb3f43cfa20875d4c27572fe91c95778d1b`.

I compared their full text. The sole difference is replacing the private absolute source path `Path('/tmp/nla-fresh-round1/mf22/RESULT.md')` with `Path(__file__).with_name('reviewed-proof.md')`. This binds the same preserved proof file while making the check reproducible from the repository. Every Gaussian-integer polynomial operation and all 31 assertions are unchanged. The original independent exact result and full mathematical PASS therefore apply to this path-only adaptation.

No repository staging, committing, pushing, or pull-request operation was performed as part of this review.
