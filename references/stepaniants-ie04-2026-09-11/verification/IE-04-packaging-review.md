# IE-04 independent publication-conversion review

**Verdict: PASS.** The final publication faithfully preserves the complete recovered mathematical proof, original canonical target, and stated scope. No source or PDF correction is required.

Reviewer: `/root/prepare_manuscripts`, a separate Codex agent from the IE-04 packager and the earlier complete-proof reviewer. Signed on **12 September 2026 UTC** (11 September in the author's local time zone). This addendum supplements the [frozen independent mathematical review](IE-04-independent-review.md); it is not external human peer review, formal proof-assistant certification, or a novelty or priority determination.

## Exact version binding

The [reviewed recovered source](reviewed-proof.md) has 8,401 bytes and SHA-256 `428c586bf6a0b66ce94d478eed5be6e951032cc09fc646df7204ae2823b14a75`. The prior full mathematical review has 10,522 bytes and SHA-256 `757daf1061629d1b1efbebc1a8546fca0a2dfb339d2a8e8d68237a08ccd48564`. Both remain byte-identical to their frozen copies.

I independently read the complete original Markdown, final Markdown, generated TeX, canonical page, and earlier mathematical review. I checked the following final artifacts against the packager's frozen inventory and independently recomputed their byte counts and SHA-256 values.

| Final canonical artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| [README.md](../../../linear-systems-and-elimination/IE-04/README.md) | 4,898 | `4dc92888b019c4b4816e891fab15377128415f2e2caa9b44e4cdc7973e34050a` |
| [solution.md](../../../linear-systems-and-elimination/IE-04/solution.md) | 9,944 | `5418bb8fa765313d2e4dcbd85a78558e244fc6207b165b511a2b03532f34199e` |
| [solution.tex](../../../linear-systems-and-elimination/IE-04/solution.tex) | 12,098 | `e776df45e852467d1e9f27674dbd85fc9cd3c06fb5ec7a3760bb146bf9a8d4c6` |
| [solution.pdf](../../../linear-systems-and-elimination/IE-04/solution.pdf) | 72,828 | `f0857c8559155d840343639b4930e3fb842d9c08baec6e5898fed42088a29ac3` |
| [problem.tex](../../../linear-systems-and-elimination/IE-04/problem.tex) | 8,349 | `06f4e51a63a43841cd41c80d99e75bfe71b7e47e540aada370a62fba2166f59a` |
| [problem.pdf](../../../linear-systems-and-elimination/IE-04/problem.pdf) | 40,120 | `2774d9c462d6fd6df8ee748ff42c30cf787716ecde94b093ef601e2e945febff` |

## Proof and TeX preservation

After normalizing original top-level headings to the publication's second-level headings and removing exactly 19 `\nopagebreak[4]` lines and four `\Needspace` directives (10, 10, 9 and 12 baselines), the mathematical core is byte-identical. Its exact span begins immediately after **Statement and conclusion** and ends immediately before **Verification, scope, and provenance**. It has **6,168 bytes**, SHA-256 `728a52e23229112c06da15bfbf41459c2cda4167ff3cdb5acfd92712098341ba`.

All **92 ordered core math expressions** match between the recovered source, final Markdown and TeX after whitespace normalization. Extending the comparison through the verification and scope section gives **95 ordered expressions**, all identical. Equation tags 1 through 18 occur in the same order; the unnumbered order-four matrix is also preserved exactly. I also read the TeX prose and checked the displayed inequalities and their explanatory text, including strict pivot separation, the perturbation radius, Gaussian box probability, strict tail event, and the contradiction for arbitrary positive real constants.

A comparison of the entire body from Statement and conclusion through the references finds only two additional nonmathematical changes: the code fence drops its `text` language label, and the historical pending-review sentence is replaced by the authorized substantial ChatGPT/Codex assistance disclosure and completed independent-review status. The script command, certificate description, finite-check limitations, scope paragraph and complete references are otherwise unchanged. Publication metadata and the introductory review links precede the preserved body.

The [comparison evidence](IE-04-packaging-comparison.json), SHA-256 `6494d9b335400f5772280b0f96898bbe943354253a80802ff02ba1d37b9669a4`, records the exact artifact hashes, normalized-core hash, all 92 ordered core formula fingerprints and PDF text checks. The original supplied files and the canonical checker, certificate and recorded output were checked for byte-for-byte preservation.

## Original target, attribution and scope

The [original canonical page](original-target.md) is byte-identical to accepted upstream commit `87366c62d3b5c47d170f747b1cb40ab38d501013`, with SHA-256 `e774f301b6b50da21fcb1904aec6f6279fd40ec293082593e35f959fd5bf5550`. The entire current canonical block from **Context and notation** through the final historical audit paragraph is byte-identical to that base; its SHA-256 is `a4c427fe31d5b5977f80e6c2c390a64ee9425daea520a95ce5ed05bbcade5c0a`. The added resolution notice preserves IE-04's permanent identifier and original target.

The notice and proof consistently use the allowed nonsingular deterministic center $I_n$, noise level one, the original active-Schur-complement normalization and the unrestricted range $x\geq1$. Failure in sufficiently large dimensions refutes the universal target, so the theorem's $n\geq2$ range does not omit a required positive case. The text expressly leaves replacement tails, expectations and sharp high-probability exponents outside its conclusion. Spielman and Teng retain the historical attribution in the unchanged source references.

The final Markdown, TeX, canonical page and visible PDF bylines identify **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**. The publication distinguishes substantial AI assistance from the separate automated-agent audit and disclaims external human peer review and formal certification. No contact email or `mailto:` link was found in the reviewed manuscript/record sources or either PDF's extracted text.

## Read-only visual inspection

I inspected every existing final page image individually: solution pages **1–4** and canonical problem pages **1–2**, against the frozen PDF versions listed above. The title and affiliation, 18 numbered displays, order-four matrix, proof transitions, references, margins, page numbers and retained problem/history text are readable and complete. No clipping, overlap, missing glyph, orphaned display cue or broken equation label was observed. PDF metadata and text extraction independently confirm the four- and two-page counts, attribution, absence of contact email and absence of replacement-character glyphs.

No manuscript, original source, checker, TeX file or PDF was edited or regenerated during this review. Only this signed addendum and its comparison-evidence JSON were created. Repository validation, eligibility and publication remain separate steps owned by the coordinating agent.

Signed: `/root/prepare_manuscripts`, independent publication-conversion reviewer.
