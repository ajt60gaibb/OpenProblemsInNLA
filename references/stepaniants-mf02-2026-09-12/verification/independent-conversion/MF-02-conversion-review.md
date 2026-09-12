# MF-02 independent publication-conversion addendum

Reviewer: Codex agent `/root/prepare_manuscripts`  
Date: 12 September 2026 (UTC)

**PASS.** The frozen publication sources faithfully preserve the independently reviewed theorem. The revised scope paragraph correctly records the uniform asymptotic-order verdict while retaining the unresolved exact-minimum, leading-constant, and same-budget questions. No mathematical correction or artifact change is requested.

The original review remains unchanged: [MF-02-independent-review.md](../independent-review/MF-02-independent-review.md), SHA-256 `ea00fa08007d4e2c042a110fa41e85504b8c02c925dd5d4d43cddfea67b20bb7`, bound to candidate `63d6a0dccebaf43b7da3dc6b2615755c3c3d24791a12527007f1276256e89ba9`. This is a separate addendum, not a replacement of its historical scope verdict.

I independently verified the following:

- After removing five `Needspace` layout directives, Sections 1–5 differ from the reviewed candidate only in the one declared scope paragraph. All other bytes in those sections are identical. The old and replacement paragraphs are recorded verbatim in [comparison.json](comparison.json).
- All **166 ordered mathematical expressions** in those sections are unchanged and match the standalone TeX after whitespace normalization. There are also 166 expressions in the whole manuscript. Mathematical prose matches between Markdown and TeX after removing heading, boldface, label, and layout syntax; no proof step is lost or reordered.
- The changed paragraph replaces the pending scope judgment with the completed uniform-order conclusion and explicitly leaves the same-budget comparison unanswered. This is consistent with my original review. The exact values at budgets zero and one remain one; the one-stage-per-multiplication upper guarantee is proved for positive budgets. All original infimum, gap, cost, and degree conventions remain intact.
- The complete canonical suffix beginning with `Context and notation`, including its target, references, and dated history, is byte-identical to the originally reviewed page. All **15 ordered formulas** on the final canonical page match `problem.tex`. The status notice explicitly identifies uniform constant-factor asymptotic order as the resolved scope.
- I read the [separate source review](../source-review/REVIEW.md), SHA-256 `30ba39e5f1afc5726956ce12caaa238518609f26dab3a18a96b35e28c25d6ea3`. Final Section 6 accurately carries its distinctions: the scaled iteration is credited to Chen–Chow, composition-class optimality to the cited Polar Express work, and prior constant-factor complexity and the uniform-order synthesis to Cheon–Kim–Kim. The note claims no first discovery of that order or iteration. The added attribution prose is identical in Markdown and TeX after presentation normalization. This conversion check does not independently certify publication priority.
- The Lorentzon initial is corrected to `G.`. George Stepaniants's full name, department, university, and substantial AI-assistance disclosure are present; the four source artifacts contain no email address. Both archived signed reviews, the original candidate, and the original mathematical checker/output remain byte-identical.

The source cores, including their scope paragraphs, are bound as follows:

| Core | Bytes | SHA-256 |
| --- | ---: | --- |
| Original reviewed Sections 1–5 | 8,725 | `0c2a3001bcb1d88c2d82ed132161e8ad479fe1c9ea0485445b39dfd7cf3c89a1` |
| Published Sections 1–5, five layout directives excluded | 8,699 | `00d3378f753b867cc747b22722a788452eb92856180f5086414791b5f23f0044` |

All six files under `matrix-functions-and-stability/MF-02/` match the supplied freeze manifest exactly:

| Artifact | SHA-256 |
| --- | --- |
| `solution.md` | `e104a785ddecbec117f6dffe58110222550dd7f1354bfda8c67c37daa68c1924` |
| `solution.tex` | `5afd5b5966215fe18fe0ee6e9dea8bdc23590f91da8c649941010565096e8453` |
| `solution.pdf` | `db9e652ed0beac7a7b2a4ba514fbfe42b38f589b3bd76f2d27ea4622a197c514` |
| `README.md` | `6d882b129f5ed6bf62184cc7cd2f9e29f909da0b8eb97c8ce463ab498b031487` |
| `problem.tex` | `00730232742075fcb0b3f1f181914346f8c3a7189cfbb3777a1606f9c0abc644` |
| `problem.pdf` | `19bd62564343ac714b6c88b910e6e4bf9d617683e2f2bb2867dae812fcc343f5` |

No artifacts, prior reviews, git state, or public state were modified. This addendum covers exact source conversion, attribution integration, and scope; it makes no independent claim about PDF visual inspection, which the coordinating agent handles separately. It is an informal independent AI-agent audit, not external human peer review or formal verification.

Signed: **Codex agent `/root/prepare_manuscripts`**, 12 September 2026 (UTC).
