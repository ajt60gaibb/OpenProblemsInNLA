# Independent maintainer review - fourth batch, 11 September 2026

This audit reviewed current submissions independently of the contributors' own AI review reports. It covers complete proofs, original problem scope, cited primary results, reproducible computations and PDF/source consistency. Verification is by automated agents, not external human peer review or formal certification. Every permanent ID and mathematical target is retained.

| PR | Original reviewed head | Independent result |
| --- | --- | --- |
| [111](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/111) | `450ee69e20e54bb687240e01477cf95b0de61e0e` | RA-20 formula refuted; corrected admission reviewed again. Thirteen other additions pass bounded source/status review. |
| [114](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/114) | `1edaf118df2258c1b20c75966807219075d2ddf7` | PASS: TR-17 and TR-27 full targets. |
| [116](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/116) | `7d34abbd7d8fb12a37fea28ba68875c54780a5ed` | PASS: MF-18 full complex-coefficient equality. |
| [118](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/118) | `a9dd6917e5edaf96b9e578019a45625105cd4062` | PASS: RA-13 both absolute trace-tail comparisons. |
| [120](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/120) | `51e8ae1a801d846f3b649d387e5185df6c4cfdfe` | PASS: MF-22 eventual conditioning bound for the exact Toeplitz family. |

## Reports

- PR111: [eight source entries](PR111-eight-entry-review.md), [six source entries and counterexample](PR111-six-entry-review.md), and [final correction/document review](PR111-repair-review.md), and [final integration review](PR111-integration-review.md).
- [PR114 mathematical and PDF review](PR114-review.md).
- PR116: [mathematical review](PR116-review.md), [six-page PDF/source check](PR116-pdf-qa.md).
- PR118: [mathematical review](PR118-review.md), [eight-page PDF/source check](PR118-pdf-qa.md).
- PR120: [mathematical review](PR120-review.md), [eight-page PDF/source check](PR120-pdf-qa.md).

RA-20's original universal formula and complete parameter range remain unchanged. The [generic three-critical-point counterexample and reproducible checker](../research-expansion-2026-09-11/ra20-resolution/README.md) support Solved (refuted), without asserting the other formulas individually. IE-27's source section and SP-15's missing reference were also corrected. The four affected PDFs were rebuilt and all seven final pages inspected.

The reports preserve original review-time paths and commit identifiers as evidence. Later integration commits update shared indexes and distinguish historical partial/auxiliary contributions from subsequent full resolutions, while retaining their original authors and proof artifacts. Required permanent-ID checks and all 17 safeguard tests are rerun against the published base before each integration. The [integration results](integration-results.json) record the exact reviewed and merged heads, required CI results, permanent-ID checks and artifact-preservation counts for PRs #114, #116, #118 and #120.
