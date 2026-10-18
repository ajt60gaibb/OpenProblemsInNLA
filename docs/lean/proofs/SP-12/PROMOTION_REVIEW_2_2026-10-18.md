# SP-12 status promotion, originals and rendered statement — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
**APPROVE the reviewed status/documentation promotion and preserved original statement.** I did not author these changes. This review made no canonical or package edit.

The canonical page changes only its status/date and adds one clearly bounded formal-proof notice. Removing exactly that notice and restoring the two metadata values reproduces the entire original README byte for byte, including Hall/Stepaniants credits, original statement, ratings and all history. The notice accurately cites immutable full-proof commit `529e7b0560cef6461c98e950046860a160e6f86c`, successful actual run `39142969327`, the independently verified Linux receipt and exact original archive. It distinguishes AI-agent checks from external human peer review.

The package README and formalization metadata accurately mark the complete original Target as verified after actual Comparator/kernel acceptance. Their 96-input claim explicitly refers to the retained immutable first run; they separately state that refreshed descriptive metadata requires new committed CI. All 55 checked Lean sources and all live/frozen/Challenge/Identity/Comparator boundaries remain unchanged. Standard axiom permissions are unchanged. The selected proof alone has zero sorries; Challenge remains the separately identified deliberate comparison placeholder. The schema and exact Comparator coverage validator passes one full selected export. No source theorem, proof premise, permanent ID or canonical path was edited.

I read the preservation checker and reran it independently against fixed base `e3725bf89a9682c28bb2c0cec1cee1be658d5d11`, saving a separate [16-check result](promotion/independent-preservation.json). It passes: all 217 registry IDs/paths and every canonical page remain retained; only SP-12's authorized page changes; all original text is exactly recoverable; of 611 immediate original artifacts, only its regenerated TeX/PDF differ, with 609 unchanged; all three original archived files match exact base hashes; frozen statements and all 55 actual CI Lean inputs remain unchanged. The checker uses the real retained CI hash manifest and an exact allowlist of the two regenerated paths. It does not weaken identity guards or overwrite historical all-byte-preservation evidence.

I additionally verified the archive contains exactly README, TeX and PDF, and each is byte-identical to published base `36767fa430309f13d04dc6ebe080d470f5c2444a` and its manifest digest. Across the complete original/generated TeX, all **20 mathematical expressions** remain identical after whitespace normalization. This independently checks more than the target-section-only preservation guard. The rendering change only adds SP-12 to the existing verification-date footer list; no mathematical rendering transformation was introduced.

Using the PDF skill read-only workflow, I independently rendered the final PDF into three new PNGs and inspected every page. All content is legible and unclipped, with no overflow, overlapping elements, missing mathematical glyphs or broken headers/footers. The complete original graph/PSD/SAP/chromatic problem statement appears on page two with all three SAP equations, exact matrix pattern, maximum-nullity definition and chromatic inequality intact. Credits, references and historical records remain present. The final repository renderer log is clean; the earlier new-notice overflow attempt remains retained rather than overwritten.

The final PDF SHA-256 is `adb83285086eaf4459f6df1f704ca608e546c6cf6ef5b0e8e24c4c7cfa997f29`. [Independent source/visual evidence](promotion/independent-pdf-and-originals-review.json) binds that PDF, current TeX, original archive and all three separately rendered images. [Reviewed input hashes](promotion/independent-reviewed-inputs.json) bind the actual canonical/package metadata, PDF/TeX, renderer and preservation checker reviewed here.

Reproduce the strict preservation check from the repository root:

```bash
python3 docs/lean/proofs/SP-12/check-promotion-preservation.py \
  --ci-result docs/lean/proofs/SP-12/verification/full-linux-ci/artifact/verify-20261018T162848Z-4209/result.json \
  --output docs/lean/proofs/SP-12/promotion/independent-preservation.json
```

The mathematical proof and actual first Linux artifact were reviewed separately in the full closure, canonical and Linux artifact reports. This promotion review does not relabel changed package metadata as the earlier 96 immutable CI inputs; a fresh committed-project Linux run remains required for the refreshed package. No external human review or source-author endorsement is claimed.
