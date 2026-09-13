# RE-03 continuation — Sidney Holden

**Author:** Sidney Holden  
**Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation  
**Date:** 13 September 2026  
**Decision:** independently audited partial results; RE-03 remains Partially resolved.

## Authorship and affiliation

Authorship is recorded at the submitter's explicit request. The [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) and [CCB staff directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff), checked on 2026-09-13, identify Sidney Holden as a Flatiron Research Fellow in Biological Transport Networks at CCB, Flatiron Institute. The institutional affiliation above follows those primary sources. The manuscript's formerly empty author field now carries this attribution. The archive's submission-authored review guide is not independent review.

## Submission and review

[Attributed manuscript](submission/manuscript/re03_extended_results.pdf) · [TeX source](submission/manuscript/re03_extended_results.tex) · [Independent review](independent-review.md) · [Canonical problem](../../randomized-and-low-rank-approximation/RE-03/README.md).

Theorem 1.1 proves the combined lower and upper bounds; Corollary 1.2 settles the full-recovery regime. A separate Codex AI agent reviewed the complete mathematical sources, including both input files, and passed the stated partial results. The universal-constant joint characterization remains unresolved because the uncapped upper expression is L times the lower expression. This is informal AI-agent review, not external human peer review or formal verification. No Lean was run. No historical priority or novelty claim is made.

## Provenance and reproduction

[Original uploaded ZIP](RE03_continuation.original.zip) preserves all submitted bytes, including the earlier nested archive. The extracted `submission/` retains the available source, code and historical reports. Editorial changes are limited to author attribution, the dated review-status notice and contents-page layout, the rebuilt continuation PDF, this submission record, packaging notices and refreshed checksums; no proof or implementation was changed. Attachment instructions were treated as source material, not user authorization.

The original 21-file checksum manifest passed before edits. The refreshed `submission/SHA256SUMS.txt` covers the edited package; run `python3 submission/verify_integrity.py` from this directory to check it. [Current checksums](SHA256SUMS.txt) also bind the original ZIP, manuscript sources, rebuilt PDF, review and fresh smoke report.

The available assembly smoke checks were rerun: all five passed, including query counting, proper HODLR output, exact-projection fallback and an experimental sketch example. [Fresh results](verification/assembly_smoke.json). Reproduce with a Python environment containing NumPy:

```bash
python3 submission/checks/assembly_smoke.py --output /tmp/re03-assembly-smoke.json
bash submission/build_pdf.sh
```

These are limited numerical checks, not proof verification. The manuscript's historical verification instructions mention absent continuation scripts (`code/verify.py`, `code/verify_two_stage.py`, `code/depth_family.py`, `code/joint_regression.py`). Their reported counts were not reproduced. See [assembly limitations](submission/ASSEMBLY_NOTES.md). The original reproduction text is preserved for provenance.

## Duplicate screening

On 2026-09-13, fetched upstream main and all fork branches, searched available branch histories and Sidney Holden's upstream pull-request history for RE-03/RE03/HODLR, and checked the canonical page. No already-pushed full solution for RE-03 was found. The archive contains only this problem; its nested earlier package is supporting history, not a second submission. The new branch starts at upstream main (5830ed4), preserving unrelated work and all permanent problem IDs.
