# PF-04 submission by Sidney Holden

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation.

## Affiliation verified 13 September 2026 (UTC)

The [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) lists Sidney Holden as a Flatiron Research Fellow in Biological Transport Networks at CCB, Flatiron Institute, with an October 2024 start. The [current institutional staff directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff) corroborates that appointment. The affiliation above uses these institutional sources; the former Edinburgh PhD affiliation is not presented as current.

## Submission and scope

[Manuscript PDF](submission/PF04_proposed_proof.pdf) · [Editable source](submission/PF04_proposed_proof.tex) · [Independent review](independent-review.md) · [Rerun exact results](rerun-results.json).

Theorem 1.1, proved in Sections 2–8, asserts the exact retained PF-04 target: every real completely positive matrix of order six admits a nonnegative factor with at most nine columns, including singular matrices and zero entries. Proposition 8.1 supplies a positive-definite sharpness witness. No computational-complexity or novelty certification is asserted. Published inputs retain their original authors and references in the manuscript and [source record](submission/SOURCES.md).

A separate Codex AI agent reviewed the analytic argument and external inputs independently of the submission editor. This informal audit and the supplementary finite checks are distinct from external human peer review and formal verification. AI assistance was used for submission preparation and review; the original package describes a research manuscript prepared in a conversation. No Lean verification was performed, as requested.

## Eligibility and provenance

The new branch is based directly on upstream `main` at `5830ed4fb06da0659414a3deb2a40ad327aca052`. At that revision PF-04 was Partially resolved, with no full solution files. The fetched fork branch history and upstream pull-request search for PF-04 found no prior full-solution submission; the related merged factorization PR #40 did not submit a PF-04 solution. Thus this package is not a duplicate of an already pushed full solution.

Supplied archive: `PF04_proposed_solution.zip`, SHA-256 `05646dc8d21e7bfa0d139b89a7d8977ef60f94cfb2088a5e1f602db971ae6e7c`.

[Original package hashes](original-SHA256SUMS.txt) retain the incoming integrity record. The submission copy changes author/affiliation, PDF author metadata and review-status text only; its mathematics is unchanged. The PDF is rebuilt from that source. Updated [package hashes](submission/SHA256SUMS.txt) describe the submitted copy. The original self-audit is retained as author-supplied material and is not the independent review.

## Reproduction

Use Python 3.10 or newer (the submitting editor used Python 3.12):

```sh
python3 submission/verification/verify.py --output rerun-results.json
cd submission
sh reproduce.sh
```

The verifier checks finite graph claims and exact examples; its PASS alone is not a proof of the universal theorem. The repository resolution decision also requires the complete independent analytic audit.
