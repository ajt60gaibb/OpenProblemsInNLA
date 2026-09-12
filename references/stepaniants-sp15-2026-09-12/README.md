# SP-15 submission record

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

This record accompanies the [complete proof](../../eigenvalues-and-inverse-problems/SP-15/solution.md) of a negative resolution in complex dimension nine. The exact original target is preserved in the [canonical page](../../eigenvalues-and-inverse-problems/SP-15/README.md). The earlier generic finiteness theorem and the question retain their attribution to Maxime Fortier Bourque and Thomas Ransford.

The complete negative resolution passed a separate independent Codex-agent mathematical audit on 12 September 2026 UTC. Substantial AI assistance is disclosed. This is informal automated review; no external human peer review, Lean verification or novelty certification is claimed. The coordinating audit also passed. Both signed reports and the frozen proof remain unchanged.

## Frozen provenance

- [Reviewed proof candidate](verification/RESULT.md): 9,440 bytes, SHA256 `d992da0546924d7fbc9f1bb0e89e00b1442ec3c3045c739722c9767078ce40c1`.
- [Independent full-proof review](verification/independent-review-aa01/review.md): 11,984 bytes, SHA256 `8157139b028b2f68433038b6855d0d258bdaf1c2a3071bdefdd916d3d5fab499`. Its [review manifest](verification/independent-review-aa01/review-manifest.json), [independently written universal coefficient checker](verification/independent-review-aa01/coefficient_check.py), and [exact 136-term output](verification/independent-review-aa01/coefficient-check.json) are preserved unchanged. This symbolic diagnostic supports the audit; it does not formally certify the differential-topological argument.
- [Coordinating mathematical review](verification/SP-15-root-math-review.md), preserved unchanged.
- [Original canonical README](verification/canonical-statement.md), preserved unchanged from base `1f22006bdaa4659fcaa0bb775a887685cd3cc566`.
- [Sanitized public-network audit](verification/network-check.json), completed 2026-09-12 00:54:41 UTC: five repositories, 37 branch heads, 98 distinct selected text blobs and 32 PR review bodies. All eight extant SP-15 pages were Partially resolved; 29 older heads lacked the new page. The sole matching discussion was admission PR111, not a solution.
- [Eligibility and source-search scope](verification/eligibility-and-checks.md).
- [Exact integer diagnostic](verification/check_identity.py) and [five-case output](verification/identity-check.json). This is not a proof of the continuous fiber.

Only locally authored source, review and audit records are included. Third-party papers are linked at their primary locations and are not redistributed. The raw public-network response is private; its sanitized archive omits unrelated file contents and discussion bodies.

The mathematical core from “Exact target and conclusion” through Section 4 is preserved byte-for-byte from the frozen proof. Presentation metadata and source/reference prose are maintained separately. The mathematical core has 7,308 bytes and SHA256 `b93675c67c4756099e5d0c169a02a789da304380e99fb0976a5b042b94a20722`. [Document checks](verification/document-checks.md) and the [immutable source/artifact checkpoints](verification/source-checkpoints.json) record final verification. The [offline checker](verification/check_submission.py) verifies these identities, all ordered formulas and local links; its [output](verification/submission-check-output.json) is retained.

## Reproduction

From the repository root, run:

```bash
python3 references/stepaniants-sp15-2026-09-12/verification/check_submission.py
python3 references/stepaniants-sp15-2026-09-12/verification/check_identity.py
python3 references/stepaniants-sp15-2026-09-12/verification/independent-review-aa01/coefficient_check.py
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 -m unittest discover -s tests -p 'test_problem_statuses.py' -v
python3 tools/render_solutions.py SP-15
python3 tools/render_problems.py SP-15
```

The renderer requires Pandoc and XeLaTeX and supports their documented executable overrides. Rebuilding PDFs can change creation metadata, so the checkpoint hashes identify the reviewed final binaries; inspect every rebuilt page before publication. The portable public-network checker `verification/network_check.py` requires the GitHub CLI (`gh`, or the `GH` environment override); it writes a fresh sanitized `sp15-network-recheck.json` in the working directory, or the path given by `SP15_AUDIT_OUTPUT`. Rechecks have their own dates and do not replace the retained eligibility snapshot.

## Completed publication review and fresh eligibility

The separate [coordinating publication-conversion review](verification/SP-15-publication-conversion-review.md) passed on the exact frozen six canonical artifacts. All original mathematical content and target history are unchanged, and every final PDF page was individually inspected.

The [fresh shared public scan](verification/network-prepublication-2026-09-12.json), completed at 01:14:27 UTC on 12 September 2026, checked five repositories, all 38 branch heads, 103 selected text blobs and all 32 returned PR review bodies. Both SP-13 and SP-15 remained Partially resolved wherever present. Matching discussions were unchanged from the initial reviewed scan: admission PR 111 and unrelated MI-25 material. No prior full resolution was located. The [read-only reproduction script](verification/network_prepublication_check.py) takes an explicit output path; the public snapshot retains hashes and target excerpts rather than unrelated full text.

The [final coordinating verification record](verification/final-publication-checks.json) binds the unchanged canonical files, mathematical reviews, complete page inspection and prepublication scan. The original packaging checkpoints are retained separately before the publication-evidence additions.
