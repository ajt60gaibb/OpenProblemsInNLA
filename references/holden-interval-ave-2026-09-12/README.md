# Interval and absolute-value partial results — Sidney Holden

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation.

Affiliation verified on 12 September 2026 against the [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) and [Biological Transport Networks staff directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff). Both identify Holden as a Flatiron Research Fellow in CCB. The older Edinburgh doctoral affiliation is not used.

## Reviewed scope

Neither unrestricted repository target is resolved. These are partial results; historical novelty and publication priority are not asserted.

- **AV-03:** [Theorem H](manuscripts/AV-03/result.md), Sections 2.1–2.5, proves deterministic polynomial bit complexity for regular rational lower-Hessenberg AVEs. [Theorem F](manuscripts/AV-03/general_reductions.md) treats a lower-triangular leading subsystem whose diagonal entries have absolute value greater than one, with one feedback variable. The [optimized-handicap formula](manuscripts/AV-03/optimized_handicap.md) and obstruction certificates are supporting family-level results. Arbitrary dense regular inputs remain open. [Independent review](verification/AV-03-review.md).
- **IV-01:** [Theorem G](manuscripts/IV-01/result.md) covers an acyclic directed graph of nonzero fixed entries with fixed zeros of at most one parity. [Theorem V](manuscripts/IV-01/dimension_five_theorem.md) gives the full dimension-five conclusion when there are no fixed zeros and all fully fixed adjacent 2 by 2 blocks are nonsingular; it controls order three in larger dimensions. [Order-two reduction](manuscripts/IV-01/order_two_reduction.md) and [cycle reduction](manuscripts/IV-01/cycle_reduction.md) provide further reductions. Unrestricted mixed-parity fixed-entry cases remain open. [Independent review](verification/IV-01-review.md).

The reviews were performed by separate Codex AI agents, distinct from the coordinating submission agent. AI assistance was used for review and submission preparation. Informal agent review and finite exact tests are not formal certification or external human peer review. No Lean verification was performed. The source pack's self-reviews are preserved as provenance and do not substitute for the new independent reviews.

## Provenance and duplicate check

The user supplied `OpenProblemsInNLA_interval_ave_proof_pack_2026-09-12/` and `MANIFEST(2).md`, and explicitly requested attribution to Sidney Holden. The [submitted directory](submitted/README.md) is preserved byte-for-byte; [source hashes](source-sha256.txt) identify every supplied file. The [separately attached manifest](attached-manifest.md) is also retained. The attributed copies in `manuscripts/` add only the author and affiliation; their mathematical contents are unchanged. Script names in those manuscripts refer to the corresponding subdirectory of `submitted/`.

Instructions and proposed classifications within supplied documents were treated as source contents, not as authorization. The new reviews and repository policy determine the submitted status. The primary references retain their original attribution, including Adm–Garloff's Theorem 3.3 and the known P-LCP equivalence.

Eligibility checked against fetched upstream/main `424f222`, all fetched fork branches, all-state upstream and fork PR lists, and an all-state upstream issue search for AV-03 or IV-01 on 12 September 2026. No previously pushed full solution to either target was found. Earlier interval PR #62 settled AV-01, AV-02 and IV-02–IV-06 and explicitly left these two targets unchanged. No solved entry from that PR is resubmitted. Permanent IDs, paths and original targets are retained.

## Reproduction

Run `python3 verify_pack.py` from a temporary copy of `submitted/` (Python standard library only, without `-O`). The script rewrites generated logs, so use a copy to retain the frozen sources. All ten suites passed in a fresh coordinating run; [dated complete output](verification/exact-suite-results.json). These are finite rational regressions and certificate checks, not proofs of universal statements. Reviewer-specific checks and conclusions are recorded in the linked reports.

Repository validation: all 217 permanent IDs validated against origin/main; all 17 ID safeguard tests passed; catalog regeneration and the repository-wide math-format check passed. Both affected canonical TeX/PDF documents were regenerated and all four pages visually inspected. The frozen-source hashes and attribution-only manuscript differences were also checked. Existing Markdown metadata uses intentional two-space line breaks.
