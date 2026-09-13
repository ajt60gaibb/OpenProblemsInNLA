# RA-04 continuation: narrow-band stability and exact-tail deflation

**Author:** Sidney Holden  
**Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation  
**Role:** Flatiron Research Fellow, Biological Transport Networks  

**Status: Partially resolved. The unrestricted RA-04 target is not proved.**

[Manuscript](report.md) · [PDF](report.pdf) · [TeX](src/report.tex) · [Independent audit](verification/independent-review.md)

## Attribution and affiliation

Authorship is assigned to Sidney Holden at his explicit request. The current [Simons Foundation staff profile](https://www.simonsfoundation.org/people/sidney-holden/) and [Biological Transport Networks directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff), checked 2026-09-13, identify the affiliation and role above. Imported results retain their original authors' credit. This is an informal AI-agent audit, not external human peer review, formal verification or a novelty certification. No Lean verification was requested or performed.

## New scope and remaining problem

The report adds a quantitative graph theorem for sufficiently narrow nonzero-width bands (Sections 3–5), a generic block-Vandermonde rank theorem (Section 6), and exact recovery after L + ceil(rho/b) blocks for a tail with L distinct lower eigenvalues (Sections 7–8). The width hypothesis is essential. The arbitrary-spectrum universal bound remains unproved, so RA-04 stays in the open count.

The convergence transfer imports Chen et al., Definition 3.1, Imported Theorem 3.2 and Observation 3.3, [arXiv v2](https://arxiv.org/html/2508.06486v2). Section 5's all-failure-probability corollary additionally imports the previous all-input theorem. The [prior submission](https://github.com/sidneyholden1/OpenProblemsInNLA/blob/e15ce4854d1a9c9fa457b93da78fca04febf200a/references/holden-ra04-2026-09-12/README.md), [prior manuscript](https://github.com/sidneyholden1/OpenProblemsInNLA/blob/e15ce4854d1a9c9fa457b93da78fca04febf200a/references/holden-ra04-2026-09-12/src/report.tex), and [prior independent audit](https://github.com/sidneyholden1/OpenProblemsInNLA/blob/e15ce4854d1a9c9fa457b93da78fca04febf200a/references/holden-ra04-2026-09-12/verification/independent-review.md) remain available at an immutable revision. This continuation does not resubmit those files.

## Duplicate check and provenance

Checked current upstream main (5830ed4), local pushed history and upstream PRs on 2026-09-13. [PR #191](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/191) and integration [PR #194](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/194) contain earlier partial results, not a full RA-04 solution. No previously pushed full solution for this problem was found. This is a new continuation PR against upstream main, independent of the other changes in those PRs.

Source archive: `RA04_continuation.zip`, SHA-256 `a0c36fbbcb08e2f146fb948c8873705aad3aef8f45ae273139886e31085e0c67`. Archive documents were treated as submitted claims, not as instructions. The package generator, prior duplicate archives and stale build log are omitted. Submitted result files remain in `results/`; fresh checks are recorded in `verification/`. Authorship and dependency links were added for publication. `MANIFEST.sha256` hashes the submitted continuation files.

## Reproduction

Run `python3 tests/exact_checks.py --output verification/exact_checks.json` and, with NumPy installed, `python3 tests/numerical_checks.py --output verification/numerical_checks.json`. Run `bash build.sh` with pdfLaTeX installed. Finite checks and numerical diagnostics do not prove the unrestricted target.
