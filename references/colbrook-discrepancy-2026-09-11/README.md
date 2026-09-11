# Discrepancy submissions by Matthew J. Colbrook

Recorded 11 September 2026 from `nla_submission_package_5.zip`.

**Author: Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom; m.colbrook@damtp.cam.ac.uk. The [official departmental homepage](https://www.damtp.cam.ac.uk/user/mjc249/home.html) confirms this affiliation (checked 11 September 2026). Authorship is recorded at the submitter's explicit request. Independent agent checks and the reviewer-created witness below are identified separately; they are not external human peer review or formal proof-assistant certification. No novelty, publication priority, or maintainer acceptance is asserted.

## Results and boundaries

- **MD-06: Solved, negative resolution.** [Theorem 1 and complete attributed manuscript](manuscripts/MD-06.pdf) prove that the probability of every local minimum being synchronized tends to zero in the exact uniform labelled simple cubic model. The mean-zero Hessian and positive-cosine guarantees are uniform. [Deterministic review](verification/reviews/MD-06-deterministic-review.md) and [probabilistic review](verification/reviews/MD-06-probabilistic-review.md) independently check the complete source and exact primary-theorem hypotheses.
The [many-minima note](submitted/research_notes/md06_many_minima.md) also passed probabilistic review: the number of nonsynchronized minima modulo rotation diverges in probability. Its exponential count is in the number of separated gadgets, not in graph order; no growth rate in graph order is proved.

## Original package and missing files

Eight MD-06 source, certificate, note and issue-draft files are retained under `submitted/`. The [archive and retained-file SHA-256 values](bundle-sha256.json) identify their original bytes. The broader research report and other-target supporting material are withheld from this MD-06-only submission at the submitter's request. Mathematical source bodies are preserved in the attributed export; front matter adds attribution, subsequent review status and a packaging correction. Original statements about pending review describe the input date.

The MD-06 prose refers to absent supplementary programs, including `analytic_gadget.py`, `verify_flow_certificate.py`, `test_certificates.py`, logs, and `alternative_correction_argument.md`. Claims that those files were supplied or that their tests ran are not adopted. They are not premises of the complete asymptotic proof.

The absent analytic-gadget program is not needed for the MD-06 asymptotic proof. A separately written [independent symbolic checker](verification/independent_md06_symbolic_review.py) checks the described construction at radii 4, 5 and 6; its [results](verification/independent_md06_symbolic_review_results.json) are reviewer evidence, not recovered submitted files.

No source-generation provenance document was present in this archive, so none is inferred.

## Reproduction

From the repository root, with Python 3.10 or later (standard library only):

```sh
python references/colbrook-discrepancy-2026-09-11/submitted/MD-06/code/verify_certificate.py references/colbrook-discrepancy-2026-09-11/submitted/MD-06/data/cubic20_certificate.json
python references/colbrook-discrepancy-2026-09-11/submitted/MD-06/code/verify_certificate.py references/colbrook-discrepancy-2026-09-11/submitted/MD-06/data/cubic500_certificate.json
python references/colbrook-discrepancy-2026-09-11/verification/independent_md06_symbolic_review.py
python tools/render_reviewed_tex.py references/colbrook-discrepancy-2026-09-11/manuscripts.json
python tools/validate_problem_ids.py --base-ref origin/main
python tools/update_catalog.py --base-ref origin/main
python tools/render_problems.py MD-06
python -m unittest discover -s tests -p test_problem_ids.py -v
```

Rendering requires XeLaTeX, and canonical exports also require Pandoc. Both supplied rational certificates passed fresh execution: [20 vertices](verification/cubic20.json) and [500 vertices](verification/cubic500.json). Their exact rational acceptance proves nearby exact minima; the input rational phase vectors themselves are not asserted stationary. Finite checks supplement the full asymptotic proof.

All permanent IDs, original targets and dated audits are retained. The canonical Markdown, TeX, PDF and generated indexes accompany this submission. Local Windows tests encounter the existing symlink-privilege restriction in two cases; the unchanged full suite is checked in Linux pull-request CI.
