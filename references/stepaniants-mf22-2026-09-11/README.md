# MF-22 resolution by George Stepaniants

**Result:** eventual invertibility and a linear condition-number bound for every fixed positive parameter in the exact cubic $C^1$ spline Schrödinger Toeplitz family. The precise locator is the **Theorem in Section 1, proved in Sections 2–4** of the [complete manuscript](../../matrix-functions-and-stability/MF-22/solution.md). [PDF](../../matrix-functions-and-stability/MF-22/solution.pdf) · [standalone TeX](../../matrix-functions-and-stability/MF-22/solution.tex) · [canonical problem](../../matrix-functions-and-stability/MF-22/README.md).

## Author, attribution and verification

George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. The name and affiliation are published with his authorization. The department and university were checked against his [official Caltech profile](https://www.cms.caltech.edu/people/george-stepaniants) on 11 September 2026. No contact email is included.

The proof was developed with substantial ChatGPT/Codex assistance at the author's request. One agent constructed the proof, a separate agent performed the complete adversarial mathematical review, and the coordinating agent independently reconstructed the root classification and boundary estimate. The [independent report](verification/MF-22-independent-review.md) returned **PASS for the complete canonical target**, including the exceptional parameter $\rho=\sqrt{10}$, the exact finite boundary conditions, and the uniform bound in matrix size.

Bogoya, Böttcher, Ferrari, Grudsky and Serra-Capizzano retain credit for the explicit family, its scalar determinant-root classification, and the original question. This submission supplies the recurrence, proof of noncancellation, and finite Green-matrix estimate establishing the additional condition-number conclusion.

This is independent automated-agent review, not external human peer review, formal proof-assistant verification, or certification of historical priority. The theorem holds for each fixed $\rho>0$, with constants allowed to depend on $\rho$. It asserts eventual invertibility, as the original target requires, and makes no claim about every small size or about extra corner corrections.

## Exact reviewed source and conversion

The archived [frozen proof](verification/reviewed-proof.md) has SHA-256 `4b2b030d0284014d2eabfc79ce56c4293bc83be7cb80f86deda31d3dddab5f4f`. Its original pre-review status wording is retained as provenance. The frozen independent report has 9,317 bytes and SHA-256 `256c61373b594db549bf5aef4c62a0f996b3d812d4b797cb47a7a8122e5fd1d8`.

The canonical manuscript preserves Sections 1–4 exactly after removing explicitly identified raw LaTeX page-layout directives. Publication changes outside the proof are the author metadata, a completed review notice and its repository link, and PDF spacing settings. No theorem, assumption, equation or inference was changed. A separate [publication-conversion review](verification/MF-22-packaging-review.md) confirms exact preservation and the portable checker adaptation. Final source hashes, proof-body comparison, build results and PDF checks are recorded in [document checks](verification/document-checks.json).

The [author's exact checker](verification/verify_exact_algebra.py) verifies the numerator, denominator, resultant, common-root elimination, parameter exclusion and discriminant using Gaussian-integer polynomial arithmetic. The [reviewer's separately written checker](verification/independent_exact_check.py) confirms 31 identities, including all canonical block coefficients, the Cayley identity, exceptional points and a direct characteristic determinant. Both use only Python's standard library and no floating-point arithmetic. Each checker was adapted only to read the neighboring archived proof, replacing its original private source path; its mathematics is unchanged. The original author-check report is retained [here](verification/original-exact-verification.json).

These exact computations check algebraic identities. The infinite-size conclusion rests on the full proof and the independent mathematical review, not on finite condition-number experiments.

## Existing-solution check

The [public-network snapshot](verification/network-check.json), completed at **2026-09-11 22:57:14 UTC**, checks the original repository, its network source, every recursively reported public fork, and all public branch heads: **five repositories and 30 heads**. Every canonical MF-22 page retained **Open** status. The check also fetched ID-named and relevant spline/Schrödinger/conditioning text documents and root indexes, and checked issues, PR bodies, issue comments and inline review comments in every repository.

No MF-22 solution manuscript or matching full-resolution discussion was found. The sole broad-keyword discussion match concerned the unrelated IS-05 sign-matrix problem and was excluded after reading its full body. Root indexes are retained as MF-22 excerpts with complete-file hashes; the unrelated discussion is represented by its URL, title, complete-body hash and assessment. The complete local fetch is also hashed. Private, deleted, unpublished or unidentifiably named work is outside this audit.

A [final pre-submission snapshot](verification/network-before-push.json), completed at **2026-09-11 23:09:31 UTC**, rechecked all **five repositories and 31 branch heads** after upstream advanced. Every MF-22 canonical page was still Open, and no full solution was found in the 83 distinct text documents or matching discussions read. The unrelated IS-05 discussion was again excluded after reading its full body.

A bounded literature check read [the current arXiv record](https://arxiv.org/abs/2608.24151), which still lists only v1, and the [complete primary text](https://arxiv.org/html/2608.24151v1), particularly equation (5.22), §5.3 equation (5.32), Proposition 5.14, and the paragraph after Figure 9. Searches for the identifier, cubic spline family, Schrödinger Toeplitz conditioning and a later solution located no full resolution. These are bounded checks, not an exhaustive priority assertion.

The portable read-only checker can be rerun using an authenticated GitHub CLI:

```bash
python3 references/stepaniants-mf22-2026-09-11/verification/network_check.py --output /tmp/mf22-network-check.json
```

Set `GH` to the CLI path if it is not on `PATH`.

## Reproduction and repository safeguards

```bash
python3 references/stepaniants-mf22-2026-09-11/verification/verify_exact_algebra.py
python3 references/stepaniants-mf22-2026-09-11/verification/independent_exact_check.py
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/validate_problem_ids.py --base-ref upstream/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 tools/render_solutions.py MF-22
python3 tools/render_problems.py MF-22
python3 references/stepaniants-mf22-2026-09-11/verification/check_submission.py
```

The package was first checked against upstream commit `aaa88c40fbf58e8cebc335021b3c5cd108c357e4`, then integrated with `87366c6` before submission. The later integration preserves all six canonical and proof artifacts byte-for-byte and retains the newly accepted upstream resolutions. All 203 permanent ID/path mappings and the original mathematical statement are preserved. The shared solution template makes its contact-email field optional, as required for this submission. The generated TeX files compile independently with XeLaTeX. The proof and canonical PDFs are rendered twice and every page is visually checked; the final validation record is linked above.
