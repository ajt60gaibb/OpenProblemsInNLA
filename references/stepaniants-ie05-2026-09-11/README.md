# IE-05 negative resolution by George Stepaniants

**Result:** the exact orthogonal partial-pivoting extremizer equality is false already at order eight. The **Theorem and Sections 1-4** of the [complete manuscript](../../linear-systems-and-elimination/IE-05/solution.md) give an explicit orthogonal matrix with growth $5272/63$, above the prescribed candidate's $\sqrt{17948132/2601}$. [Proof PDF](../../linear-systems-and-elimination/IE-05/solution.pdf) · [standalone TeX](../../linear-systems-and-elimination/IE-05/solution.tex) · [canonical target](../../linear-systems-and-elimination/IE-05/README.md).

## Author and verification

George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. The author authorized publication of his name and full affiliation; the department and university were checked against his [official Caltech profile](https://www.cms.caltech.edu/people/george-stepaniants) on 11 September 2026. No contact email is included.

The proof was developed with substantial ChatGPT/Codex assistance at the author's request. A separate agent read the full argument, independently parsed and checked the printed integer matrices, and returned [PASS for the complete canonical target](independent-review.md). The coordinating agent separately reconstructed the positive-diagonal QR factors by rational Gram-Schmidt and checked all active entry maxima. The proof supplies exact arithmetic throughout; no floating-point search result is used as the final certificate.

This is independent automated-agent verification, not external human peer review, formal proof-assistant certification, or a claim of historical priority. Peca-Medlin retains credit for the extremizer conjecture and cited element-growth analysis. This result does not determine the true orthogonal supremum or settle the separate asymptotic leading-constant question.

## Frozen source, review and publication conversion

The [frozen reviewed proof](full-proof.md) has 7,351 bytes and SHA-256 `18d49f30a3ef26f4c88a85c8ea1fc9e5c4e1702b4be6061d39aec892e96a4af7`. The [signed independent review](independent-review.md) has 8,434 bytes and SHA-256 `65629d58b94a2b5921955d5af6c3f30b69c59388dd48c2d8606ed58674eac7e4`.

The [prior draft](full-proof-before-attribution-review.md), SHA-256 `ebc80737d81f2e1e6d4a06b6064519f0260bf883ad48864cd9d058c046f82711`, is retained. The final frozen draft changes only one attribution sentence, distinguishing the older orthogonal matrix family from Peca-Medlin's conjecture and element-growth analysis. No mathematical text, matrix or table changed in that amendment.

The canonical solution preserves the entire frozen theorem, proof and scope text after removing exactly 23 raw LaTeX `\nopagebreak[4]` layout directives. Publication additions before the theorem are author metadata, spacing settings and the completed review disclosure. A separate [publication-conversion review](verification/IE-05-packaging-review.md) checks the Markdown, generated TeX, both tables and original canonical target. [Final fingerprints and document checks](verification/document-checks.json) record the exact sources, PDFs and validation results.

## Exact certificates

Three separately written standard-library checks are included:

- The [author's verifier](verification/verify_ie05.py) checks the displayed integer matrices, orthogonality, LU identities, all pivots, active maxima and the exact positive gap. Its [recorded output](verification/verification-output.json) is retained unchanged.
- The [independent printed-matrix verifier](independent-review/exact_matrix_review.py) parses the frozen proof itself and compares two independent constructions of every active Schur complement. Its [output](independent-review/exact_matrix_review.json) records all 408 active-entry checks and 56 multipliers across the two matrices, bound to the frozen source hash.
- The [coordinating agent's rational Gram-Schmidt verifier](verification/integer_counterexample.py) reconstructs both QR factors directly from the lower triangular inputs. Its [output](verification/integer_counterexample.json) records orthogonality, exact multipliers and all active maxima.

All three files are copied byte-for-byte from the checked research artifacts. The proof is self-contained and can be verified from its printed integer matrices; the executable checks make the finite arithmetic reproducible.

From the repository root:

```bash
python3 references/stepaniants-ie05-2026-09-11/verification/verify_ie05.py
python3 references/stepaniants-ie05-2026-09-11/independent-review/exact_matrix_review.py --source references/stepaniants-ie05-2026-09-11/full-proof.md --output /tmp/ie05-independent-check.json
python3 references/stepaniants-ie05-2026-09-11/verification/integer_counterexample.py
```

The third command reproduces the neighboring JSON file. The second accepts explicit input/output paths and checks the complete frozen-source hash.

## Existing-solution and source checks

The [public-network snapshot](verification/network-check.json), completed at **2026-09-11 23:25:40 UTC**, covers the original repository, its network source and all recursively reported public forks: **five repositories, 32 public branch heads, 114 distinct text documents and 26 PR review bodies**. It also checks matching issues, PR bodies, issue comments and inline comments. Every IE-05 canonical page retained **Open** status; no prior full resolution or matching discussion was located. The sanitized snapshot retains complete canonical content and document hashes. Private, deleted, unpublished and unidentifiably named material is outside this bounded check.

The [primary-source and literature check](verification/source-check.md) records the exact source locators, current arXiv version and bounded follow-up searches. The mathematical review checks the source conventions separately from the new exact certificate.

The [portable network checker](verification/network_check.py) is the original read-only joint IE-02/IE-05 audit tool. With an authenticated GitHub CLI, it can be rerun as follows; set `GH` to its executable path if necessary:

```bash
python3 references/stepaniants-ie05-2026-09-11/verification/network_check.py --output /tmp/ie02-ie05-public-network.json
```

Its output is the complete public fetch for local review; the submitted snapshot is the separately sanitized IE-05-only record linked above.

## Repository and PDF verification

The package is based on accepted upstream commit `87366c62d3b5c47d170f747b1cb40ab38d501013`. All 203 permanent ID/path mappings are retained. The complete canonical text from **Context and notation** onward is byte-identical to that base, and every other canonical page is unchanged. The original source and earlier status checks remain visible beneath the resolution notice.

The shared solution template has only formatting changes: its email field is optional, and standard Pandoc table packages plus an unnumbered-table counter are loaded when tables are present. No other manuscript was regenerated. Both generated TeX documents are standalone and compile with XeLaTeX. The four-page solution and two-page canonical PDF were each rendered twice and every final page was visually inspected, including both integer-matrix arrays and both stage tables.

```bash
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/validate_problem_ids.py --base-ref upstream/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 tools/render_solutions.py IE-05
python3 tools/render_problems.py IE-05
python3 references/stepaniants-ie05-2026-09-11/verification/check_submission.py
```

Both ID validations and all 17 safeguard tests passed. The catalog decreases the open count by one while retaining IE-05 at its original path. The final package checker verifies the reviewed-source hashes, unchanged original target, artifact fingerprints and local links.

## Later recovery comparison - 11 September 2026

A subsequently supplied reconstructed IE-05 manuscript changes entry $(7,2)$ instead of $(8,2)$. A separate [exact comparison](verification/recovery-comparison.md) proves that its orthogonal matrix equals the existing witness with rows 7 and 8 interchanged and column 7 negated. Every active-stage maximum and the growth ratio agree under the respective first-available-row paths. Both supplied checking programs reproduce their exact certificates. This is corroborating recovery provenance within the same submission, not an additional solved problem or a replacement proof. The frozen mathematical source, signed reviews, canonical pages, TeX and PDFs above remain unchanged. The [pre-recovery document manifest](verification/document-checks-before-recovery.json) is retained byte-for-byte; the current manifest adds only the recovery evidence and this appended record.

## Final layout and eligibility refresh - 11 September 2026

The [final presentation addendum](verification/layout-move-review.md) records moving the canonical page's raw page-break command into the IE-05 renderer. The actual Pandoc input and metadata remain byte-identical, so both standalone TeX files, both PDFs, the complete solution source and the completed six-page visual inspection are unchanged. The [pre-layout document manifest](verification/document-checks-before-layout-move.json) preserves the preceding canonical README fingerprint; no historical review was rewritten.

The unchanged [final public-network refresh](verification/network-before-push.json), completed at **23:51:45 UTC**, checked **five repositories, 33 public branch heads, 176 distinct text documents and 26 PR review bodies**. All IE-05 canonical pages remained Open, with no prior full resolution located; the only discussion match concerned unrelated IE-08. The original earlier audit remains preserved above. These checks cover publicly discoverable material within the recorded scope.
