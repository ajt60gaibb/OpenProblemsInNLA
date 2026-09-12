# SP-13 resolution by George Stepaniants

**Result:** trace-norm-$o(n)$ complex perturbations preserve every prescribed Hermitian spectral distribution, without spectral-norm bounds on either sequence or normality of the perturbed matrices. The precise locator is the **Theorem in Section 1, proved in Sections 2-5** of the [complete manuscript](../../eigenvalues-and-inverse-problems/SP-13/solution.md). [PDF](../../eigenvalues-and-inverse-problems/SP-13/solution.pdf) · [Standalone TeX](../../eigenvalues-and-inverse-problems/SP-13/solution.tex) · [Original canonical target](../../eigenvalues-and-inverse-problems/SP-13/README.md).

## Author, attribution and review

George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. The name and affiliation are published with his authorization. The department and university were checked against his [official Caltech profile](https://www.cms.caltech.edu/people/george-stepaniants) on 11 September 2026. No contact email is included.

The proof was developed with substantial ChatGPT/Codex assistance at the author's request. The separate [independent Codex-agent mathematical review](verification/SP-13-independent-review.md) returned **PASS for the complete canonical target**; a [coordinating-agent mathematical audit](verification/SP-13-root-math-review.md) also found no gap. Both checked the exact external theorem, its matrix-size-independent constant, the Schur decomposition, all singular-value thresholds, and the limit for arbitrary compactly supported continuous complex test functions.

This is informal automated-agent review, not external human peer review, Lean verification, another formal proof-assistant certification, or a determination of historical priority. No surviving parameter case of the displayed SP-13 target is omitted.

Barbarino and Serra-Capizzano retain credit for the conjecture and earlier perturbation results. Randrianantoanina and Dodds, Dodds, de Pagter and Sukochev retain credit for the published weak-type triangular-truncation theorem. The argument here applies that theorem to the imaginary Hermitian part of a Schur form and transfers the resulting singular-value estimate to the required spectral distribution.

## Exact reviewed source and publication conversion

The archived [frozen proof](verification/reviewed-proof.md) is 11,248 bytes, SHA-256 `dc5a7118b33fa84221d1b051997642180ca9c45e1605ebcad7b15a0d0642c7dc`. Its original pending-review wording remains as provenance. The signed independent report is preserved unchanged: 8,888 bytes, SHA-256 `f6e75de15aaccb63db10c8e9b16857a3a9aad40d5111eb60de4aa9b160dd08f7`. The coordinating report is preserved unchanged at SHA-256 `83083dcb832083331f51324e3a954deb1ee942b4a064db3d278eddb81f832cde`.

The canonical solution preserves the complete mathematical Sections 1-5 byte-for-byte: 7,494 bytes, SHA-256 `c89b2767c14af0419d403d8706bd446bad72ea4b76c28704b7290f67547d8dc0`. That core contains 121 mathematical expressions; the whole manuscript contains 123, all preserved in order in the generated TeX. The mathematical scope paragraph is also unchanged. Publication changes outside that body add the authorized author metadata, completed review notice, stable repository links and attribution. The references are retained. PDF-only page directives are inserted by the renderer, leaving the Markdown free of raw layout commands. The [source and document checks](verification/document-checks.json) record final hashes and validation.

The [original target](verification/original-target.md) is preserved exactly. In the canonical page, everything from `## Statement` through the original references and status history remains byte-identical; the resolution and historical-rating notices precede it. That earlier history describes the literature check before this submission. The problem's ID and path have not changed.

## Primary sources and existing-solution check

The essential external result was read directly in [Randrianantoanina, Theorem 4.8, printed page 23](https://www.impan.pl/shop/en/publication/transaction/download/product/87479), with its proof on page 24 and weak-norm definition on page 12. The theorem gives an absolute constant for arbitrary finite projection families and arbitrary trace-class inputs. Its matrix specialization uses the ordinary, unnormalized trace. The original [Barbarino-Serra-Capizzano conjecture, Section 6, printed page 29](https://giovannibarbarino.github.io/doc/articles/NHperturbation.pdf) was checked against the canonical statement. Precise file hashes and limits are in the [primary-source record](verification/primary-source-check.md). No complete third-party paper or rendered source-page image is included in this submission.

The bounded [public-network snapshot](verification/network-check.json), completed at **2026-09-12 00:53:36 UTC**, examined **five public repositories, every one of their 37 returned branch heads, 98 distinct selected text blobs, and 32 PR review bodies**. Existing SP-13 pages were all Partially resolved; other branches predated the entry. The only target-specific discussion was admission PR 111. The other three broad-keyword matches concerned the unrelated MI-25 trace-norm endpoint and were read and excluded. No prior complete SP-13 solution was found.

The public snapshot retains branch statuses, text-file inventories, complete-file hashes and SP-13 excerpts, and matching discussion-body hashes. Unrelated complete texts are omitted. The full private read-only fetch has SHA-256 `c6a56b5005e1570a8d188161060672189bdfde28845352e61220b25abe168dd7`. The [sanitizer](verification/sanitize_network.py) produces this bounded publication record from that fetch. Private, deleted, unpublished, or unidentifiably named work remains outside the check.

The related arXiv record `1808.05555` still listed v1. The 2025 Barbarino-Garoni Theorem 3.2 was checked and has extra restrictions that do not provide the present full conclusion. Targeted title, conjecture, trace-norm and spectral-distribution searches found no later resolution. These observations are bounded eligibility evidence, not an exhaustive priority claim.

## Reproduction and safeguards

The mathematical proof is analytic; it relies on the identified published weak-type theorem and the independently reviewed argument, not finite numerical experiments. The portable [submission checker](verification/check_submission.py) verifies exact mathematical-source preservation, all ordered math expressions in the generated TeX, original-target retention, no contact email, and every artifact fingerprint.

```bash
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/validate_problem_ids.py --base-ref 1f22006bdaa4659fcaa0bb775a887685cd3cc566
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 -m unittest discover -s tests -p 'test_problem_statuses.py' -v
python3 tools/render_solutions.py SP-13
python3 tools/render_problems.py SP-13
python3 references/stepaniants-sp13-2026-09-11/verification/check_submission.py
```

Pandoc and XeLaTeX are required for rendering; their executable paths may be supplied as `PANDOC` and `XELATEX`. Both generated TeX files compile independently with XeLaTeX. The build runs each document twice, and every final PDF page is visually inspected.

A fresh public check can be written to a new local path using the authenticated GitHub CLI:

```bash
python3 references/stepaniants-sp13-2026-09-11/verification/network_check.py --output /tmp/sp13-network-raw.json
python3 references/stepaniants-sp13-2026-09-11/verification/sanitize_network.py --input /tmp/sp13-network-raw.json --output /tmp/sp13-network-public.json
```

Set `GH` to the CLI executable if necessary. These commands are read-only on GitHub. Recheck matching full discussion bodies before interpreting a new snapshot; the sanitizer does not decide mathematical status. The original pre-publication checker is retained separately as provenance.

## Completed publication review and fresh eligibility

The separate [coordinating publication-conversion review](verification/SP-13-publication-conversion-review.md) passed on the exact frozen six canonical artifacts. All original mathematical content and target history are unchanged, and every final PDF page was individually inspected.

The [fresh shared public scan](verification/network-prepublication-2026-09-12.json), completed at 01:14:27 UTC on 12 September 2026, checked five repositories, all 38 branch heads, 103 selected text blobs and all 32 returned PR review bodies. Both SP-13 and SP-15 remained Partially resolved wherever present. Matching discussions were unchanged from the initial reviewed scan: admission PR 111 and unrelated MI-25 material. No prior full resolution was located. The [read-only reproduction script](verification/network_prepublication_check.py) takes an explicit output path; the public snapshot retains hashes and target excerpts rather than unrelated full text.
