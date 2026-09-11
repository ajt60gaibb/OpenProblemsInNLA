# Recovered submissions by Matthew J. Colbrook

Recorded 11 September 2026 from `OpenProblemsInNLA_recovered_GitHub.zip`.

**Author: Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom; m.colbrook@damtp.cam.ac.uk. The [official departmental homepage](https://www.damtp.cam.ac.uk/user/mjc249/home.html) confirms this affiliation, checked 11 September 2026. Authorship is recorded at the submitter's request.

The notes and software were reconstructed with substantial AI assistance, as disclosed in the [original recovery record](submitted/research/RECOVERY_AND_CORRECTIONS.md). This is not a bit-for-bit recovery of an earlier archive. Independent agents checked the complete proofs against the current canonical targets. Their checks are not external human peer review or formal proof-assistant certification. No novelty, publication priority, or repository acceptance is asserted. The smallest right-inverse matrix is expressly attributed to Dokmanic and Gribonval's prior example.

## Reviewed results

| Canonical target | Result and primary proof | Independent review |
|---|---|---|
| IE-13 | **Solved:** sharp unequal-bandwidth growth recurrence; [Theorem 1, Sections 2-4](manuscripts/IE-13.pdf) | [Full proof review](verification/reviews/IE-13-review.md) |
| IE-14 | **Solved:** exact cyclic tridiagonal growth $F_{n+1}+1$; [Theorem 1, Sections 2-4](manuscripts/IE-14.pdf) | [Full proof review](verification/reviews/IE-14-review.md) |
| IE-17 | **Solved negatively:** both specified LSMR errors can increase; [Sections 1-4](manuscripts/IE-17.pdf) | [Full proof review and source caveat](verification/reviews/IE-17-review.md) |
| IE-18 | **Solved negatively:** four-step Anderson identity fails, with unbounded underestimation; [Sections 2-3](manuscripts/IE-18.pdf) | [Full proof review](verification/reviews/IE-18-review.md) |
| IE-19 | **Solved negatively:** inverse-norm counterexample and sharp unattained infimum; [Section 1 and Theorem 1](manuscripts/IE-19.pdf) | [Full proof review](verification/reviews/IE-19-review.md) |
| IE-21 | **Solved:** spherical row-deletion probability limit and error bounds; [Theorem 1, Sections 2-5](manuscripts/IE-21-22.pdf) | [Full analytic review](verification/reviews/IE-21-22-review.md) |
| IE-22 | **Solved:** matching universal row-deletion constant; [Theorem 2, Sections 6-7](manuscripts/IE-21-22.pdf) | [Full analytic review](verification/reviews/IE-21-22-review.md) |
| IE-23 | **Solved negatively:** nonunique direct norm-minimizing right inverses for every $2<p<\infty$; [Theorem 1 and Sections 3-4](manuscripts/IE-23.pdf) | [Full proof review](verification/reviews/IE-23-review.md) |

The [rook-pivoting note](submitted/research/rook_partial.md) and [independent review](verification/reviews/rook-review.md) establish the exact lower-bound example $g_{\mathrm{RP}}(5)\ge893/131$. This concerns order five, not the order-three/order-four constants asked for by IE-15. Its related-evidence notice leaves IE-15 Open. No matching rook upper bound is supplied.

The LSMR resolution concerns precisely the canonical **matrix-only spectral norm**, with fixed right-hand side. The cited SISC paper has a different default norm convention; no Frobenius-error conclusion is inferred. The Anderson result concerns a four-step identity, not asymptotic convergence. The inverse-norm claim uses entrywise ordering, not ordering of dominance margins. Row-deletion normalization, retention fraction, variational singular value, and eventual-uniform quantifiers are checked explicitly. IE-23 concerns the right inverse itself, not its product with the original matrix.

## Source preservation and verification

The original [package README](submitted/README.md), [status ledger](submitted/STATUS.md), [source register](submitted/SOURCES.md), combined manuscript, seven individual TeX/Markdown/PDF notes, code, outputs and submission drafts are retained under `submitted/`. The supplied [manifest](submitted/MANIFEST.json) matched all 57 hashed files before rerunning any checks. Including that manifest, all 58 original files are retained. [Archive identity](bundle-sha256.json) records the ZIP hash. The archived TeX is the package's canonical mathematical source.

The attributed exports preserve each complete mathematical source body. Front matter adds author affiliation, current verification status, confirmed canonical mapping, and the LSMR norm qualification. Statements in the original drafts about unavailable source access and provisional identifiers describe the reconstruction date; the subsequent dated reviews record their resolution and any remaining provenance limits. Review reports identify complete UTF-8/LF source hashes without trimming. Three separate agents covered the seven manuscripts and related rook note.

Fresh [exact verification results](verification/fresh-results.json) pass all six finite groups: 60 banded attaining matrices, 27 cyclic orders, LSMR iterates and spectral certificates, Anderson examples and independent recurrence, inverse identities and parameter checks, and right-inverse/Gram identities. The [rook rerun](verification/fresh-rook-results.json) also passes. The printed corrected LSMR constants pass a separate transcription audit. These finite checks supplement the all-orders and probabilistic proof reviews; IE-21 and IE-22 are verified analytically.

## Reproduction

From the repository root, with Python 3.10 or later (standard library only):

```sh
python references/colbrook-recovered-2026-09-11/submitted/scripts/check_integrity.py
python references/colbrook-recovered-2026-09-11/submitted/verification/run_all.py --output /tmp/recovered-results.json
python references/colbrook-recovered-2026-09-11/submitted/verification/check_document_constants.py
python tools/render_reviewed_tex.py references/colbrook-recovered-2026-09-11/manuscripts.json
python tools/validate_problem_ids.py --base-ref origin/main
python tools/update_catalog.py --base-ref origin/main
python tools/render_problems.py IE-13 IE-14 IE-15 IE-17 IE-18 IE-19 IE-21 IE-22 IE-23
python -m unittest discover -s tests -p test_problem_ids.py -v
```

Use a suitable temporary output path on Windows. To rerun `submitted/verification/rook_partial.py`, first copy the supplied package to a temporary folder: that script writes beside itself. Keep `submitted/` unchanged if checking its original manifest. PDF generation requires XeLaTeX and, for canonical entries, Pandoc. Executable overrides are supported by the repository renderers.

All 203 permanent IDs and original targets are preserved. Canonical Markdown, TeX and PDF changes accompany regenerated indexes. The local safeguard suite passes 15 tests; two tests require Windows symlink privileges unavailable here. The unchanged full suite runs in Linux pull-request CI.

