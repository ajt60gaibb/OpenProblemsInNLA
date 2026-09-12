# PR #118 independent read-only PDF/source QA

Reviewed head: `a9dd6917e5edaf96b9e578019a45625105cd4062` (`origin/pr/118` in the shared audit repository).
Date: 2026-09-11. **PASS.** No document/source-conversion blocker found. This report checks packaging and source correspondence; the two separate mathematical reviews supply the proof verdict.

The six RA-13 documents were exported as exact Git blobs to `/private/tmp/nla-review-inequalities/pr118-source/`. No shared repository or authoritative document was modified or recompiled. Poppler created only temporary PNGs in `pr118-pdf-qa/`.

| Artifact | Pages | SHA-256 |
|---|---:|---|
| solution.pdf | 6 | `9a0d4da8c1a65fd1516af8d706be21bc5c05f146bfabe42e0516b86c55fcf0ad` |
| problem.pdf | 2 | `3c9eea52c935364e34fb415ffead2dc4739caddc89ae5ec9a329821695a0492b` |

I read the complete solution Markdown and canonical README. Every inline and displayed expression was extracted from Markdown and compared in sequence with the generated TeX, ignoring whitespace only. All **172 solution expressions** and **23 canonical expressions** match exactly. Full source hashes and counts are recorded in `pr118-pdf-qa/checks.json`. A fresh comparison confirms every exported file remains byte-identical to its exact Git blob.

I rendered and individually inspected all eight pages at readable resolution against the source. The six proof pages contain all eight sections and the complete references: normalized signed-Gamma statements, external shape/regularity assumptions, inflection identity, both transfer cases, grouped negative-coefficient removal, positive concentration, infinite-divisibility limit, and conversion to the exact RA-13 probability chain. Equation tags (1)-(9), tail directions, non-strict thresholds, signed kernels, the Greek nu function, Gaussian terms, Gamma shape/rate parameters, and normalization factors are legible and match the source. No mathematical passage is lost at a page break. The final proof page consists of references and the retained-auxiliary-results note; this is harmless pagination.

Both canonical pages are complete. Page 1 retains George Stepaniants's name and Caltech department/institution, the resolution and proof/review links, AI-assistance disclosure, and Matthew J. Colbrook's name and Cambridge affiliation with the auxiliary mode/inflection counterexamples and their limited scope. Page 2 retains the entire original trace estimator, matrix definitions, Gamma distribution convention, threshold, two-step probability chain, indefinite/zero-trace scope, source reference and historical audit notes. Hallman and Kwaśnicki retain their theorem/method attribution in the proof.

No clipping, overlapping text, missing glyphs, truncated formula or missing reference was observed. The crowded final canonical page remains readable and within the page. Automated text checks found zero out-of-bounds characters and zero replacement glyphs on all eight pages. All authorship and review-status text is readable. The PDFs correspond to the current Markdown/TeX; no correction is required for integration.

Evidence: `pr118-pdf-qa/checks.json`, complete extracted `solution.txt` and `problem.txt`, and all eight PNG pages. The original source files and exact PDF blobs are retained separately in `pr118-source/` for reproducibility.
