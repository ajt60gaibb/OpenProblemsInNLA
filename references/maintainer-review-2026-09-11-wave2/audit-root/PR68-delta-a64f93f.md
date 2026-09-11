# PR 68 delta audit: a64f93f

Date: 2026-09-11. Independently reviewed transition from `c9ad7691e1b3f2cf6595fd204fef54a6b1349910` to `a64f93f93124e0f7486d15a06cac8d0eec69a9eb`.

**Verdict: PASS.** The delta removes the author's contact address from the two manuscript bylines and the submission README, regenerates the corresponding PDFs, and updates three verification records. No mathematical proposition, proof, assumption, attribution, problem target, status, permanent ID, or workflow changes. The prior mathematical verdict in `PR-68.md` therefore carries forward to this exact head with its existing limitations. This is a delta-preservation audit, not a new proof-assistant certificate or a claim of external human peer review.

## Exact source and supporting-record comparison

There are exactly eight changed files. The two TeX edits are confined to their author blocks: `arithmetic-and-complexity/AA-01/solution.tex:57–61` and `references/stepaniants-2026-09-11/manuscripts/md03_md04_proofs.tex:33–37`. Every byte beginning at each `\begin{document}` through the end of its source is identical to the previously reviewed version. All canonical problem READMEs, solution Markdown, original-source archives and other submission files are unchanged.

The unchanged AA-01 complete document-body SHA-256 is `212035a280475cb6338964aa5a4569ac21c9d9af3e8f8f9a9520ada263284abd`. The discrepancy note's unchanged body SHA-256 is `4610299e6267c35035b3a84154cee7492952d619c3e31eb432a35b0d4a30aa8e`. These match independently recomputed values, rather than merely the submitted declarations. The updated document-check record's previous/current artifact hashes, source hashes and all recorded PDF hashes also match the actual files. The two appended review notes accurately describe these source-preservation facts.

## PDF and redaction verification

Both changed PDFs preserve their page counts: AA-01 has 11 pages and the discrepancy note has two. Complete extracted text, normalized only by removing the old contact address and whitespace, is identical in both old/new comparisons. Thus no mathematical text was dropped or changed by recompilation.

I independently rendered and visually inspected all 13 changed pages. The title/byline areas, displayed mathematics, headings and references remain legible with no clipping or overlaps observed. Every extracted character is within a five-point inset of its page. The rendered pages and three contact sheets are in `PR68-delta-pdf-qa/`.

A separate scan of all 28 originally contributed text/PDF files finds zero occurrences of the removed contact address in raw files, PDF extracted text, or decoded PDF objects, including compressed object streams. The comparison derives the old contact only in memory; this report and the reproducible check do not republish its literal value. This verifies the current submitted tree, not erasure from Git history.

## Scope and evidence

The old snapshot was preserved. The new commit was fetched into a separate temporary clone and extracted to `pr-68-current`; neither the shared integration checkout nor any remote was changed. No workflow approval or push was performed.

Reproducible check: `check_PR68_delta.py` (stdlib, pypdf and pdfplumber). Structured results: `PR68-delta-a64f93f-evidence.json`. Original mathematical audit: `PR-68.md`. No new primary-source consultation is necessary for this exact delta because all reviewed mathematical content and source citations are byte-preserved.
