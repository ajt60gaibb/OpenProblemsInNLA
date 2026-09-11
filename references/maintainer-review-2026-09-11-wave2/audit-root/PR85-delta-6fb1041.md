# PR #85: review of the contact-redaction update

Reviewed old head: `bf70552daecf8c6275ef1eb73f73aac664358228`.
Reviewed new head: `6fb1041e83823f726a326b33ef8169cd593df631`.
Review date: 2026-09-11.

**Verdict: the mathematical PASS carries to the new head. One historical PDF fingerprint needs correction before the supporting verification record is accepted as accurate.** The correction is documentary and does not change the proof, its hypotheses, the resolved scope, or the rendered mathematical content. This is mathematical agent review, not proof-assistant certification or external human peer review.

The new commit was fetched read-only into a separate temporary clone and archived in `pr-85-current`. The frozen `pr-85` snapshot and shared integration checkout were left unchanged. The exact commit delta comprises nine modified files, with no additions or deletions.

## Mathematical scope and exact content comparison

The earlier review in `PR-85.md` establishes the positive-definite target of MI-28 for every `k >= 0` and `0 <= p <= 2`, including the stronger normalized log-majorization. Its analytic argument checks the two Furuta parameter regions, the noncommuting factor order and inversion in the parameter swap, the coverage of all remaining parameters, the published `k >= 2` lemma with its exact substitution, exterior powers, and the endpoint continuity argument. The earlier independent exponent checks and 324 complex positive-definite diagnostics remain relevant because the theorem, proof and verification scripts are unchanged.

Independent whole-source comparisons establish the following, without relying on the contributor's review labels:

- Canonical `solution.md` differs only by deletion of its email metadata line.
- Canonical `solution.tex` differs only by deletion of the contact line; its entire mathematical body is byte-identical.
- The preserved manuscript Markdown differs only by deletion of the contact header line. The preserved manuscript TeX additionally moves the author block's closing brace to the preceding affiliation line. Its entire document body is byte-identical.
- All four newly recorded mathematical-core byte lengths and SHA-256 digests match actual source substrings, and each entire substring also occurs byte-identically in the old source.
- The canonical `README.md`, `problem.tex` and `problem.pdf`, the permanent ID registry, the numbering workflow, the rendering scripts and the manuscript's Python verification scripts are byte-identical to the reviewed head.
- The shared solution template changes only by guarding the existing contact line with the optional email conditional. The remaining text changes explain the redaction and update its evidence.

Therefore this update introduces no new mathematical assertion, scope expansion or changed original target. MI-28 retains its original number and canonical path.

## Required supporting-record correction

At new-head `references/stepaniants-mi28-2026-09-11/verification/document-checks.json:93`, the field `pre_email_redaction_record.pdfs[0].sha256` contains the new PDF digest:

`2d9cf1edcdd6a30fd0a6f47313d97e4f44fea0277319588ae282cdd32fc91f70`

That field explicitly describes the historical, pre-redaction PDF, whose actual SHA-256 digest in both the frozen old snapshot and old commit is:

`f225b707eef5a0684b705f3b6a02d1fc083a1cbd4842439d19695172ef0b2be5`

Replace only the historical field with the latter digest. Retain the current digest in the top-level `pdfs` list. All other checked current and historical source/PDF fingerprints and page counts are correct. This finding concerns provenance accuracy; it does not undermine the unchanged mathematical proof.

## PDF and reproducible checks

`pr85_delta_checks.py` performs **55 checks: 54 PASS and the one historical-fingerprint failure above**. Its result is recorded in `pr85-delta-qa/checks.json`; the failure is retained explicitly rather than hidden or treated as a passing assertion. Run it with the bundled Python environment containing `pdfplumber` and Pillow:

```sh
/Users/ajt253/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3 /private/tmp/nla-review-wave2-artifacts/audit-root/pr85_delta_checks.py
```

All five pages of the regenerated canonical solution PDF were rendered and visually inspected. The title, displayed mathematics, lemma transitions and references are legible, with no clipping, overlaps or missing glyphs observed. The full extracted PDF text agrees with the old PDF after removing only the contact address, whitespace and page-number footers. The new PDF has zero out-of-page characters and zero replacement glyphs; its text, metadata and annotations contain no removed contact. The unchanged two-page canonical problem PDF was not redundantly rerendered.

Evidence consists of five individual page PNGs, `all-five-pages.jpg`, two extracted text files with the old contact redacted, and `checks.json`. The report and check script never embed the removed contact address.

This local mathematical/document review neither approves nor executes GitHub workflows. The separate workflow-approval restriction remains in effect.
