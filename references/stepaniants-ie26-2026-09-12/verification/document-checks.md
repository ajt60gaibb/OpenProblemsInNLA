# IE-26 packaging and document checks

Packaging agent: `/root/review_md03_md04`. Date: 12 September 2026 (UTC).

## Scope and source preservation

The independent full-target report is the unchanged [signed review](independent-review/IE-26-independent-review.md), SHA-256 `995aa6144f2e8875c9e330d84230786ee46be45a18e5e28cef0b6fc6fef4ce92`. This packaging check verifies conversion and provenance; it does not substitute for that mathematical review.

The original 20,755-byte proof remains unchanged, as do its source manifest, original target, coordinating check, and the complete seven-file independent reviewer directory. The publication Markdown retains the entire 16,618-byte mathematical Sections 1–7 exactly, SHA-256 `0f9222764933df1602163748f6d8c8755f7e45ab9e25139733d2b92851879f55`. All canonical content from `## Statement` through the final historical source-check paragraph remains byte-for-byte identical. Publication metadata records the later review outcome separately from the frozen pending-review history.

The first estimate retains one absolute constant for every `0 < alpha < 1/2`. The second retains an alpha-dependent constant for every fixed `1/4 < alpha < 1/2`, with no endpoint assertion. The row-index convention is explained explicitly; the inverse norm is unchanged under the transposed frequency-row convention. No mathematical clarification was inserted into the reviewed body. The independent report explains the intended blocks of length R, except for the last shorter block.

## Repository checks

The worktree is based on `1f22006bdaa4659fcaa0bb775a887685cd3cc566`, branch `codex/stepaniants-ie26-fourier-stability`. The registry remains unchanged with 217 permanent ID/path mappings. The following commands completed successfully during packaging:

```bash
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/validate_problem_ids.py --base-ref refs/remotes/upstream/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
```

Both validators reported 217 IDs; `origin/main` resolved to `ab754fabe3d48dc8d6eab6bcffce583e46d2b88f`, and the checked upstream ref resolved to the worktree base above. All 17 identifier tests passed. Index regeneration reported Open=64, Partially resolved=74, Solved=78, Lean verified=1. The only changed problem status is IE-26.

The optional plain `git diff --check` flags only the two deliberate Markdown hard-line-break spaces after the changed Status value, following the retained metadata style. With end-of-line blanks excluded for that formatting convention, the whitespace check passes. No identifier safeguard is relaxed, and no frozen source is changed for this cosmetic diagnostic.

The [offline checker](check_submission.py) compares the reviewed core, original canonical suffix, 272 ordered proof math expressions and 37 ordered canonical math expressions, exact source/artifact fingerprints, local links, the complete registry, and allowed author/affiliation metadata. It checks the generated TeX's formula order after whitespace normalization; it is a conversion check, not a mathematical proof. Its captured result is [submission-checks.json](submission-checks.json).

Run it from any directory:

```bash
python3 references/stepaniants-ie26-2026-09-12/verification/check_submission.py
```

The contact-address scan passes. For Python files it examines strings and comments so the matrix-multiplication operator is not misclassified as an address. The authoring source and exact reviewer snapshots were not changed to satisfy the scan. No contact email is present in new public text or PDF content.

## PDF generation and every-page visual inspection

The PDF skill's create marker was run once, with expected output count two, before the first authoring command in this batch. The accepted solution template already makes the contact field optional; no template change was required.

Both documents were rendered through the repository's Pandoc/XeLaTeX tools. Each emitted standalone TeX source was compiled twice in an isolated temporary directory. Pandoc 3.11 and XeLaTeX were used, with `PANDOC` pointing to the installed executable. Final runs reported `IE-26 solution: OK` and `IE-26: OK`, with no overfull or missing-character warnings.

```bash
python3 tools/render_solutions.py IE-26
python3 tools/render_problems.py IE-26
```

The renderer changes are limited to IE-26 presentation: the three original Unicode proof-ending marks use a math-font black square, headings and displayed formulas stay with their context, Section 2 starts on a fresh proof page, and the retained canonical statement and reference block start on appropriate pages. The GitHub Markdown body has no added TeX layout directives. Every mathematical expression remains in order.

The final proof PDF has **9 pages** and the final retained problem PDF has **3 pages**. All 12 final pages were rendered at 110 dpi and individually inspected by this packaging agent. The byline, complete department/university affiliation, exact parameter ranges, equations, source links, reference lists, review disclosure, page numbers and headers are legible. There is no clipped or overlapping material, missing glyph, isolated opening word, split pair of canonical target inequalities, or fragmented canonical reference block. The proof's three end markers are visible. The private page images and their manifest are retained for the coordinating agent's separate conversion review; they are not bundled as public evidence.

The [artifact checkpoints](source-checkpoints.json) bind the six immutable canonical files, including both PDFs. The proof PDF has SHA-256 `dd55cc943beb4acbfa3102d5c74f580496edb1f3071add369107318a896b66bc`; the problem PDF has SHA-256 `97cf89b65d5096cb67f2ff7d6ba64c78be2244b457eb4b7db054b3fee5233461`.

## Eligibility, attribution, and handoff

The [final broader public audit](final-public-audit/README.md) preserves the 02:10:34 UTC check separately from the original narrower source audit. IE-26 was Open on 11 public heads and absent on 29 older heads; both the target and its Open status were present on current upstream main. The admission PR111 contained no solution. No competing resolution was found in the bounded public search. The three final audit files are copied byte-for-byte, with raw bodies retained privately.

The publication identifies George Stepaniants with Department of Computing and Mathematical Sciences, California Institute of Technology affiliation. Austin, Trefethen, the cited later authors, and Laugesen retain their respective contributions. AI assistance, reviewer independence, and the difference between informal automated review and human or formal verification are explicit.

Only the newly authored manuscript, retained problem artifacts, original review/check text, scripts, sanitized public evidence and fingerprints are included. No third-party PDF, extracted publication text, page image, private contact information, or credential is redistributed. No commit, push, issue, pull request, or public message was made by this packaging agent. The coordinating agent performs the final independent conversion review and publication steps.
