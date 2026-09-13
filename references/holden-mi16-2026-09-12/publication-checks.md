# Publication checks — 12 September 2026 (13 September UTC)

The independent mathematical audit and [final publication audit](publication-review.md) both returned PASS. The latter's pending link check is resolved by this file.

- All 27 original archive files are byte-identical to the uploaded ZIP; every supplied manifest hash matches. The archived payload contains no extra runtime files.
- The final TeX is byte-identical to the original from Section 1 onward. The canonical README is byte-identical to upstream main from its original Problem statement onward. All 217 permanent IDs and canonical paths are unchanged.
- Required permanent-ID validation passed against both `origin/main` and `upstream/main`. Catalog regeneration passed. Counts relative to the submitted upstream base: 16 Lean verified, 52 Open, 72 Partially resolved, 77 Solved; 124 targets retain open cases.
- All 47 relevant repository tests passed: 17 permanent-ID, 16 math-formatting, 11 rendering (with Pandoc), and 3 status tests. Global math formatting reports zero pages needing changes. `git diff --check` passes.
- The independent reviewer reproduced 12,832 exact supplied checks, seven selector examples including the full p=1296 comparison, and 8,175 separately written rational checks. The coordinator also reran the independent checker and the original 1,848 subcase regressions. No Lean checks were run.
- The canonical TeX/PDF were regenerated with the repository renderer, Pandoc and XeLaTeX. The authored proof PDF was rebuilt with three successful pdfLaTeX passes. Final proof build reports no overfull boxes, undefined references, or warnings.
- All 19 authored proof pages and both canonical PDF pages were rendered and visually inspected. The authorship addition initially overflowed the title page; reducing only front-matter spacing fixed it. Final inspection found no clipping or overlap, and the independent reviewer additionally inspected the first page.
- Final payload hashes are recorded in `submission-hashes.json`; that manifest excludes itself. Source and original verification records are distinguished from newly generated review evidence.

The branch is submitted through a new fork pull request to `ajt60gaibb/OpenProblemsInNLA:main`. No direct push or merge into upstream main is part of this submission. The PR explicitly asks maintainers to review whether this finite algebraic answer meets their intended historical scope.
