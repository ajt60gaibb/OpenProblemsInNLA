# Submission validation — 12 September 2026

- Original archive contents match every supplied SHA256SUMS entry.
- Independent mathematical audit: PASS, full target (see independent-review.md).
- Submitted finite checker rerun: PASS (see rerun-checks.json).
- Permanent-ID validation passed against origin/main and upstream/main; all 217 IDs retained.
- Catalog regenerated: open targets 125 → 124; solved entries 76 → 77.
- Permanent-ID tests: 17 passed. Status tests: 3 passed. Math-format/render tests: 27 passed.
- Global GitHub math check: no pages need formatting. Git diff whitespace check: passed.
- Authored manuscript compiled twice with pdfLaTeX; canonical problem regenerated with the repository renderer, Pandoc and XeLaTeX. All pages visually inspected. The obsolete TR-08 reference-page break was removed from the renderer so the enlarged canonical page occupies two pages without a nearly empty intermediate page.
- No Lean verification performed. Archived experiments were not rerun.
