# Publication checks — 13 September 2026

- Independent mathematical audit: PASS for full original NR-03 target.
- Supplied suite rerun with bundled Python 3.12.14: PASS; see submission-tests.txt.
- Separate set-based exact checker rerun with only its input root relocated: PASS; see independent-check.txt. No optimization flag was used (assertions active).
- Code and all certificate data compared byte for byte with the original upload: unchanged.
- Canonical context, original question and historical references/status-check suffix compared byte for byte with upstream main: unchanged.
- ID validators against origin/main and upstream/main: 217 permanent IDs pass.
- All 17 permanent-ID tests: PASS. Global math-format check: zero pages needing formatting.
- Catalog regenerated: 124 open targets (53 Open + 71 Partially resolved), down from 125; 77 Solved and 16 Lean verified. No IDs added or reassigned.
- Manuscript rebuilt with pdfLaTeX twice: six pages, author metadata Sidney Holden, no compilation/layout warnings. Removed one forced break after the added affiliation caused a nearly empty page.
- Canonical TeX/PDF rebuilt with repository Pandoc/XeLaTeX renderer: two pages.
- All eight resulting PDF pages rendered and visually inspected: no clipping, overlap or blank pages.
- Relative links in changed canonical/author/proof pages resolve locally.
- Whitespace checking permits the repository's intentional Markdown hard breaks and original CSV CRLF endings.
- No Lean verification performed. No external human peer review or novelty certification claimed.
