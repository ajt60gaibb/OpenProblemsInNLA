# RA-13 final document and repository checks

Checked 11 September 2026 by the preparing Codex agent. This records local preparation; it is not a claim that a commit, issue, pull request or merge has already been published.

## Mathematical and identity checks

The [full independent review](RA-13-independent-review.md) passed the complete canonical target. The [notation addendum](notation-conversion-addendum.md) permits the two spacing fixes and the one Greek-letter restoration. The separate [final packaging review](RA-13-packaging-review.md) passed the exact canonical Markdown and TeX, all 172 ordered mathematical expressions, the retained statement and attribution. The original frozen proof and signed report are unchanged.

The executable [source-identity check](verify_source_identity.py) and [output](source-identity-check.txt) verify the frozen hashes, the three permitted notation changes, exact remaining mathematical-body bytes, exact original target, and the auxiliary-result block apart from its now-historical scope sentence. The author, department and university are present; new source/evidence files contain no contact-address strings. Public contact-address strings in the network capture were redacted without changing mathematical/status content.

## Repository safeguards

- `python3 tools/validate_problem_ids.py --base-ref origin/main`: PASS, all 203 permanent IDs. [Output](validate-origin-main.txt).
- `python3 tools/validate_problem_ids.py --base-ref refs/remotes/upstream/main`: PASS, all 203 permanent IDs against the published base. [Output](validate-upstream-main.txt).
- Only after validation, `python3 tools/update_catalog.py --base-ref origin/main`: PASS; Open 74, Partially resolved 78, Solution claimed 1, Solved 50. [Output](catalog-update.txt).
- `python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v`: all 17 tests PASS. [Output](id-tests.txt).

The isolated branch is `codex/stepaniants-ra13-trace-tails`, based on upstream/main commit `aaa88c4`. The canonical target, registry and IDs were not renumbered, replaced or deleted. The optional-email template change consists only of enclosing the existing contact line in a conditional block. No global Git configuration was changed by the preparing agent.

## PDF generation and complete visual inspection

The PDF skill's create marker ran successfully once before authoring this two-PDF batch. Pandoc 3.11 and XeLaTeX were used through the repository's `render_solutions.py RA-13` and `render_problems.py RA-13`, with the installed Pandoc path supplied through `PANDOC`. Both renderers reported **OK**, with no overfull-box or missing-character warning.

The final `solution.pdf` has **six A4 pages**. The final `problem.pdf` has **two A4 pages**. Every final page was rendered with Poppler and visually inspected after the last respective source change. All formulas, Greek symbols, equation tags, links, headings, authorship, affiliation and pagination are legible; no clipping, overlap, missing glyph or broken mathematical line was found. The corrected Greek nu is visible in the definition and all subsequent kernel integrals. The canonical problem starts on its own second page; this is a layout-only `\newpage` before the original problem heading, outside the retained target. Headers and verification footers are present on every proof page. Text extraction and PDF metadata were checked as supplements to visual inspection, not substitutes for it.

The proof PDF metadata author is George Stepaniants. The problem PDF retains the repository's catalog-author metadata while visibly attributing the resolution to George Stepaniants and preserving Matthew J. Colbrook's auxiliary result. Neither final PDF nor its generated TeX contains a contact-address string or a `mailto:` link.

## Final canonical artifact hashes

| File in RA-13 | SHA-256 |
| --- | --- |
| `solution.md` | `afc1b17cc61164093c5038e786934bc710ef141b9747c9a8a10ca8ab16414677` |
| `solution.tex` | `8bfde617822abef81989b3c1da94f9390f0e56cad23efaa37f107f91f42e63f9` |
| `solution.pdf` | `9a0d4da8c1a65fd1516af8d706be21bc5c05f146bfabe42e0516b86c55fcf0ad` |
| `README.md` | `c51baf8fb49622a63509eba9f0f1380150e5afc5ec0da8ac74ed2c37ed10ff5e` |
| `problem.tex` | `fcbe9de6b7c19a9a3729b26ca834fd27adbaaabcf52c7242c829c117902c0386` |
| `problem.pdf` | `3c9eea52c935364e34fb415ffead2dc4739caddc89ae5ec9a329821695a0492b` |

The [artifact manifest](artifact-manifest.json) records the full prepared file set. [Final local link check](local-links-check.txt) and [whitespace check](diff-check.txt) complete the local checkpoint. Raster QA intermediates remain outside the repository under `/tmp/nla-fresh-round1/ra13/tmp/pdfs/`.

The fresh network status and its exact scope/timestamps are in the [main audit](network-check.json) and [supplementary discussion audit](network-discussions.json). The latter read all 16 PR review bodies and confirmed GitHub Discussions was disabled in all five public repositories. The only relevant review concerned the existing auxiliary result, not a full RA-13 solution.

The coordinating agent verified every prepared artifact hash, reran the exact source-identity check, read the complete independent proof and conversion reviews, and performed the final public-network check at 22:57 UTC. All 30 branch heads still recorded RA-13 as Open. The final audit is retained as `network-before-push.json`; publication metadata and record additions alter no proof or PDF.
