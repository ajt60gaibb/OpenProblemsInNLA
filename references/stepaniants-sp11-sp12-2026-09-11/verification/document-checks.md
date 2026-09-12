# SP-11/SP-12 document and preservation checks

Prepared by Codex agent `/root/review_md03_md04` on 11 September 2026 in an isolated worktree based on upstream commit `87366c62d3b5c47d170f747b1cb40ab38d501013`. No issue, pull request, commit, or push was performed by this packaging agent.

## Required repository checks

- `python3 tools/validate_problem_ids.py --base-ref origin/main`: PASS, 203 permanent IDs.
- `python3 tools/update_catalog.py --base-ref origin/main`: PASS, after the explicit validator. Result: 203 retained entries, 68 Open, 72 Partially resolved, 1 Solution claimed, 62 Solved. These counts reflect this isolated branch's base plus the two status corrections.
- `python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v`: PASS, all 17 tests.

No registry ID or path was changed. Both original canonical bodies from `## Problem statement` to EOF remain byte-identical to their accepted base versions, which are retained in `original-targets/`. Earlier attributed partial results and historical searches remain present. Their historical scope is explained by the new resolution notices.

## PDF generation and visual inspection

The PDF skill's artifact marker completed successfully once immediately before authoring this batch, with operation `create`, expected output count 4, format `pdf`. Both solution manuscripts and both canonical documents were rendered with the repository's Pandoc/XeLaTeX tools, with two XeLaTeX runs per document. The renderers reported no overfull boxes or missing characters.

| Final PDF | Pages | All-page visual result |
|---|---:|---|
| `eigenvalues-and-inverse-problems/SP-11/solution.pdf` | 2 | PASS, pages 1-2 inspected |
| `eigenvalues-and-inverse-problems/SP-11/problem.pdf` | 2 | PASS, pages 1-2 inspected |
| `eigenvalues-and-inverse-problems/SP-12/solution.pdf` | 3 | PASS, pages 1-3 inspected |
| `eigenvalues-and-inverse-problems/SP-12/problem.pdf` | 3 | PASS, pages 1-3 inspected |

Every final page was rendered at 100 dpi with Poppler and opened for visual inspection. Author and affiliation, mathematical symbols, block matrices, references, scope statements, and page numbers are legible; no clipping, overlap, missing glyphs, or detached headings were observed. Canonical target page breaks live in `tools/render_problems.py`, not the canonical Markdown. The solution template's email block is now conditional; no email is supplied.

The [frozen source checkpoint](source-checkpoints.json) records exact Markdown, TeX, PDF, review, audit, and renderer hashes. The manuscript formatting adds standard mathematical notation and standalone definitions to the supplied text. It does not modify the original archived package or assert missing experimental evidence. The separate root-agent final conversion review returned PASS and is preserved in `SP-11-SP-12-packaging-review.md`; it independently compared the complete original and publication notes, checked all ordered formulas and canonical target suffixes, and inspected all five application-note PDF pages.

## Preservation and verification limits

The portable `check_submission.py` checks all six original archive hashes and the five supplied checksums, both exact original target bodies, ordered mathematical expressions in each Markdown/TeX pair, local links, the fixed 203-ID registry digest, frozen artifact hashes, and absence of personal emails from submitted text. Its actual output is retained separately in `submission-check-output.json`.

The portable network script was syntax-checked, and its local registry lookup was checked. It was adapted from the actual parent audit to use portable CLI/output paths and retain only content digests. A second full network request was not needed; the parent's dated, sanitized audit is preserved unchanged. Any future rerun requires an authenticated GitHub CLI and fresh manual classification of keyword matches.

These checks establish preservation and document quality. They are not graph-atlas runs, numerical evidence for an all-graph theorem, human peer review, or formal proof certification. The separate mathematical review records the analytical basis and limits of the Solved classifications.

## Final local checkpoint

The portable submission check returned PASS: six unchanged original files, five supplied checksums, two unchanged canonical target bodies, 19/16 ordered solution/problem formulas for SP-11 and 98/20 for SP-12, all 203 IDs, frozen file hashes, local links, and no personal email in submitted text. The archived canonical snapshots' relative links are checked from their original canonical locations. `git diff --check` passed. Removing trailing spaces from the changed status lines was separately verified to leave the renderer's parsed metadata and body exactly unchanged, so it did not change the final TeX or PDF layout.

The parent's separate final public-eligibility refresh at 23:51:45 UTC is archived in `network-before-push.json`, unchanged and included in the frozen hashes; it again found both targets partially resolved throughout the visible network. The original earlier snapshot remains unchanged.

The final packaging review is 6,196 bytes with SHA-256 `5ff6c550e717ff0396fe4b02aed2d4d8231e2896baf60e5a3915a323dc42eebb`. Linking that unchanged addendum was the final metadata change; no mathematical source or PDF was modified. The final portable check output and external handoff manifest record the resulting frozen files.
