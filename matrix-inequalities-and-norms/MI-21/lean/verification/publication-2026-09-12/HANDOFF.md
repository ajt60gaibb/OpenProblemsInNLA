# MI-21 publication preparation handoff

**Prepared for independent final publication review; no commit or push made.**
The isolated branch is `codex/lean-mi21-geometric-mean` in
`/tmp/nla-lean-mi21-worktree`. `HEAD` remains the actual verified proof commit
`06ade659dee260a18b79ce638383bf0a49125ecf`. Upstream
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc` was merged cleanly with
`--no-commit --no-ff`; `MERGE_HEAD` deliberately remains pending for the root
reviewer's final integration commit. No mathematical merge conflict occurred.

The prepared change adds the completed independent Linux operational audit
and all original evidence, updates the manifest and project guide, promotes
the canonical MI-21 entry, adds the formalization credit to `RESOLVED.md`,
regenerates the indexes, and renders the canonical two-page PDF. George
Stepaniants's full Caltech department affiliation is visible in the canonical
page, PDF, archive and formalization metadata. Matthew J. Colbrook retains
mathematical authorship; no George email is published.

## Verification and protected bytes

- The actual Linux run is
  [34709291489](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34709291489),
  accepted at immutable proof commit `06ade659dee260a18b79ce638383bf0a49125ecf`.
  Both original artifact ZIPs, all 23 extracted members, raw selected job logs,
  full source identity and operational review are retained unchanged under
  `../linux-2026-09-12/`. Its original manifest binds 58 other evidence files.
- All **79** original project inputs other than the two authorized current
  metadata pages (`lean/README.md`, `formalization.yaml`) are byte-identical
  to the successful proof revision. This includes every frozen Lean source,
  the comparator configuration, all pins and all frozen review/evidence files.
- The full original `## Problem statement` suffix is byte-identical to
  upstream, including its references and dated historical source check.
  Informal `solution.tex`, `solution.md` and `solution.pdf` are unchanged.
- All **216 other canonical pages** are byte-identical to integrated upstream;
  its RA-03 promotion is retained. Shared harness, docs and workflow files
  are unchanged. The append-only 217-ID registry is unchanged.

The complete before/after record is `integrity.json`, produced by the retained
read-only `check_integrity.py`. The publication file identities are recorded
there, separately from the immutable Linux evidence manifest.

## Actual checks and PDF review

Both permanent-ID validators passed against `origin/main` and
`nla-upstream/main`. Catalog generation against `origin/main` completed, and
all **17** required permanent-ID tests passed. Metadata validation passed the
actual v0.4 schema and exact **three-export** Comparator coverage. The
repository math-format check reported **0 pages** needing changes. Diff
checking of the edited publication text and generated TeX passed. Original
raw logs retain their original whitespace; they were not sanitized to change
their digests. A diff against the pre-merge HEAD naturally also contains
upstream's already-published RA-03 raw logs.

The regenerated catalog reports **57 Open, 71 Partially resolved, 82 Solved,
7 Lean verified**. The seven verified IDs are IE-01, IE-18, IE-19, MI-19,
MI-21, RA-03 and TR-01. Counts were regenerated after integration even though
the merge produced no conflicts.

The canonical `problem.pdf` was rendered through the repository's own Pandoc
and XeLaTeX path with no layout warnings. Both pages were rendered with
Poppler and inspected individually. Page one shows the title, status,
authorship, scope and exports; page two keeps the complete original target
and references together. No clipping, overlap, illegible glyphs or broken
formula was found. `pdf-visual-review.json`, `pdfinfo.log` and `pdf-render.log`
record that review. The local PNGs for independent inspection are under
`/tmp/nla-lean-formalization/pdf-mi21/` and are not submission artifacts.

No Lean proof rebuild was repeated for these publication-only changes:
all mathematical inputs remain exactly those already checked by both final
referees and the actual successful Linux kernel/Comparator run. Root now
independently reviews the final diff and PDF before committing, pushing,
updating the PR and requesting upstream inclusion.
