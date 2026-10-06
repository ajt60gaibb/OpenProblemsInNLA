# Integration and document validation

Date: 6 October 2026. Performed by the coordinating Codex agent on branch
`codex/mi18-issue329`, based on published commit
`412489c6c52f49653bf069ac2f85e92034cdbfa5`.

## Passed checks

- All **217 permanent IDs** validate against `origin/main`. The registry is
  byte-identical to the base. The original MI-18 problem statement is
  byte-identical, and every previously retained order-four artifact is unchanged.
  See [preservation check](preservation.json).
- [All 17 permanent-ID tests](id-tests.log) pass.
- [All 84 repository tests](repository-tests.log) pass, including catalog
  statuses, Lean manifest/selection safeguards, math rendering and statement
  inventory tests. Pandoc 3.9 and Python 3.13.14 were used. Initial attempts found
  missing PyYAML; PyYAML and jsonschema were then installed into a temporary
  dependency directory and the complete suite passed. No runtime dependencies
  were added to this repository.
- [All seven inventory tests](inventory-tests.log) pass after adding MI-18's
  external statement metadata. The normal inventory `--check` passes with its
  preserved published base `baa79cd88c1ec889d122254a1c361608b8ff7c74`.
  Only MI-18's entry changes. This source inventory does not itself verify proofs.
- `tools/format_math.py --check` reports zero pages needing formatting.
- Catalog generation changes the open-target count from **104 to 103** and
  partial count from **66 to 65**; Lean verified increases from **68 to 69**.
  Open remains **38**, Solved **44**, and Solution claimed **1**. There are no
  Needs verification or Withdrawn entries. The total stays **217**. The matrix
  inequalities category has **13** entries with open targets, previously 14.
- The [exact certificate computation](certificate-check.json) passes, as do the
  additional independent checks in the [manuscript audit](manuscript-audit.md).
- Local links in the changed MI-18 and review documents resolve. Whitespace
  checking passes with Markdown's intentional two-space hard line breaks
  permitted (`git -c core.whitespace=-blank-at-eol,blank-at-eof,space-before-tab diff --check`).

## PDF and TeX checks

Both the three-page canonical `problem.pdf` and the eight-page `solution.pdf`
were regenerated with the repository's renderers, Pandoc 3.9 and XeLaTeX. Both
final renders reported `OK`, with no overfull boxes or missing-character
warnings. All pages were rendered to PNG with Poppler and visually inspected.
Equations, all 144 ordered certificate triples, references, links, and footers
are legible and unclipped. The certificate table fits on one page.

Two small renderer accommodations keep public mathematical prose unchanged:
MI-18's canonical footer calls its date a verification check; its manuscript
gets page-break/table-layout rules. The solution template loads LaTeX `calc`
when tables are present, as required by Pandoc's calculated column widths.
The manuscript's Markdown and all mathematical/data files retain the exact
final bytes approved in the manuscript audit.

This validation is an integration and arithmetic check. **No Lean kernel rerun
was performed locally.** The formal evidence level and limits are recorded in
[the evidence audit](evidence-audit.md).
