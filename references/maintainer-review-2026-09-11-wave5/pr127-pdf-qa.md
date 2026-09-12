# PR #127 IE-05 PDF/source packaging QA

Date: 2026-09-11. Reviewer: Codex agent `/root/audit_inequalities`.

**PASS for PDF/source packaging and the isolated rendering additions. No artifact blocker found.** Preserve the newer main renderer rules during integration, as detailed below. The parent and mathematical auditor separately assess the proof and final merge.

Frozen reviewed head: `e5ad08c1a301d532ea200df8580224bb893b2240`.
Published target-comparison base: `d8cc1134bc5b6c288b9841995e26daf411c8941e`.
Canonical path: `linear-systems-and-elimination/IE-05/README.md`.

## All-page visual review

The two canonical PDF pages and four complete-solution PDF pages were rendered with Poppler to individual temporary PNGs at maximum dimension 1700 pixels and inspected in full. All six pass: no clipping, overlap, missing glyph, incomplete formula or illegible table was found. PDF extraction independently found zero replacement characters and zero characters outside page bounds. Author metadata is visible in both documents.

The canonical pages preserve the negative-resolution notice, exact original element-growth definition, tie conventions, positive-diagonal QR candidate, supremum over orthogonal matrices and all admissible paths, and original references/status history. The solution pages display all three integer matrices H, T and H0 clearly. Both initial maximum-entry norms, 63^2/5272 for the witness and 51^2/3286 for the candidate, are printed legibly and distinctly. Both complete eight-stage tables have legible headers, correct source correspondence, and unambiguous scalings; neither is split across pages. The concluding squared-growth comparison and limited scope remain clear.

## Source and manifest checks

All 84 solution mathematical expressions and 19 canonical expressions match the generated TeX exactly in their original order after whitespace removal. All 16 table-data rows match cell-for-cell between Markdown and TeX, including stage numbers, locations, values and radical denominators. Matrix entries and norm formulas are included in the full formula comparison. These checks establish correspondence, not an independent proof of the algebraic claims.

Everything from the canonical Context and notation heading onward is byte-identical to current published main. The original target and history are preserved. Independently checking all byte counts and hashes in `document-checks.json` found 49 matching files and no mismatch.

Both submitted checkers were read before execution with `python3 -B` at the frozen head. `check_submission.py` performs local file/hash checks, read-only git queries and a call to the separately inspected layout checker. It passed complete reviewed-proof preservation after removal of 23 specified layout directives; the original target; all packaged fingerprints; 203 original IDs; the 202 other historical canonical pages; historical resolution/reference preservation; and 54 local links.

`check_layout_move.py` safely intercepts the first Pandoc subprocess call before any canonical TeX/PDF write or compilation. It creates only disposable metadata in a temporary directory. It passed equality of the actual effective Pandoc body and metadata before/after moving the raw page break out of Markdown into the renderer. It also verified unchanged solution Markdown, solution TeX/PDF and canonical TeX/PDF against the prior manifest. No document rebuild was performed by this reviewer.

George Stepaniants and his Caltech affiliation are consistently displayed as the proof's attribution. John Peca-Medlin retains credit for the conjecture and cited element-growth analysis. The package distinguishes the negative resolution of the exact extremizer equality from the separate asymptotic growth/leading-constant questions and discloses AI assistance and automated-review limits.

## Shared renderer/template review

The new solution-template block is guarded by `$if(tables)$`. It loads `longtable`, `booktabs` and `array` and declares the `none` counter used by the generated unnumbered longtables. The shipped TeX uses the corresponding `longtable` environments, booktabs rules and `LTcaptype=none` convention. Removing precisely that conditional block makes the template byte-identical to current main. Thus the textual template change is isolated to documents for which Pandoc sets the table flag. The optional email conditional is already present on current main; it is not an additional integration change.

The renderer addition is guarded by exact identifier `IE-05`, inserts one page break before the unique Context and notation heading, and does not alter mathematical content or other identifiers' execution paths. The inspected layout-equivalence checker confirms the IE-05 generated input remains unchanged.

**Integration caution:** the branch predates main's later renderer edits. Merge the isolated IE-05 block into the current main renderer; do not replace that file wholesale. Main's reference breaks for IE-02, MI-28 and the later-added entries, target breaks for SP-11/SP-12, and RA-10/AA-01 layout rules must remain. The parent was notified before integration. This is a branch-base reconciliation requirement, not a defect in the new conditional itself.

The frozen submission's checker also binds to the historical 203-ID registry and historical global artifacts; current main has newer entries. Leave that archived checker unchanged and use the repository's base-aware validator and artifact-preservation checks for the integrated checkout.

## Frozen hashes

| Artifact | SHA-256 |
| --- | --- |
| `README.md` | `8dda07df642a6ef407d9c8e5fa07839b57ef2ba81cd41b230f367353fef67dea` |
| `problem.pdf` | `686c0d83c3352defba1c414ffea4b1dccf5fd577f8a8550cd4cb73348a4fabdb` |
| `problem.tex` | `a9834f98854edeb2ca64c831a273b3a612848a5813a335d6c4d223fd17dfaa63` |
| `solution.md` | `1b94eda6df18066f2f09b66b8b28a18ca071c0c2fb070b536dc8c798992ae434` |
| `solution.tex` | `7282b644fa4f83612393c2a0d9679a77f0e30b10c2cad1aa94002b3c3fed3d3a` |
| `solution.pdf` | `e35721db7408fe5f4d90c9963cfd8d51098bbf25a0a100d51e85e45b0dd8ae83` |

The PDF page counts are problem.pdf = 2 and solution.pdf = 4. The source snapshot is `/private/tmp/nla-review-inequalities/pr127-source/`; machine-readable checks, extracted text and the six inspected page PNGs are in `/private/tmp/nla-review-inequalities/pr127-pdf-qa/`, including `snapshot.json` and `checks.json`.

This reviewer wrote only scratch snapshots, rendering output and this report. No canonical source, PDF, checker, repository or remote state was edited. The frozen-head verdict does not independently certify later integration, external publication status or historical priority.
