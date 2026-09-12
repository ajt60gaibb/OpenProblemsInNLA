# AA-01 / PR68 reconciliation plan

Read-only integration planning on 2026-09-11. Published main: `87366c62d3b5c47d170f747b1cb40ab38d501013`. Current locally fetched PR68 ref: `2a1a0b39992bbd5654e7bdf9f869e21a6cee0d71`. Merge base: `16369809e6e600144bd350ab70b7473b652f46f1`. These exact objects were inspected; no assumption is made that a later remote head is identical.

**Recommendation: retain both separately submitted AA-01 proofs at their existing paths, combine their resolution notices on the one permanent AA-01 page, and regenerate only the shared canonical presentation and catalogs.** Neither proof replaces the other. No new ID, title change, joint byline, or priority claim is needed. This plan carries forward the previously reviewed mathematical verdicts; it is not a fresh full audit of either proof.

## Confirmed facts

- The exact original AA-01 problem statement, model assumptions, references, and dated audit prose are identical in main, PR68, and their merge base. The only difference in the retained historical tail is that PR68 calls the last heading “Earlier status check” instead of “Status check.”
- Main's proof is Matthew J. Colbrook's Theorem 1.1, Sections 2–4, at `references/colbrook-arithmetic-2026-09-11/manuscripts/AA-01.tex` and `.pdf`, with two review reports and the full preserved submission package.
- PR68's proof is George Stepaniants's Theorem 2.1 and Corollary 7.1, at `arithmetic-and-complexity/AA-01/solution.tex`, `.pdf`, and `.md`; its original source and review/provenance records are under `references/stepaniants-2026-09-11/`.
- Both page summaries characterize accurate evaluability by a coefficientwise absolute majorant in signed gap coordinates, with a finite real-quantifier decision procedure. Both cover the same constant-free finite tree, stored-value reuse, branching, independent rounding, and zeros. The source theorem numbers belong to their respective manuscripts and must not be exchanged.
- There are **no overlapping proof-package paths**. An isolated `git merge-tree --write-tree` trial preserved every blob and file mode in the 218-file main arithmetic bundle and the 12-file PR68 provenance/AA-01-solution set.
- The exact trial conflicts are only `CATALOG.md`, `README.md`, `RESOLVED.md`, and AA-01's `README.md`, `problem.tex`, `problem.pdf`. The category README auto-merges, but should still be regenerated with the rest of the indexes.

Evidence is recorded in `reconciliation-evidence.json` with hashes of both proof packages and both submitted canonical snapshots. `trial-merge.txt` records the unresolved trial. It was performed only in `/private/tmp/nla-aa01-reconciliation-20260911`; no shared index/worktree or workflow was touched, and no document was rebuilt.

## Concrete resolution of each conflict

### 1. One canonical AA-01 README, two separately attributed proof notices

Use published main's AA-01 README as the starting text. Preserve its title, permanent ID, metadata, original problem statement and references. Keep **Status: Solved**; accepting a second proof must not add another problem or change the solved count for AA-01.

Immediately above the existing resolution notices, add a short maintainer sentence such as:

> Two separately submitted and independently reviewed manuscripts resolve the exact finite-tree decision question below. Both are retained with their own authorship, sources and review records.

Retain the entire existing `colbrook-arithmetic` resolution block, including its author, Theorem 1.1 locator, both review links, AI provenance, and qualification that missing experimental programs were not certified. That qualification applies to that package and must not be lost or generalized to the other manuscript.

Then add PR68's full resolution notice with a heading identifying **George Stepaniants**, preserving its Theorem 2.1/Corollary 7.1 links, exact-model description, independent-review link and ChatGPT provenance. Retain the existing source filenames; explicitly label links by author so the singular filename `solution.pdf` cannot be read as the sole accepted proof. Do not change the author affiliation already supplied in the reviewed submission, and do not infer independence of discovery from independent proof review.

Keep the original mathematical statement exactly once. Use “Earlier status check — 2026-09-10” for the final historical heading so the old dated observation of openness is clearly historical. The underlying dated prose should remain unchanged.

### 2. Canonical `problem.tex` and `problem.pdf`

These are generated presentations of the canonical README, and the competing resolution introductions account for their differences. Do not pick one side's PDF or attempt to merge TeX fragments. Once the combined README is final, generate both files with the trusted renderer from published main, retaining existing page-break behavior and visually checking the resulting pages.

Neither full manuscript PDF is a generated canonical problem page: leave both proof PDFs, both proof TeX sources, Stepaniants's Markdown solution, original-manuscript archive, and all submitted review/source records byte-for-byte unchanged.

The merge commit should retain both source heads as history, so each original canonical presentation remains recoverable by its exact commit/path. The evidence manifest records their hashes. If an externally readable frozen copy of the two old problem-page presentations is desired, place such copies in an explicitly labeled integration archive; do not overwrite either proof to preserve a canonical-page snapshot. This archive is optional because the merge history already preserves the original blobs.

### 3. `RESOLVED.md`

Retain all unrelated published-main sections and the incoming MD-03/MD-04 resolutions and their original theorem attribution. Keep one current AA-01 resolution summary under its existing main heading, with two clearly separated author/source paragraphs:

- Colbrook: Theorem 1.1; main manuscript PDF; first and second reviews; submission record and experimental-source qualification.
- Stepaniants: Theorem 2.1 and Corollary 7.1; `AA-01/solution.pdf`; its review and submission record.

Both descriptions must say the same AA-01 target is solved, without implying two catalog entries. If the incoming grouped “AA-01, MD-03 and MD-04” submission-history block is retained verbatim for provenance, its AA-01 item should link to the combined current summary and explicitly describe a second retained submission. Otherwise move its AA-01 author/source paragraph into the single current summary and keep the remaining incoming group focused on MD-03/MD-04. In either layout, retain every source/review link and all Guo–Fang–Lu theorem attribution for the discrepancy results. Repeated historical references to AA-01 are acceptable; duplicate current status rows or counts are not.

### 4. Root/category indexes

Preserve published main's non-generated prose, then regenerate `README.md`, `CATALOG.md`, and category indexes from the combined canonical metadata. Do not take the older PR68 totals: its base predates PR89 and the later accepted batch. AA-01 contributes no status delta because it is already Solved. The MD entries and any newer independently merged changes determine the remaining count deltas.

### 5. Provenance cross-links

Preserve both submission folders unchanged. If explanatory metadata is added, make it a dated maintainer integration note or separate integration record. Explain that the earlier network/eligibility checks in PR68 describe the stated pre-submission snapshot and do not deny the later PR89 acceptance. Do not rewrite `network-check.json`, old review hashes, or historical check results to match today's main.

Add links to both source packages from the current AA-01 page and, if needed, `references/README.md`. An integration record should name the two exact input heads and identify the shared generated files as the only deliberately recomposed AA-01 artifacts.

## Verification required when this plan is implemented

1. Recheck the live source heads; audit any genuine later delta before merging. Use trusted current main, not an old feature branch's renderer, metadata totals, or workflows.
2. Compare every proof-package blob and mode against the manifests here; require zero mismatches. Confirm the original AA-01 mathematical target and reference/audit tail are unchanged apart from the explicitly historical heading.
3. Validate all then-current permanent IDs against the accepted base, run the seventeen safeguard tests, and regenerate indexes. Confirm one AA-01 registry row and one canonical status row.
4. Check every manuscript/review/source link in the combined page and resolution summary. Verify no Colbrook or Stepaniants source attribution was dropped and no shared authorship or discovery priority was introduced.
5. Rebuild and visually inspect the combined AA-01 canonical PDF. Its proof manuscripts need only byte checks because they are retained exactly. Run `git diff --check` and inspect the final changed-path set, ensuring unrelated accepted contributions survive.

This plan authorizes no remote operation or workflow execution. No implementation or regeneration has been performed here.
