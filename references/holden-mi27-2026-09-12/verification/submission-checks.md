# Submission checks — 12 September 2026

- Independent analytic review: PASS; final manuscript hashes checked by the reviewer.
- Independent computational rerun: all six groups PASS; see `mi27-review-rerun.json` and `mi27-review-rerun.log`.
- Original archive manifest: all 12 checksums verified before editing.
- Duplicate screening: 34 fetched remote branches containing MI-27 all had Open status; upstream PR search and recent PR bodies found only partial PR #186, with no previously pushed full solution for MI-27.
- Permanent IDs validated against origin/main and upstream/main; registry unchanged.
- Catalog regenerated: open targets 125 -> 124; solved 76 -> 77; all 217 entries retained.
- 17 permanent-ID, 3 status, 16 math-formatting and 11 renderer tests passed.
- Canonical math-format check passed. Canonical PDF and attributed manuscript rebuilt and visually inspected. The renderer places MI-27 references on their own page to retain a coherent historical source record.
- No Lean verification performed. Numerical checks support consistency and do not replace the analytic proof.
