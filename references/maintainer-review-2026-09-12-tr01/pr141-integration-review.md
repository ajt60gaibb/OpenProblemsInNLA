# PR141 integration preservation review

Verdict: **PASS**, read-only integration snapshot at 2026-09-12 11:44 UTC.

Compared `/private/tmp/nla-pr141` working tree against main commit
`24f4c834b4245fc9ce55003689a6db5e579be3d5`; branch HEAD at inspection was
`9e6bff5711603467878e8a74f525a7d53d635cbd`, with the current main merge pending.
The comparison is against main's full tree, not the branch's older HEAD, so
the nine other accepted submissions and earlier changes are included in the
preservation check.

The independent checker reads every one of main's 2,633 files and computes its
Git blob identity and filesystem mode. Exactly the seven intended existing
files differ: the three global/category generated indexes, `RESOLVED.md`, and
TR-01's canonical README/TeX/PDF. All other 2,626 files are byte-identical and
mode-identical, including:

- All 791 files under the other 216 canonical problem directories, including
  their current statements, proofs, certificates, and exports.
- All 1,805 existing files under `references/`.
- The registry and all checked policy, renderer, validator, test, and CI files.

The complete 217-entry `problem_ids.json` is byte-identical; all ID/path pairs
are unchanged, every published canonical path exists, and each README retains
its proper ID heading. TR-01's full original `Problem statement` section and
original `References` section are byte-identical to main. The problem-section
SHA-256 is `4aca56516048c4196073b8b1315314c782ab0579638a202ea0230a88f159bc87`.

Removing the single inserted TR-01 resolution block from the current
`RESOLVED.md` reproduces main's `RESOLVED.md` exactly. There is exactly one TR-01
heading and one `tr-01` explicit anchor. The four explicit anchors and the 98
heading slugs have no duplicates or cross-collisions. Existing main resolution
prose, ordering, and attribution are preserved.

The generated `CATALOG.md` retains all 216 unrelated problem rows exactly, and
the randomized category index retains all 29 unrelated rows exactly. Each has
one TR-01 row, moved from open to retained/Lean verified. The manually inspected
generated-index diff changes only the corresponding counts: open targets
129→128, open 58→57, retained 88→89, Lean verified 1→2, randomized open 18→17.
Partial and solved counts are unchanged.

Added records are confined to the intended
`references/maintainer-review-2026-09-12-tr01/` audit directory. The canonical
documentation repairs preserve the original target and identify the exact
prescribed-width result, fixed orthonormal frame, immutable source, stale PDF
formalization disclosure, historical failed/recovered client check, and helper
build command. These are intentional documentation/audit additions.

This scope does not finalize hashes for the still-updating TR-01 audit records
or regenerated canonical PDF, and does not replace the separate kernel or PDF
reviews. Root already ran the catalog/ID validator and test suites; this review
adds an independent whole-tree preservation and resolution-union check without
rerunning them. No repository files were edited by this reviewer.

Machine evidence and reproducible read-only checker:
`pr141-integration-review.json` and `pr141-integration-check.py` in this audit
directory. The JSON contains all checks, changed/added path lists, counts,
target identity, anchor evidence, and the per-file base/current hash manifest.
