# Independent preservation review of the seven-PR integration

**Verdict: PASS. No integration-preservation blocker found.**

Frozen integration audited: `17a797f6cbb8809f869296f1c850f378f9d3ac5d`.
Published base: `5830ed4fb06da0659414a3deb2a40ad327aca052`.
Read-only checkout: `/private/tmp/nla-integration-186-193`.
Date: 12 September 2026.

This audit reads immutable Git objects at the stated commits. Later additions of review records are outside this frozen code/content comparison. No checkout files, Git state, source, generated index, or GitHub object were changed; no test, Lean build, CI job, or repository regeneration was rerun.

## Exact authored-file preservation and ancestry

For each reviewed PR head, I obtained the complete recursive Git tree and compared every path changed from the published base against the integrated tree. The comparison uses the full `(mode, object type, blob ID)` tuple. Only the deliberately combined root/category indexes and `RESOLVED.md` were excluded from literal per-head equality; those received separate checks below. No authored README, proof, definition, export, certificate, PDF, archived source, evidence, or executable script was exempted.

| PR | Reviewed head | Authored paths compared | Mismatches | Head is ancestor |
| --- | --- | ---: | ---: | --- |
| 186 | `fc83d2959723c92967a26777e5238404804c848c` | 77 | 0 | Yes |
| 187 | `94e8ae24e4c10e79d8b3502101ee4a0287506f81` | 545 | 0 | Yes |
| 189 | `5d79588e225376c81f1a664f3ec128a482bf7103` | 42 | 0 | Yes |
| 190 | `43754370fadf404837fc2330b9cdf55ffd92fc1c` | 26 | 0 | Yes |
| 191 | `e15ce4854d1a9c9fa457b93da78fca04febf200a` | 29 | 0 | Yes |
| 192 | `3fc8bde9c014d22575bbfb73c644c5ce0c492d29` | 572 | 0 | Yes |
| 193 | `f73edd6c6562a78d1c4f56fdc4c1c75dac9ace4a` | 599 | 0 | Yes |

All **1,890 distinct authored paths** match their respective reviewed heads exactly, including executable modes. The author changes have no overlapping path requiring incompatible content. Every integrated change is explained by those authored paths or the explicitly combined index/resolution files; there are no unexplained source changes.

## Published identity and shared infrastructure

All **6,974 base tracked paths remain present** among the integration's 8,834 paths. `problem_ids.json` is byte-for-byte and mode-identical to the base, containing the same **217 ID/path pairs**, and all 217 canonical README paths exist. No ID, canonical path, or existing published file was removed.

The 80 tracked paths under the shared `tools/`, `.github/`, and `docs/lean/` trees, together with root `AGENTS.md`, are unchanged in mode, type, and blob identity. This includes shared harness code and workflows. The integration therefore preserves the shared checking safeguards and does not alter the code under which the individual proof evidence was reviewed.

## Resolution archive and credits

I compared every nonblank line added to `RESOLVED.md` by each PR against the integrated archive, including line multiplicities. All **19 added nonblank lines** survive exactly. I also checked all **419 nonblank base lines retained by every PR head**; none is missing from the integration.

A direct reading of the combined resolution diff confirms the conflicting top insertions were combined without losing the RA-14 and TR-14 sections. The matrix partial-results section and the RA-04 partial-results record are present. The MI-03, IE-23, and IV-06 formal-verification additions preserve the distinct credits for Colbrook's mathematics, Stepaniants's formalization, and the original source authors. Holden's mathematical authorship, affiliation wording, retained-source credit, partial-result boundaries, and explicit informal-review scope remain as reviewed. No result was promoted to a broader proof or verification scope by combining the archive.

## Combined indexes and status counts

I independently read the status from every canonical registered README, then compared the resulting IDs, paths, and status labels with all 217 catalog rows and all 217 category-index rows across 11 categories. Every registered ID appears exactly once in the catalog and once in its category; no ID is missing or duplicated. Category open/retained grouping, each category's summary count, and all root category counts agree with those canonical statuses.

| Status | Integrated count |
| --- | ---: |
| Lean verified | 19 |
| Solved | 74 |
| Open | 51 |
| Partially resolved | 73 |
| Total retained canonical entries | 217 |

The open-target count is **51 + 73 = 124**; the other retained entries total **19 + 74 = 93**. Both root and catalog summaries give those exact totals.

Only the intended status transitions occurred: MI-03, IE-23, and IV-06 move from Solved to Lean verified; MI-16 and RA-04 move from Open to Partially resolved; TR-14 moves from Partially resolved to Solved. All other canonical statuses remain unchanged.

## Reproducibility and limit

The compact machine-readable result is `/private/tmp/nla-prs186-193-integration-review.json`. The independent read-only inspection scripts are `/private/tmp/nla-integration-preservation-check.py` and `/private/tmp/nla-integration-index-check.py`.

This is an integration preservation audit, not a new mathematical referee report or a substitute for CI. Exact equality with the reviewed author heads preserves the scope of their prior individual reviews. The conclusion applies to the frozen integration commit named above.
