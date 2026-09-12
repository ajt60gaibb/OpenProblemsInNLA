# Independent six-PR integration preservation review

Date: 12 September 2026. Reviewer: independent Codex agent `audit_tr03`, separate from the integrating agent. Read-only review of the committed integration tree; no source, index, or Git state was changed by this review.

**Verdict: PASS. No integration blocker or lost submission/publication content found.** This review checks preservation and consistency of the combined tree; the separate mathematical and formal-evidence audits remain the proof-review records. Current combined CI and any later audit-document commit are separate from this snapshot.

Reviewed integration commit: `ed179ae3b431a861852508243cb5b37a256c4b0f`.
Published base: `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.
Repository: `/private/tmp/nla-sept12-audit.JfqvTr/repo`.

## Complete submission preservation and ancestry

I compared Git directory-tree object IDs, rather than only changed filenames. Every entire canonical problem directory, including the unchanged historical materials, proof sources, PDFs, Lean projects, receipts, and nested evidence archives, is exactly identical to the corresponding reviewed PR head. All six heads are ancestors of the integration commit.

| PR | Entry | Reviewed PR head | Files in exact matching directory | Ancestry |
| --- | --- | --- | ---: | --- |
| 160 | MI-29 | `cb277ec818a42a077635ce56ababc96b575aaeb8` | 175 | PASS |
| 162 | TR-07 | `fb1e11fbd4323c3d3a073ed1ada53eb60817f7d5` | 6 | PASS |
| 164 | TR-03 | `311a0ce626e3cdf25f6000834d90969799ac4394` | 3 | PASS |
| 165 | MI-21 | `eeb4b8b905ec78b3ee892c292eca330272a34cfc` | 163 | PASS |
| 166 | MI-07 | `1dff432524c4dfb4ccd272c906ab7c701855a420` | 218 | PASS |
| 167 | MI-06 | `cdf6e1c75c29363bd04f1b13beaa6ba679a698bb` | 203 | PASS |

The complete `references/holden-tr03-2026-09-12` directory (7 files) exactly matches PR164, and `references/holden-tr07-2026-09-12` (8 files) exactly matches PR162. Thus 783 files across the eight relevant directory trees retain their submitted byte contents and modes. In particular, integration did not alter any reviewed proof or PDF, so their individual mathematical and visual audits still apply to this commit.

There are 776 changed paths relative to the published base. Every one lies inside those eight exact-match directories or one of these five intended shared files:

- `CATALOG.md`
- `README.md`
- `RESOLVED.md`
- `matrix-inequalities-and-norms/README.md`
- `randomized-and-low-rank-approximation/README.md`

There are no unexpected changed or deleted paths. All prior-main files outside those scopes, including all other canonical entries, earlier Lean verifications, shared checker/workflows, renderer, policies, and numbering safeguards, are preserved. `problem_ids.json` has the identical blob object as the base: all 217 ID/path pairs are unchanged.

Machine-readable evidence: `integration-preservation-checks.json` in the same report directory.

## Resolution archive conflict reconciliation

I inspected the complete `RESOLVED.md` diff and compared paragraph content from the base and all six submitted heads. After normalizing whitespace, all **209 preexisting nonheading paragraphs** remain present. Every new nonheading resolution paragraph from all six PRs is also present: one each for PR160, PR164, PR165, PR166, and PR167, and three for PR162. No old mathematical result, credit, source link, or verification paragraph was lost through conflict resolution.

The archive's problem-heading count rises from 76 to 78 by adding TR-03 and TR-07. Every previous resolution ID remains. The two IDs with repeated historical headings, MI-08 and FR-12, each already appeared twice in the published base and still appear twice; integration introduces no new duplication.

The MI-06 and MI-07 headings retain both Matthew J. Colbrook's mathematical credit and George Stepaniants's formalization credit. Their old informal result paragraphs survive alongside the new formal evidence and the limits of its scope. MI-21 and MI-29 likewise retain prior mathematical attribution and their new formalization evidence. TR-07's full resolution survives the subsequent TR-03 merge. TR-03's entry accurately remains a partial result.

Machine-readable evidence: `integration-resolution-checks.json`.

## Catalog counts and generated-file reproduction

I independently read the Status field of all 217 registered canonical READMEs at the integration commit. The only changes from the base are:

- MI-06, MI-07, MI-21, MI-29: Solved to Lean verified.
- TR-03: Open to Partially resolved.
- TR-07: Partially resolved to Solved.

The resulting counts are exactly **10 Lean verified, 80 Solved, 56 Open, 71 Partially resolved**. Hence the correct totals are **127 open targets** and **90 other retained entries**, still 217 permanent entries overall. The randomized/low-rank category correctly falls from 17 to 16 open targets. The four MI promotions do not affect the open-target count.

I then invoked the unchanged catalog generator with all `Path.write_text` calls intercepted in memory. This runs its published-base ID validation and derives the actual expected outputs without writing to the root worktree. All **13 generated files** match the integration commit exactly, including all category indexes, CATALOG, and README. No omitted or stale generated count was found.

Machine-readable evidence: `integration-index-checks.json`.

## Available audit and test-record consistency

Read the completed `pr162.md`, `pr164.md`, and coordinating `pr166-pr167.md` reports available during this check. Their reviewed hashes, stated mathematical statuses, distinctions between proof authorship and formalization, and preservation requirements agree with the integrated tree. Their stated complete-directory preservation condition is now independently verified here. Reports for PR160/PR165 and the final combined CI receipt were not yet available when this snapshot review was written; this report does not claim to have reviewed those pending documents.

Read the existing root integration logs: permanent-ID suite **17 tests PASS**; general suite **68 tests PASS with one skipped class requiring Pandoc**; checker harness suite **12 tests PASS**. The local general-suite log should not be described as an unqualified run of every rendering test; CI or a configured Pandoc execution can supply that coverage. No contradiction with the source-preservation findings arises, and the renderer itself is unchanged.

This reviewer did not rerun Lean locally, re-review the other agents' entire mathematical proofs, or treat preserved submitted PASS reports as new mathematical evidence. Individual proof audits and authenticated Linux evidence support those decisions separately. No public comments, merge, push, issue mutation, or root-worktree write was performed.
