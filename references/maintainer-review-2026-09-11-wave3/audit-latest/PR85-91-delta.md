# PR85 / PR91: final updated-head review

**PASS: the prior full mathematical reviews and PDF reviews carry to both exact latest heads.** No theorem, proof, canonical target, proof source or PDF changed in these updates. The integration records are accurate and appropriately limited to preservation checks. No blocking or corrective finding remains.

| PR | Earlier reviewed head | Latest reviewed head | Accepted incoming main |
|---|---|---|---|
| 85, MI-28 | `58a65609730306db4004352ccbdb5d8273ca2ff4` | `1f9a8bbd7cce9ae429fd7fd17ff409da751c414d` | `87366c62d3b5c47d170f747b1cb40ab38d501013` |
| 91, MI-24 | `cc5ed78e4ca055f15717e5130f69bff6097d9406` | `5d5f2a32a17c0ed7bb9fdfc976ab7af44c19dd4f` | `87366c62d3b5c47d170f747b1cb40ab38d501013` |

Each latest commit has precisely the corresponding earlier reviewed head as first parent and accepted main as second parent. These are ordinary merges, with no replacement of the reviewed histories.

## Isolated changes

Each first-parent diff has 598 paths because it imports accepted main. Comparing the complete Git trees against both parents isolates only seven files whose contents differ from both: the three shared files `README.md`, `CATALOG.md`, `RESOLVED.md`; the submission-record README; and three new integration files (Markdown, JSON and Python). No unrelated change is hidden among the incoming files. The category index takes the correct merge of canonical statuses and reproduces through index generation.

The entire prior submission README is an unchanged prefix, followed by the dated integration paragraph. The resolution list is exactly accepted main with the corresponding earlier reviewed author/result section inserted intact. Thus the upstream randomly pivoted, joint-spectral-radius and tensor result sections, as well as previous authors' attribution, are preserved.

## Proof, target and document preservation

For each PR, all six files in its own canonical directory are byte-identical to the earlier reviewed head: `README.md`, `problem.tex`, `problem.pdf`, `solution.md`, `solution.tex`, and `solution.pdf`. The full original problem-statement suffix also matches accepted main. Therefore MI-28 retains the full positive-definite determinant target for all k>=0 and 0<=p<=2, and MI-24 retains the complex positive-definite Schatten target for all 1<=p<=infinity. Existing hypotheses, attribution, finite-computation limitations and proof-review disclosures remain unchanged.

The previous detailed mathematical reviews remain the basis for those full-scope conclusions: `audit-root/PR-85.md` plus its intervening reviewed deltas, and `audit-root/PR-91.md`. This final audit checks their applicability to the exact new bytes; it does not pretend to be a new proof discovery or formal proof-assistant verification.

All four final PDFs and their corresponding sources are identical, so their earlier complete source/PDF and visual QA remains applicable without rerendering unchanged documents. The exact PDF/source SHA-256 hashes are recorded in `PR85-91-delta-evidence.json`.

For each branch, all **606** other canonical README/TeX/PDF files are byte-identical to accepted main. All **1,260** incoming reference/proof/evidence blobs also match accepted main. The permanent registry is byte-identical to both parents, with all **203** ID/path mappings preserved. No existing target is replaced, compacted, renumbered or recycled.

## Integration-record and program audit

Both complete new `verify_main_integration.py` scripts were read before execution. They perform read-only file/hash comparisons and Git reads; they do not post, push, fetch, rewrite history or regenerate artifacts. Their path calculation and recorded-parent selection are correct. The manifests distinguish historical fingerprints from current integration fingerprints rather than claiming old hashes describe new content.

Independent checks verify every historical hash against the recorded earlier parent, every current hash and byte count against the exact latest head, the preserved README prefixes, parent identities, the 202 other canonical README count, the 1,260 incoming evidence count, and the original target. The protected-file counts include the README whose original prefix is retained, so the separate nine/six unchanged-artifact counts are consistent. Generic AA-01 fields are false/not regenerated here and do not assert a new AA-01 review or altered attribution.

The prose expressly calls this an integration check, not a fresh mathematical review. No new visual-inspection claim is made for unchanged PDFs. The earlier document-check manifests are retained as historical evidence. The current complete catalog metadata on either individual branch is Open=68, Partially resolved=73, Solution claimed=1, Solved=61, summing to 203 and matching its record.

## Reproduction

`check_PR85_91_delta.py` independently compares complete trees and recorded hashes, including stronger checks of all three canonical artifact types. Its successful results are in `PR85-91-delta-evidence.json`.

In a separate scratch clone, both submitted integration checkers were rerun successfully. Both branches pass permanent-ID validation against the accepted incoming commit and all 17 numbering tests. Regenerating each catalog produces no working-tree diff. Logs are retained alongside this report. The coordinating review already reports successful required CI at the two latest heads; this delta report makes no separate live-CI polling claim.

No shared integration clone, remote branch, PR comment or GitHub state was changed. The only working-tree changes occurred in the isolated scratch clone used for reproducibility checks.
