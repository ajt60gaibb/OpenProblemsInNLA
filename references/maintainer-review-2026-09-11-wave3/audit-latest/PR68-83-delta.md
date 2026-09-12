# PR68 / PR83 final-head delta review

**PASS for both exact heads below.** The previous mathematical reviews carry forward: no proof, original-source archive, witness argument, or original mathematical target changed. New material reconciles accepted upstream content, attribution/status text, and integration evidence.

Reviewed 2026-09-11:

| PR | Previously reviewed head | Current reviewed head |
|---|---|---|
| 68 | `2a1a0b39992bbd5654e7bdf9f869e21a6cee0d71` | `24ea75aa75b44b280c7aa0a342ea900f0fdd7be4` |
| 83 | `eadd702330dfdc56de30e429d4fb08340c66eafb` | `9b35b5e246989843cd67b2fed702216ea1f0acdb` |

Both current heads are exact two-parent merges of the respective reviewed head and published main `87366c62d3b5c47d170f747b1cb40ab38d501013`. Their old common base is `16369809e6e600144bd350ab70b7473b652f46f1`. The comparison isolated each PR's contribution paths instead of treating already reviewed upstream imports as new work. No main path outside those contribution sets was changed or deleted.

## PR68

The entire AA-01 full proof (Markdown, TeX, PDF), both original-manuscript archives, the discrepancy manuscript and PDF, the MD-03/04 solution notes, previous proof reviews, old document checks and network record are unchanged from the reviewed head. Both MD-03/04 canonical README/TeX/PDF sets are also unchanged. The Stepaniants submission README preserves its complete original bytes as a prefix and appends a dated integration link.

The new AA-01 canonical page retains Colbrook's accepted resolution notice **verbatim**, including both review links and the missing-experimental-source qualification. Stepaniants's original proof notice body is also retained verbatim under a separately named heading, with the correct Theorem 2.1/Corollary 7.1 attribution. The integration paragraph explicitly records the two submissions and links PR68 and accepted PR89. The full original problem statement and following reference/audit text remain byte-identical to the reviewed PR68 page. There is one permanent AA-01 ID, and its status remains Solved.

The new `verify_main_integration.py` was read in full before execution. It only reads files and runs read-only git object queries, checks fixed recorded hashes/bytes, validates the original README prefix, and checks link existence; it contains no network request, write operation, shell execution, or workflow action. It correctly labels itself a dated integration check rather than a mathematical proof checker. I ran it in a separate clone checked out at the exact current head; it passed.

I also independently checked the record against immutable git objects, rather than relying on the new verifier's PASS. All historical and current fingerprints agree, all **200 other incoming canonical pages** match accepted main, and all **1,260 incoming reference/proof/evidence blobs and modes** match main. The thirteen protected original files are unchanged; the fourteenth protected item is the preserved original prefix of the append-only submission README. The registry is byte-identical to both parents and contains all 203 IDs. Independently counted metadata gives **67 Open, 73 Partially resolved, 1 Solution claimed, 62 Solved**, matching this branch's record.

`RESOLVED.md` is an insertion-only extension of accepted main for the three Stepaniants submission records; no accepted resolution or attribution was removed. The two AA-01 mentions describe separately attributed submissions for the same canonical target and do not duplicate its catalog row or count.

Only the combined canonical AA-01 TeX/PDF changed among the mathematical presentation artifacts. Both PDF pages were rendered and visually inspected: both full attribution notices are visible, the original problem and references are present, and there is no clipping, overlap, or missing material. The unchanged full-proof PDFs retain their prior QA coverage.

## PR83

All six IE-15 canonical/solution files—README, canonical TeX/PDF, and solution Markdown/TeX/PDF—are **byte-identical** to the previously reviewed head. Its witness scripts, original agent draft, scalar-lemma proof, review record, and template are also unchanged. The solution therefore still addresses exactly the real nonsingular order-three/order-four rook-pivoting target, with all ties and intermediate active entries, and retains its prior proof/PDF review.

The obsolete present-tense Open statement in `references/colbrook-recovered-2026-09-11/README.md:22` is corrected: it now says the order-five witness alone left the target open and links the subsequent exact-growth resolution. The corresponding `RESOLVED.md` sentence is likewise historical and credits Stepaniants's later order-three/order-four result. The order-five lower bound 893/131, Colbrook attribution, witness links, and absence of a matching order-five upper bound are retained. No current-status contradiction remains in these notices.

The document-check JSON adds a later-integration object while preserving every pre-existing top-level value. I independently verified all six new SHA-256 assertions and their equality to the old head. The registry is unchanged with 203 IDs, and the recomputed totals **67 Open, 74 Partially resolved, 1 Solution claimed, 61 Solved** match the record. The only changes to accepted main's resolution prose are the added IE-15 solution section and the historical-status correction; the remaining sections are preserved.

## Evidence and integration limits

- `check_68_83_delta.py` independently verifies parentage, contribution-only changes, proof/source identity, registry preservation, all new recorded hashes, status totals, both original AA-01 notices, and the IE-15 status corrections.
- `PR68-83-delta-evidence.json` records its successful exact results and the genuine changed-path lists.
- `AA01-latest-1.png` and `AA01-latest-2.png` record the new canonical PDF inspection.

The submitted seventeen-test runtime logs are historical assertions; this delta review did not need another broad test-suite run because the safeguarded code is unchanged. The newly added verifier itself was inspected and rerun, and its preservation claims were separately checked as described above. Neither that verifier nor the manifests certify mathematical proofs or discovery priority.

Root subsequently integrated the updated heads locally at `5da9170`, retaining its already-QA'd combined AA-01 canonical presentation. A bounded read-only follow-up confirms all **15 PR68 proof/provenance paths** and all **12 PR83 proof/provenance paths** match the current source heads exactly, including the newly added records/script. The canonical AA-01 presentation and shared generated indexes may legitimately differ from the PR68 snapshot in that combined integration. Consequently the new verifier's dated `current_files` fingerprints describe its recorded PR68 tree, not every future combined-main tree; preserve the dated record rather than rewriting its historical hashes.

All work here was read-only on shared integration and remote state. Execution and PDF rendering occurred only in a separate temporary clone/output directory. No workflow approval/run, remote post, merge of the shared checkout, or push was performed.
