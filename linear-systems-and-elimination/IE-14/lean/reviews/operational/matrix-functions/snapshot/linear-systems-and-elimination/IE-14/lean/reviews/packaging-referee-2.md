# IE-14 packaging supplement — independent referee 2

**Verdict: PASS for the two packaging changes reviewed against `8708d191824d66bf8dccbbad60231708b81e32fa`.** No mathematical, proof, dependency or previously sealed review bytes changed. No Linux/Comparator success is claimed; the pending authoritative run must bind the later packaging revision.

**Reviewer:** OpenAI Codex AI agent `/root/existing_verification_audit`, independent non-implementing referee 2. This bounded supplement does not replace or modify the sealed statement or complete-source reviews.

## Exact changes and checks

Before adding this report/evidence, Git showed exactly one modified tracked file and one untracked new file:

- `reviews/initial/SHA256SUMS`: only the first pathname changed from `NUMERICAL_TARGETS.md` to `../../NUMERICAL_TARGETS.md`. All seven digest strings are unchanged. The old manifest is byte-identical in both reviewed base `8708d191824d66bf8dccbbad60231708b81e32fa` and original boundary `58b516b6dbb7fa4e885b679d261bf779c263aad4`.
- `reviews/initial/README.md`: accurately explains the former external preparation path, corrected project-relative location, unchanged contents and historical Git provenance. It is eligible for tracking and is not ignored; it was not yet committed at review time.

I independently resolved every pathname relative to its own manifest directory, normalized it, and verified that it stays inside the project and names a real file. All **99 payload references across six existing SHA256SUMS manifests** match their declared SHA-256, are already tracked, and match the exact Git blobs at `8708d191824d66bf8dccbbad60231708b81e32fa`. I also ran `shasum -a 256 -c SHA256SUMS` in each of those six directories; all checks passed, including all seven initial preparation entries.

All **23 candidate inputs** still match the complete-source seal and candidate Git revision `c04371f6005220866f4f069809002d319554e039`. All **ten pre-proof inputs** still match the boundary seal and boundary Git revision. Both statement reports and both final source reports are byte-identical to the reviewed base. This is a pathname repair for an existing exact dossier payload; no target or evidence payload was replaced.

| Reviewed packaging item | SHA-256 |
| --- | --- |
| Historical initial manifest | `11fd685f5f7f149796057fdf4084d64944d7bce635bd63f2a263dbcca3855457` |
| Corrected initial manifest | `ddc46893ee51d5ae708a54057a21edf0221e221b679c74a7e7311be8fa791997` |
| New initial provenance README | `fba8d38b10f9a2dee917df7632d2ba9987fa69928bf8d67501262ad69ae42eb0` |

The [independent audit](packaging-referee-2-evidence/audit.json) records all 99 normalized paths, their hashes and Git binding, both exact file changes, source preservation and earlier report hashes. The [check log](packaging-referee-2-evidence/checksum-checks.log) contains every successful checksum result. The audit script is retained; its initial two-file status assertion records the state before this supplement was added. [SHA256SUMS](packaging-referee-2-evidence/SHA256SUMS) seals these three evidence payloads. No core source or earlier report was edited by this reviewer.
