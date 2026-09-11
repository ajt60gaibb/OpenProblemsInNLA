# Independent maintainer review — second batch, 11 September 2026

Ten PRs update 41 distinct existing catalog entries. Full mathematical arguments,
original target statements and the applicability of cited primary results were
reviewed independently of the submissions' own PASS reports. Exact algebra and
certificate checks supplement those arguments. No blocking mathematical error
was found at the recorded heads, within the scopes below.

This is mathematical review by AI agents, with exact computational checks where
applicable. It is **not proof-assistant certification, external human peer review,
or exhaustive verification of novelty or historical priority**. Finite numerical
diagnostics alone were never used to justify a universal theorem.

## Decisions and scope

| PR | Detailed review | Supported scope |
| --- | --- | --- |
| [#40](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/40) | [Factorizations](audit-factor-frames/REPORT.md) | NM-03, NM-04, NR-04, PF-02, PF-05 solved; NR-03 and PF-01 partial. |
| [#47](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/47) | [Matrix functions](audit-functions-intervals/PR47-REVIEW.md) | MF-03, MF-16, SF-01 solved; MF-14/MF-15 partial; MF-18 auxiliary to its unresolved canonical target. |
| [#54](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/54) | [Frames](audit-factor-frames/REPORT.md) | FR-02, FR-09, FR-10, FR-11 partial; FR-04 remains Open. Only the four supplied FR-09 certificates are accepted. |
| [#62](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/62) | [Intervals and absolute values](audit-functions-intervals/PR62-REVIEW.md) | AV-01, AV-02, IV-02 through IV-06 solved; complexity classifications retain their P=NP qualification. |
| [#64](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/64) | [MD-06](audit-root/PR-64.md) | Negative resolution in the uniform simple cubic graph model. |
| [#68](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/68) | [AA-01, MD-03, MD-04](audit-root/PR-68.md) | Three canonical targets supported; no efficient-algorithm claim; discrepancy theorem authorship retained. |
| [#78](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/78) | [Elimination](audit-elimination/PR78-audit.md) | Eight resolutions: IE-13, IE-14, IE-17, IE-18, IE-19, IE-21, IE-22, IE-23. IE-17 uses the catalog's spectral perturbation norm; IE-18 is a finite-step result. IE-15 order-five evidence alone leaves its target open. |
| [#81](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/81) | [Krylov and sign matrices](audit-root/PR-81.md) | IE-10 solved; IS-04 prime-square family remains partial. |
| [#83](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/83) | [Rook pivoting](audit-elimination/PR83-audit.md) and [current revision](audit-elimination/PR83-delta-a7afa4d.md) | Exact order-three/order-four growth 3 and 14/3. Preserve the separately attributed order-five evidence from #78. |
| [#85](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/85) | [MI-28](audit-root/PR-85.md) | Full positive-definite determinant target, k>=0 and 0<=p<=2. |

## Integration and permanent numbering

This integration contains PRs #40, #47, #54, #62, #64, #78 and #81. Their reviewed
heads are preserved as ancestors through ordinary merge commits. Shared indexes
were regenerated and independent resolution/source records combined. Renderer
changes were reconciled without removing existing published behavior.

PRs #68, #83 and #85 remain outside this integration while their required GitHub
Actions runs await explicit execution approval. A mathematical PASS is not a
substitute for a required repository check. Their pending status does not alter
current canonical statuses. In particular, IE-15 remains Open until #83 is
integrated; the order-five supplementary example alone does not settle it.

All **203 published IDs**, canonical paths, and original mathematical targets
are preserved. No new ID is assigned, no historical gap filled, and no solved
entry removed. The seven-PR integration adds 25 solved entries: 48 solved,
154 open or partially resolved, and one claimed solution, out of 203 retained
entries. The append-only registry and required numbering workflow are unchanged.
All 17 permanent-ID regression checks passed against published main.

The user's separate uncommitted research additions were not included or modified.

## Evidence

- [Reviewed head and changed-source SHA-256 manifest](reviewed-source-sha256.json).
- [Integration commits](integration.jsonl) and [independent integration audit](audit-elimination/integration-audit.md): all 566 nonshared contributed files preserve their reviewed blobs and modes.
- Per-review directories contain fresh independent check sources and their saved
  outputs, inspected submitted-certificate results, and source/PDF QA records.
- At the initially frozen heads, all 78 final PDFs / 250 pages were inspected.
  All six proof pages of the later PR #83 contact-redaction revision were also
  checked, with no change to mathematical content.

The reports record exact proof scope, endpoint cases, external dependencies,
source-access limitations, and the distinction between analytic arguments,
exact certificates and supplementary numerical diagnostics. Local runtime and
snapshot paths in archived reports identify the original audit environment;
transient page images and build trees are kept in the local review archive.
