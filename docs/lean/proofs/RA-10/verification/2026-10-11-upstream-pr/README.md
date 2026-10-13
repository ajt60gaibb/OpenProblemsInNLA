# RA-10 upstream submission: local verification

Date: 2026-10-11. Environment: macOS (`Darwin arm64`).
Branch: `codex/ra10-complete-upstream`.
Upstream base: `696b59ff414c74d24bfef71ab22e6d67b5c0f7cd`,
`codex/nla-proof-ra10` (PR #350).

The two completion commits from fork PR #2 were applied to the dedicated
upstream RA-10 branch. All 97 proof source files in that fork PR remain byte
identical. The upstream base adds `RidgeCompressionDefectSupport.lean` and
`RidgeCompressionEq7Scalar.lean`; neither is in the final theorem's import
closure. There are 99 RA-10 proof modules in this submission tree.

From `lean-statements/`:

```bash
lake build NLA.Proofs.RA10.OperatorMonotoneRepresentation NLA.Proofs.RA10.OperatorMonotoneConcavity
shasum -a 256 -c ../docs/lean/proofs/RA-10/verification/2026-10-11-upstream-pr/source-sha256.txt
```

The incremental local build passed (3044 jobs); `build.log` retains its output,
including the final representation, transfer-bound and target axiom reports.
Those declarations depend only on `propext`, `Classical.choice` and `Quot.sound`.
`source-sha256.txt` records 104 files: all 99 RA-10 proof modules, the live and
reviewed RA-10 statement files, and the three dependency/toolchain files.

The final declaration remains `NLA.Proofs.RA10.ra10_target`, proving the
unchanged `NLA.Statements.RA10.Target` with constant 11. No source admission,
custom axiom or external dependency was introduced. The canonical README,
frozen statement and permanent IDs remain unchanged.

This is a local build receipt, not independent proof review or isolated Linux
Comparator verification. Both remain outstanding, including the proof-target
Comparator setup. The CI build step for the candidate modules does not replace
those checks; existing Comparator statement identities do not prove RA-10.

Earlier verification directories describe the original development baseline
and intermediate proof stages. They remain historical records, not additional
approvals of the upstream submission.
