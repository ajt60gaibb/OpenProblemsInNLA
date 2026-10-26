# TR-06 actual exact-push Linux approval

Independent verifier `/root/recover_verification` (Codex AI agent; no TR-06 proof sources authored), 23 October 2026. **PASS: 45/45 strict controls on the actual completed push run**, exact source `2b049df5e9b15318987f3fa592b1a7c65a0c0057`.

[Lean verification run 40035041685](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40035041685), [TR-06 job 120692462037](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40035041685/job/120692462037), artifact `12536268648`. The original ZIP SHA-256 is `dd0693b83140e3dbb5abf607ae072bd96c00ef33eb82148d970fa56b55a614e3`, matching both GitHub metadata and the actual upload log. Exact extraction, raw job log, metadata and all fifteen artifact files are retained here. This is the actual push commit, distinct from the PR synthetic merge.

The receipt accepts exactly 153 committed/current canonical inputs, including 144 Lean files, 140 exact copies (80 completion proof sources, 58 unchanged published sources and two statement sources), and eleven selected theorem exports. Every Linux input hash equals the separately frozen canonical-audit lock. The original ten declarations and literal intrinsic `NLA.TR06.target` pass actual theorem-kind and LeanCert kernel checks, each with exactly `propext`, `Classical.choice`, and `Quot.sound`. The actual Comparator default kernel accepts the solution. Sandbox controls, three kernel regressions, five Comparator regressions, and both sorry/native negative fixtures pass. All ten actual dependency checkout revisions equal the committed manifest pins.

`independent-review-2026-10-23.json` is the complete machine-readable strict45 replay. `INDEPENDENT_LINUX_APPROVAL_2026-10-23.json` binds that result to the separate full80 shared and canonical144 fresh local approvals, the original source locks and raw receipt files. The canonical local audit rebuilt all144 files, checked 772 declarations and545 theorem kinds, and actually rejected all11 Challenge placeholders. These placeholders are specifications, never accepted proofs.

To reproduce the retained-artifact audit from the repository root:

```sh
python3 docs/lean/proofs/TR-06/verification/check-linux-artifact.py \
  --ref 2b049df5e9b15318987f3fa592b1a7c65a0c0057 \
  --artifact docs/lean/proofs/TR-06/verification/linux-ci/2b049df5/artifact \
  --metadata docs/lean/proofs/TR-06/verification/linux-ci/2b049df5/run-view.json \
  --job-log-gz docs/lean/proofs/TR-06/verification/linux-ci/2b049df5/job-120692462037.log.gz \
  --archive docs/lean/proofs/TR-06/verification/linux-ci/2b049df5/artifact-12536268648.zip \
  --artifact-metadata docs/lean/proofs/TR-06/verification/linux-ci/2b049df5/artifact-12536268648.json \
  --output /tmp/tr06-independent-linux-replay.json \
  --reviewer 'Independent retained-artifact replay'
```

This replay reads the actual retained Linux evidence; it does not rerun Comparator locally. It also requires current canonical inputs to match the exact receipt commit. Later descriptive package promotion needs separately scoped exact-input evidence. The earlier accidental tracked-cache failure remains honestly retained in `../8b714e1c/`; the harness guard was preserved. No ID, original target, proof source or canonical package file was changed by this verification.
