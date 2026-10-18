# SP-11 refreshed promotion: independent actual Linux artifact review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
**PASS: all 40 actual-artifact/source correspondence checks, covering all 135 canonical project inputs.**

The actual successful [Linux workflow run 39140854908](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39140854908), [SP-11 job 117714897072](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39140854908/job/117714897072), and original `lean-SP-11` artifact ID `12141672724` bind immutable source commit `9c1f62be980d174b9418285d2e54fb9deae3a5bc`. This run checks the promoted package metadata and documentation as committed after merging published main. It does not reuse the earlier 9264361 input hashes. All 135 inputs and the exact file set match both this recorded commit and the current canonical package at audit time.

The harness accepted the full unchanged `NLA.SP11.target` with no definition holes. The actual default Lean kernel and generated theorem-kind/LeanCert kernel consumer passed; the full export depends only on `propext`, `Classical.choice`, and `Quot.sound`. All three builtin-kernel cases, all five Comparator regressions, real build/export sandbox restrictions and negative option cases, and deliberate sorry/native axiom rejections passed. The source lock, Forsythe checker pin, toolchain/compiler and recorded sandbox/checker binary identities match the actual result. The independently regenerated consumer matches the recorded source hash.

The original zip SHA-256 is `2dbbcc28fd12ea1978ca5bf0bcdebfe56ed209b694c289ec8f78c4e9be21ee37`, matching both GitHub's artifact digest and the raw upload log. Every extracted archive member matches the retained original zip. The raw uncompressed job log SHA-256 is `25d6f8a59671f8704c6111f49cf0f1120cbf9e760eee0e192e0cc38421e1d27a`. Complete per-file hashes, all check outcomes and source correspondence are in [sp11-refreshed-linux-artifact-check.json](sp11-refreshed-linux-artifact-check.json); actual artifact, original zip, raw/gzip job log and API metadata are in [sp11-refreshed-linux-ci/](sp11-refreshed-linux-ci/).

Reproduce from the repository root after downloading the retained inputs:

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-full-linux-artifact.py   --ref 9c1f62be980d174b9418285d2e54fb9deae3a5bc   --artifact docs/lean/campaign-2026-10-17/verification/sp11-refreshed-linux-ci/artifact   --metadata docs/lean/campaign-2026-10-17/verification/sp11-refreshed-linux-ci/run-metadata.json   --job-log-gz docs/lean/campaign-2026-10-17/verification/sp11-refreshed-linux-ci/job.log.gz   --archive docs/lean/campaign-2026-10-17/verification/sp11-refreshed-linux-ci/lean-SP-11.zip   --artifact-metadata docs/lean/campaign-2026-10-17/verification/sp11-refreshed-linux-ci/artifact-metadata.json   --output docs/lean/campaign-2026-10-17/verification/sp11-refreshed-linux-artifact-check.json
```

This independent review reads genuine completed CI evidence; it does not claim a local rerun of the Linux checker, nor replace the separate exact-statement and mathematical source reviews. I authored five historical SP-11 support modules; their independent semantic reviews are by other agents. This artifact review does not claim independent self-review or external human peer review. The original 9264361 receipt and artifact remain unchanged.
