# SP-12 complete Target: independent actual Linux artifact review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
**PASS: all 40 actual-evidence checks, all 96 committed/current canonical project input hashes, and the exact project file set.** No canonical project input was edited for this audit.

The actual successful [Linux run 39142969327](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39142969327), [SP-12 job 117727133138](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39142969327/job/117727133138), and original `lean-SP-12` artifact ID `12143550920` bind immutable source commit `529e7b0560cef6461c98e950046860a160e6f86c`. The retained harness result is `comparator-accepted` with `lean_cert_proof_trust: kernel-checked`, for precisely `NLA.SP12.target`, no definition holes and only the three standard permitted axioms. It is the complete original PSD/SAP/chromatic Target, not a support gate or statement identity.

The checker matches all 96 harness input hashes to both this immutable committed project and the package at audit time, including the exact file set. It verifies the selected literal wrapper uses the closed shared proof, the published Target remains unchanged, and the exact Comparator config is the one recorded in the result. It verifies the pinned harness source lock/Forsythe revision, actual x86-64 Linux Lean4.33.1 compiler identity, and recorded checker/exporter/sandbox binary hashes. Independently generating the committed harness's proof-trust source reproduces its recorded hash, including actual theorem-kind and LeanCert kernel checks. The export's actual trust log reports exactly `propext`, `Classical.choice`, `Quot.sound`.

The retained raw logs show actual Comparator default-kernel acceptance and success; all three builtin-kernel control cases; all five Comparator regressions; actual restricted build/export writes; host loopback and AF_UNIX denial; absent effective capabilities and enabled no_new_privs; all four sandbox option rejections; and deliberate sorry/native axiom rejection. These are real completed Linux logs, not locally simulated markers or macOS substitutes.

The original downloaded zip SHA-256 is `d615a3d2fc8ee54391a10f1150415b8a41a2488b841868e06ae57d1be17589fb`. It matches both GitHub's artifact metadata digest and the actual raw job upload message. Every extracted member matches the original zip. Raw uncompressed job log SHA-256 is `e94e07bf8cede7b49b5b5f2f1bacc4920daee0d0018057c37f2ab43a88b48aee`. API metadata, original zip, raw/gzip job log, bootstrap and verification logs are retained under [verification/full-linux-ci/](verification/full-linux-ci/). All check outcomes and per-input/member hashes are retained in [verification/full-linux-artifact-check.json](verification/full-linux-artifact-check.json).

Reproduce from the repository root using the retained artifact:

```bash
python3 docs/lean/proofs/SP-12/verification/check-linux-artifact.py \
  --ref 529e7b0560cef6461c98e950046860a160e6f86c \
  --artifact docs/lean/proofs/SP-12/verification/full-linux-ci/artifact \
  --metadata docs/lean/proofs/SP-12/verification/full-linux-ci/run-metadata.json \
  --job-log-gz docs/lean/proofs/SP-12/verification/full-linux-ci/job.log.gz \
  --archive docs/lean/proofs/SP-12/verification/full-linux-ci/lean-SP-12.zip \
  --artifact-metadata docs/lean/proofs/SP-12/verification/full-linux-ci/artifact-metadata.json \
  --output docs/lean/proofs/SP-12/verification/full-linux-artifact-check.json
```

This audit independently reads actual CI evidence and source correspondence; it does not rerun Linux Comparator locally. Statement fidelity and mathematical reasoning are covered by the separate hash-bound preproof, support, analytic/full closure and canonical reviews. I authored no SP-12 source. I authored five unchanged historical SP-11 supports, independently reviewed by other agents; this artifact audit is not self-approval of their mathematics. Toolchain, pinned dependencies and checker trust remain the harness model recorded in the actual receipt. These are AI-agent checks, not external human peer review or source-author endorsement. Later package metadata changes require a separate fresh committed CI run and must not be relabeled as these 96 immutable input hashes.
