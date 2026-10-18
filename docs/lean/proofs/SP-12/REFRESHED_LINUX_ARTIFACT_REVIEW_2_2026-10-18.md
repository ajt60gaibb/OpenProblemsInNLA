# SP-12 promoted package: independent refreshed Linux artifact review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
**PASS: all 40 actual-artifact checks and all 96 committed/current project input hashes, with the exact file set.** No canonical project input was edited for this audit.

The actual successful [push run 39149417211](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39149417211), [SP-12 job 117739903353](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39149417211/job/117739903353), and original `lean-SP-12` artifact ID `12143944681` bind immutable promoted commit `a7adfc8e30ad284f42ec2ea0221a990ee9804031`. The real full-Target Comparator/default-kernel and generated theorem-kind/LeanCert kernel consumer pass for exactly `NLA.SP12.target`, with no definition holes and only `propext`, `Classical.choice`, `Quot.sound`.

The retained original zip SHA-256 is `b0727fbe155790ef58328831a7630e121b8450c3fd91daaaf662fd4b7a20841f`, matching both official GitHub metadata and the real job upload log. Every extracted member matches the zip. The uncompressed raw job log SHA-256 is `088da3f43dde65268c33ab1b5fb2755f4b3276d346aace143d2e964c0a8c69d5`. Actual artifact, original archive, raw/gzip job log and API metadata are retained separately under [verification/refreshed-linux-ci/](verification/refreshed-linux-ci/), with full per-file checks in [verification/refreshed-linux-artifact-check.json](verification/refreshed-linux-artifact-check.json).

The actual controls and real sandbox evidence pass: all three builtin-kernel cases, all five Comparator regressions, designated build writes and restricted export writes, denied host loopback and AF_UNIX, absent capabilities, no_new_privs, four invalid sandbox-option rejections and deliberate sorry/native axiom rejections. Pinned checker source lock, Forsythe revision, Linux toolchain/compiler and recorded binary identities match the actual result. Independently regenerating the committed kernel consumer reproduces its source hash.

The [two-run source comparison](verification/refreshed-proof-identity.json) confirms the same 96 paths and all 55 Lean source hashes identical to the first accepted package. Only `README.md` and `formalization.yaml` differ. This refreshed acceptance therefore checks the real promoted descriptive inputs rather than relabeling the first run's hashes. The original 529e7b0 receipt/artifact and historical exact-boundary/proof evidence remain retained.

Reproduce from the repository root:

```bash
python3 docs/lean/proofs/SP-12/verification/check-linux-artifact.py \
  --ref a7adfc8e30ad284f42ec2ea0221a990ee9804031 \
  --artifact docs/lean/proofs/SP-12/verification/refreshed-linux-ci/artifact \
  --metadata docs/lean/proofs/SP-12/verification/refreshed-linux-ci/run-metadata.json \
  --job-log-gz docs/lean/proofs/SP-12/verification/refreshed-linux-ci/job.log.gz \
  --archive docs/lean/proofs/SP-12/verification/refreshed-linux-ci/lean-SP-12.zip \
  --artifact-metadata docs/lean/proofs/SP-12/verification/refreshed-linux-ci/artifact-metadata.json \
  --output docs/lean/proofs/SP-12/verification/refreshed-linux-artifact-check.json
```

This independent audit reads genuine completed Linux evidence; it does not claim a local rerun of the Linux tools. Mathematical fidelity and preservation are covered by the separate source, boundary and promotion reviews. I authored no SP-12 proof or project source. Five historical SP-11 prerequisite supports are my work and independently reviewed by other agents; this evidence audit is not independent self-review of their mathematics. These are AI-agent checks, not external human peer review or source-author endorsement.
