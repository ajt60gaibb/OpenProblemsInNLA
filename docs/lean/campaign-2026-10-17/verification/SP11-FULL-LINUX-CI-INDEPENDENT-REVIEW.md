# SP-11 complete Target — independent actual Linux CI audit

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
**Verdict: PASS — 40 checks; all 135 committed project inputs match.**

I independently downloaded and inspected the actual successful
[Linux run 39131755109](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39131755109),
[SP-11 job 117688269984](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39131755109/job/117688269984),
and artifact `lean-SP-11`, ID `12138590670`. The workflow and job both succeeded
for commit `9264361fafb89b37b5c48236afebb304bc84110a`. The harness result records
that same source commit and canonical project
`eigenvalues-and-inverse-problems/SP-11/lean`.

The actual Comparator selection is exactly `NLA.SP11.target` from Solution,
with no definition holes and only `propext`, `Classical.choice`, `Quot.sound`
permitted. The live Target is byte-identical to the published frozen all-graph
statement, and Solution directly exports the complete copied shared proof.
The result is `comparator-accepted`, with `lean_cert_proof_trust` equal to
`kernel-checked`. The Comparator log records its default kernel accepting
the solution and `Your solution is okay!`. The generated independent trust
consumer is reproducible from the committed harness, requires a theorem
constant, and checks the actual selected export in kernel mode. Its logged
transitive axioms are exactly the three permitted foundational axioms.

All **135 project input hashes**, including proof sources, statements,
configuration, reviews and metadata, match both the recorded commit and the
current package at audit time. The complete recorded/current tracked file set
also matches, not merely the main Lean file. The verifier's source-lock hash
is `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`,
binding Forsythe commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`.
The receipt identifies Lean 4.33.1, compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, on actual x86-64 Linux, with
recorded Comparator, exporter and Landrun executable hashes.

The retained logs demonstrate the real strict Linux sandbox: build writes
are limited to `.lake`, export writes are denied, host loopback is unreachable,
AF_UNIX creation is denied, namespaces are private, effective capabilities are
absent and `no_new_privs` is set. All four malformed/widened sandbox-option
cases are rejected and outer/export fixtures remain unchanged. All three
builtin-kernel controls and five Comparator regressions pass. Deliberate
`sorryAx` and native proof axioms are rejected with expected nonzero exits.
The actual selected-target Comparator and trust commands run through the
recorded strict sandbox wrapper and user service.

I also downloaded the original artifact zip independently of its extracted
files. Its SHA-256 agrees with GitHub artifact metadata and the digest in the
actual job upload log; every extracted file equals the corresponding archive
member. This binds the retained evidence to the successful job rather than a
locally recreated log.

| Artifact file | SHA-256 |
| --- | --- |
| `result.json` | `993f80bcc3aa4eb17aef9006ffe8f1caf7dd23ac48b460a268ffbc40e18d2db4` |
| `comparator.log` | `a2975694f49d8bab169e9496ce5a66805597ce0bb34c2c01eeafc40ce6ce69b4` |
| `leancert-proof-trust.log` | `c0474d6c78d3d4522ae1128a620a216a5ca4c52b27cd90141bc82ca4db3b4681` |
| `sandbox.log` | `cad1dbe8aa97047459b2d140a811440c571ff34295c9222510df7d2a425a5980` |
| original artifact zip | `bf81f1df753ac7710f63e984c282982cb07ac0d7f2b39bae3a19ae9ca1530e0a` |
| uncompressed raw job log | `35312cb0ad0b657c24fba2a85e21c5d6e389c27994735de2ea332fb9b6316e08` |

The first four files are under artifact directory
`verify-20261018T133100Z-4187/`. All archive files, their digests, exact input
records, GitHub metadata and compressed/raw job log are retained in
`sp11-full-linux-ci/`; the machine-readable audit is
`sp11-full-linux-artifact-check.json`.

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-full-linux-artifact.py \
  --artifact docs/lean/campaign-2026-10-17/verification/sp11-full-linux-ci/artifact \
  --metadata docs/lean/campaign-2026-10-17/verification/sp11-full-linux-ci/run-metadata.json \
  --job-log-gz docs/lean/campaign-2026-10-17/verification/sp11-full-linux-ci/job.log.gz \
  --archive docs/lean/campaign-2026-10-17/verification/sp11-full-linux-ci/lean-SP-11.zip \
  --artifact-metadata docs/lean/campaign-2026-10-17/verification/sp11-full-linux-ci/artifact-metadata.json \
  --output docs/lean/campaign-2026-10-17/verification/sp11-full-linux-artifact-check.json
```

The retained first audit attempt passed all source/proof/control checks but
expected a human-readable GitHub step label; this CLI emitted `UNKNOWN STEP`.
The corrected check instead requires the actual successful artifact-upload
message and additionally verifies the archive digest. `attempt-1-audit.json`
preserves that checker-only mismatch; there was no CI or proof failure.

This audit did not rerun Linux locally or independently rebuild its tools.
It verifies the downloaded actual run under the pinned harness/toolchain/cache
trust model. Semantic fidelity is supplied separately by hash-bound statement
and full-proof reviews. This complete-target receipt is distinct from the
earlier seven-module support/statement-identity run. Future changes to project
inputs need fresh verification; the recorded commit and its original artifact
remain reproducible historical evidence.
