# SP-11 complete Target: actual Linux verification receipt

**PASS, 18 October 2026.** The real isolated Linux Comparator accepted the
complete unchanged `NLA.SP11.target`, and pinned LeanCert checked its kernel
trust with only `propext`, `Classical.choice`, and `Quot.sound`.

- Immutable checked commit: [`9264361fafb89b37b5c48236afebb304bc84110a`](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/9264361fafb89b37b5c48236afebb304bc84110a/eigenvalues-and-inverse-problems/SP-11/lean).
- Actual [workflow run 39131755109](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39131755109) and [SP-11 job 117688269984](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39131755109/job/117688269984): both successful.
- Original artifact: [`lean-SP-11`, ID 12138590670](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39131755109/artifacts/12138590670).
- Canonical project: `eigenvalues-and-inverse-problems/SP-11/lean`.
- Comparator selection: only `NLA.SP11.target` from `Solution`; no definition holes.

The theorem is the original all-graph real symmetric delta target: for every
positive graph order, a real symmetric matrix has exactly the graph's
off-diagonal nonzero pattern and nullity at least its minimum degree. The
diagonal and edge signs are unrestricted. The mathematical theorem remains
credited to H. Tracy Hall; this formalization, review and packaging are
OpenAI Codex AI-agent work. No external human review or source-author
endorsement is claimed.

The harness result records `comparator-accepted` and
`lean_cert_proof_trust: kernel-checked`. The actual Comparator/default-kernel
acceptance and the separately generated theorem-kind/LeanCert kernel consumer
refer to that full export. This is distinct from the historical seven-module
[support receipt](LINUX_SUPPORT_CI_RECEIPT.md) and statement-identity checks.

An [independent actual-artifact audit](../../campaign-2026-10-17/verification/SP11-FULL-LINUX-CI-INDEPENDENT-REVIEW.md)
passed **40 checks**. All **135 committed project input hashes** and the exact
file set matched the checked commit and the package at audit time. It also
verified the original zip against GitHub metadata and the actual job upload
digest, and matched every extracted artifact member. The retained real Linux
sandbox logs show restricted build/export writes, private namespaces, denied
host networking and AF_UNIX, no effective capabilities and `no_new_privs`.
All three builtin-kernel controls, five Comparator regressions, four sandbox
option rejections, and deliberate sorry/native axiom rejections passed.

The receipt identifies Lean 4.33.1, compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, on x86-64 Linux. The checker
source-lock SHA-256 is
`b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`,
binding Forsythe commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`.
The actual generated proof-trust consumer SHA-256 is
`97195b048bf0b7e5b4c762016a8abc29e8ed624cb9eb5d1a4f55582a8bdd17a1`.

| Retained evidence | SHA-256 |
| --- | --- |
| `result.json` | `993f80bcc3aa4eb17aef9006ffe8f1caf7dd23ac48b460a268ffbc40e18d2db4` |
| `comparator.log` | `a2975694f49d8bab169e9496ce5a66805597ce0bb34c2c01eeafc40ce6ce69b4` |
| `leancert-proof-trust.log` | `c0474d6c78d3d4522ae1128a620a216a5ca4c52b27cd90141bc82ca4db3b4681` |
| `sandbox.log` | `cad1dbe8aa97047459b2d140a811440c571ff34295c9222510df7d2a425a5980` |
| original artifact zip | `bf81f1df753ac7710f63e984c282982cb07ac0d7f2b39bae3a19ae9ca1530e0a` |
| uncompressed raw job log | `35312cb0ad0b657c24fba2a85e21c5d6e389c27994735de2ea332fb9b6316e08` |

The first four files are under
`verify-20261018T133100Z-4187/` in the retained
[artifact directory](../../campaign-2026-10-17/verification/sp11-full-linux-ci/artifact/).
The [original zip](../../campaign-2026-10-17/verification/sp11-full-linux-ci/lean-SP-11.zip),
[compressed raw job log](../../campaign-2026-10-17/verification/sp11-full-linux-ci/job.log.gz),
[GitHub metadata](../../campaign-2026-10-17/verification/sp11-full-linux-ci/run-metadata.json),
and [machine-readable audit](../../campaign-2026-10-17/verification/sp11-full-linux-artifact-check.json)
are retained separately from the canonical project. The audit script and
exact invocation are in the independent report linked above.

Independent semantic checks are recorded in
[full source review 1](CLOSURE_REVIEW_1.md),
[full source review 2](CLOSURE_REVIEW_2_2026-10-18.md), and
[canonical-package review](CANONICAL_CLOSURE_REVIEW_2_2026-10-18.md).
The canonical audit passed 42 fresh Lean commands, 291 declarations and 201
theorem/lemma-kind checks, including the literal unchanged Target type.

This receipt binds the immutable checked commit and original artifact. The
subsequent promotion updates canonical status and descriptive package
metadata while preserving proof/statement sources. Those refreshed project
inputs require a fresh committed CI check; this receipt does not relabel
their changed hashes as the original 135 inputs. The original pre-promotion
[README, TeX and PDF archive](../../campaign-2026-10-17/verification/sp11-originals-47006/manifest.json)
is byte-identical to published base `47006df8b3a6c724a557266c891893d03e69323a`.

## Refreshed promoted package — actual Linux PASS

The promoted package was freshly accepted at immutable commit
[`9c1f62be980d174b9418285d2e54fb9deae3a5bc`](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/9c1f62be980d174b9418285d2e54fb9deae3a5bc/eigenvalues-and-inverse-problems/SP-11/lean)
by [run 39140854908](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39140854908),
[SP-11 job 117714897072](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39140854908/job/117714897072).
The real full-Target Comparator and LeanCert kernel checks, controls and sandbox
checks all passed. An [independent refreshed-artifact review](../../campaign-2026-10-17/verification/SP11-REFRESHED-LINUX-CI-INDEPENDENT-REVIEW.md)
passed all 40 checks and matched all 135 committed/current project input hashes
and the exact file set. This separately resolves the refreshed-input check
required above; the original receipt and artifact remain historical evidence.

The original refreshed `lean-SP-11` artifact ID is `12141672724`, with archive
SHA-256 `2dbbcc28fd12ea1978ca5bf0bcdebfe56ed209b694c289ec8f78c4e9be21ee37`.
Its digest matches GitHub metadata and the actual upload log; every extracted
member matches the retained zip. Actual logs, API metadata and the original zip
are retained under [sp11-refreshed-linux-ci/](../../campaign-2026-10-17/verification/sp11-refreshed-linux-ci/),
with the complete [machine-readable audit](../../campaign-2026-10-17/verification/sp11-refreshed-linux-artifact-check.json).
The proof sources and full frozen Target are unchanged.
