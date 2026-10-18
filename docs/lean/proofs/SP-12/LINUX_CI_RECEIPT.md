# SP-12 complete Target: actual Linux verification receipt

**PASS, 18 October 2026.** The real isolated Linux Comparator accepted the complete unchanged `NLA.SP12.target`, and pinned LeanCert checked its kernel trust with only `propext`, `Classical.choice`, `Quot.sound`.

- Immutable checked commit: [`529e7b0560cef6461c98e950046860a160e6f86c`](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/529e7b0560cef6461c98e950046860a160e6f86c/eigenvalues-and-inverse-problems/SP-12/lean).
- Actual [workflow run 39142969327](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39142969327) and [SP-12 job 117727133138](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39142969327/job/117727133138): successful.
- Original artifact: [`lean-SP-12`, ID 12143550920](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39142969327/artifacts/12143550920).
- Canonical project: `eigenvalues-and-inverse-problems/SP-12/lean`.
- Comparator selection: only `NLA.SP12.target` from Solution; no definition holes.

For every positive-order finite simple graph, the theorem constructs one real symmetric matrix with exactly its off-diagonal nonzero pattern, a nonnegative quadratic form, the full Strong Arnold property and nullity at least the actual chromatic number minus one. Disconnected graphs, isolated vertices and the singleton are included. Diagonal entries and edge signs remain unrestricted. The mathematical construction and Strong Delta theorem are credited to H. Tracy Hall; the original explanatory application note is by George Stepaniants. This formalization, packaging and review are AI-agent work. No new theorem priority, source-author endorsement or external human review is claimed.

The actual harness result records `comparator-accepted` and `lean_cert_proof_trust: kernel-checked` for the full original export. The actual Comparator default kernel accepted the proof, and a separately generated consumer enforced theorem kind, kernel trust and the permitted transitive axioms. This is distinct from statement/Identity elaboration or earlier conditional support gates.

The [independent actual-artifact review](LINUX_ARTIFACT_REVIEW_2_2026-10-18.md) passed **40 checks**. All **96 committed project input hashes** and the exact file set matched the immutable commit and package at audit time. The original zip matches GitHub metadata and the actual upload digest, and every extracted member matches the zip. Retained real Linux sandbox logs verify restricted build/export writes, denied host networking and AF_UNIX, absent effective capabilities and `no_new_privs`. All three builtin-kernel cases, five Comparator regressions, four negative sandbox option cases, and deliberate sorry/native axiom rejections passed.

The receipt binds x86-64 Linux Lean4.33.1, compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Checker source-lock SHA-256 is `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`, binding Forsythe commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. The independently reproduced generated kernel-consumer SHA-256 is `218ecdcda801e35a0a481bebf066fefde9c3989e2a126d0b37df8738c7433233`.

| Retained evidence | SHA-256 |
| --- | --- |
| `result.json` | `1c3bc9acb3e98ef510f11e09984d74dd74e9661836cd8fe5e4df963004531f53` |
| `comparator.log` | `931d68ca27fe7098c15958c3bc774669f5a23e67a49c6da4e39e0036415ff02a` |
| `leancert-proof-trust.log` | `3be40003862f92b97f34146bdbac0bab40dfaacd9c6a4af8ce825b93b68125e2` |
| `sandbox.log` | `6b05149c7deb01a30af4993c51fec61482b0ea60b4bc6f2fde1166e90a8a9ad7` |
| original artifact zip | `d615a3d2fc8ee54391a10f1150415b8a41a2488b841868e06ae57d1be17589fb` |
| uncompressed raw job log | `e94e07bf8cede7b49b5b5f2f1bacc4920daee0d0018057c37f2ab43a88b48aee` |

The first four files are in `verify-20261018T162848Z-4209/` under the retained [artifact](verification/full-linux-ci/artifact/). The [original zip](verification/full-linux-ci/lean-SP-12.zip), [compressed raw job log](verification/full-linux-ci/job.log.gz), [GitHub metadata](verification/full-linux-ci/run-metadata.json) and [machine-readable audit](verification/full-linux-artifact-check.json) are retained outside the canonical project. Exact audit invocation is in the independent review.

Mathematical and exact-boundary evidence is supplied by the preproof statement reviews, two pre-Solution boundary approvals, [complete independent source review](CLOSURE_REVIEW_2_2026-10-18.md), [extension/final review](EXTENSION_FINAL_REVIEW_2_2026-10-18.md), and [canonical package audit](CANONICAL_CLOSURE_REVIEW_2_2026-10-18.md). The latter passed all 55 real source builds plus the independent consumer, 379 declarations and 270 theorem-kind checks, including the literal unchanged Target and actual private helper. Every copied closure source matches the separately reviewed shared source.

This receipt binds the immutable first checked package and original artifact. Subsequent promotion changes to canonical status and descriptive package metadata require a fresh committed CI run; those changed hashes are not these original 96 inputs. Original mathematical text, credits, history, IDs and paths must remain retained.
