# Author-collected actual Linux receipt

The offline author audit passed all **1,264 checks**. This is mechanical receipt
collection and audit, pending separate independent audit. It is not independent
source review or full TR-26 verification.

- [Successful PR Linux run 40390314938](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40390314938).
- Actual TR-26 project job: `121812956621`; original artifact: `12685225619`.
- Selected theorem: `NLA.Proofs.TR26.isotropic_degree` only; no replaceable definitions.
- Actual result: `comparator-accepted`, LeanCert `kernel-checked`, standard three axioms.
- Official Lean `4.33.1`, `x86_64-unknown-linux-gnu`; actual platform
  `Linux-6.17.0-1022-azure-x86_64-with-glibc2.39`.

The raw checkout log and immutable Git object prove that CI executed synthetic
merge `71e8a941218a22a9c4f48f553b8e9767e7843349`, with parents
`ccc7864f5034cf7c4602f7577ceaf083ebf63d52` and
`6c607ab14af2b8b2b8075f0b3f1798e037c10899`. The audit checks every one of the
354 CI input files, including the 353 package-locked files and `PACKAGE_LOCK.json`
itself, against both that executed merge and the proof head. All package inputs
also equal the later metadata-only head
`04045bad74f9dff03488b3b9080b081f397e5349`.

The run's nested PR head and live PR metadata had moved to that later head at
retrieval. Those mutable fields are recorded separately and are not used to
infer the executed checkout. All 24 pre-proof frozen original inputs, the full
canonical README and both actual preserved original copies are checked.

Original ZIP: **26,456 bytes**, SHA256
`5a7095e9d185add28288faff6e1bb96ca609b670982688c1a9180c124488f567`.
Separately retrieved raw job log: **111,630 bytes**, SHA256
`189262eaf19e29e5a3b2fe2c89d6bb0a5262c84001d35074f92231ca6e9f4834`.
The original ZIP digest matches GitHub's artifact metadata and raw upload log.
Every artifact log body is matched in order against the separate raw job log.
Actual kernel, Comparator, isolation, `sorryAx` rejection and native-axiom
rejection controls are checked; the separate checker-controls job was skipped.

Reproduce the offline audit using the command in `README.md`. The full report is
`initial-run-audit/AUTHOR_CI_RECEIPT.json`; its exact auditor SHA256 is
`a6764158d4e6fbf53b293bb49e0ec25689f67fb278672f267a1e33d9b4e19311`.
Raw API metadata, original ZIP and raw job log are under
`retained/run-40390314938/terminal/`. The extracted artifact and reconstructed
kernel consumer are retained under `initial-run-audit/`.

The initial statement-boundary failure is separately retained and identifies
only stale generated `docs/lean/statements/inventory.json`; it is not a Linux
proof-verification failure. Audit-driver diagnostics are retained under
`diagnostics/`. No package file, branch, PR metadata or canonical status was
changed by this collection task.
