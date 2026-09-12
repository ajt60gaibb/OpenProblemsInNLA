# Linux Lean verification infrastructure: operational review

**Decision: PASS for the checker infrastructure at commit `214c142d6bfe0f0c338808f188062acbbad0fb19`.** Every required sandbox, raw-kernel, and Comparator control executed and produced its expected result. This run verifies checker infrastructure and no NLA mathematical target. No infrastructure branch was modified during this review.

Reviewer: Codex agent `/root/formal_review_standards`, 12 September 2026. This is an independent inspection of the actual GitHub execution, downloaded artifacts, and root-authored CI adaptations. The reviewer previously implemented the generic harness, so this report is not represented as an independent second source-code review of that original driver. The root-authored workflow, project selection, metadata validation, and CI adaptations received separately scoped reviews. This is AI-agent review, not human peer review or formal certification of an operating system.

## Identity and provenance

- Repository/branch: `sgstepaniants/OpenProblemsInNLA`, `codex/lean-verification-infrastructure`.
- [Actual run 34702904248](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34702904248), triggered by a push at `2026-09-12T15:39:45Z`, completed successfully at `15:41:17Z`.
- [Checker job 103577715893](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34702904248/job/103577715893) ran successfully; its build/control step ran from `15:40:33Z` to `15:41:11Z`. It was not skipped.
- Artifact `lean-checker-controls`, ID `10300566765`: the downloaded original ZIP has SHA-256 `d063d6562d710b66b90e8ff88d0efdb5b5d2806d2948537428ae3f246a74a01e`, independently recomputed and matched to GitHub's artifact digest. Every extracted file was compared byte-for-byte with that archive.
- [Evidence manifest](EVIDENCE-MANIFEST.json): SHA-256 `124dcd81a75fa9622bedf210343406e81d00b0edaca289c980a44b7de4ca9065`. It binds all 35 downloaded/source/evaluation files. [Identity verification](identity-verification.json) and [control verification](control-verification.json) record the independently checked relationships.

The checked-out infrastructure worktree was clean at the run's exact commit. Copies of the workflow, harness, source lock, relevant documentation, validators/tests, and original control sources are retained under `source/`. The workflow and file contents were read, not inferred from the green run badge.

The actual host was Ubuntu 24.04.5, Linux `6.17.0-1022-azure`, x86-64, with Lean 4.33.1 (commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and Go 1.27.1. The bootstrap logs show fresh compilation of Landrun, Comparator, and lean4export; the 20-job checker/exporter build completed. The run receipt records binary hashes. This audit does not claim to have downloaded and independently rebuilt those Linux binaries.

The source-lock hash is `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`, pinning 58 source files to Forsythe commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. All original files were independently hash-checked locally. The derived CI-probe hash in the actual receipt is `31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803`, matching an independently generated derivation from those sources and the already-reviewed AST-preserving adaptation.

## Actual Linux isolation controls

The [sandbox log](artifacts/lean-checker-controls/selftest-20260912T154052Z-4184/sandbox.log) records both build and export modes completing with exit zero as UID 1001. All six namespaces—user, PID, mount, network, IPC, and UTS—differ from the host. The host parent is absent from the private `/proc` and cannot be reached by the signal lookup. The host loopback listener cannot be reached; AF_UNIX socket creation is denied. Effective capabilities are empty and `no_new_privs` is set.

Both modes reject opening an outer file for writing, truncation, read-only open combined with truncation, writing through a `.lake` symlink to an outer file, and creating an outer file. The build positive control actually creates the designated file inside `.lake`. Export mode additionally rejects writing and truncating inside `.lake`. The probe verifies unchanged contents of all outer and export fixtures at the end.

The nested Bubblewrap executable is now actually started. Its attempt is rejected in both modes at **UID-map setup**, with `bwrap: setting up uid map: Permission denied`, and exits one. This is successful containment of the attempted nested-namespace escape. The inner write payload is not reached; the log does not establish what would happen after a successfully created nested namespace. The separate direct-write and symlink controls do exercise their write operations. The reviewed probe-only `--rox /usr/bin/bwrap` grant permits execution without adding write permission, leaves the actual Comparator sandbox unchanged, and removes no original assertion.

All four malformed sandbox invocations are executed and rejected with the expected exit two: an unknown unrestricted-filesystem option, an outer `--rw` path, an outer `--rwx` path, and a relative `.lake` `--rwx` path. A bounded AF_UNIX-restricted user-service startup check also exits zero. The noninteractive transport/deadline changes do not provide a fake sandbox or accept a missing namespace control.

## Actual proof-checker controls

The [raw replay log](artifacts/lean-checker-controls/selftest-20260912T154052Z-4184/kernel-controls.log) records the real `Comparator.runBuiltinKernel` calls, with the intended Comparator `Main.olean` selected despite the exporter's module sharing that name:

| Raw replay case | Observed result |
| --- | --- |
| Honest fixture including inductives and quotient primitives | Kernel accepts |
| `True.intro` supplied as a raw proof of `False` | Kernel rejects at declaration replay with type mismatch |
| Falsified exported `Quot.lift` | Quotient post-check rejects after normal primitive regeneration |

The last case deliberately prints initial kernel acceptance before the quotient post-check rejection. The final rejection and exact mismatch reason are present; treating the earlier acceptance line as the final outcome would misread the log. The source probe checks each expected failure phase, not just any nonzero exit. Its trusted synthetic declarations test the kernel API; this is distinct from the following full build/export/sandbox pipeline.

The [Comparator log](artifacts/lean-checker-controls/selftest-20260912T154052Z-4184/comparator-controls.log) records fresh Challenge and Solution builds and exports in every fixture:

| Comparator fixture | Observed result |
| --- | --- |
| `simple_match` | Exit 0, default kernel acceptance, final success message |
| `simple_mismatch` | Exit 1, constant-kind mismatch |
| `simple_axiom_issue` | Exit 1, illegal custom axiom `helper` |
| `simple_kind_mismatch` | Exit 1, illegal custom axiom `helper`, as this retained fixture actually tests |
| `type_mismatch` | Exit 1, target theorem statement mismatch |

The additional [sorry control](artifacts/lean-checker-controls/selftest-20260912T154052Z-4184/negative-sorry.log) completes both builds/exports and rejects `sorryAx`. The [native control](artifacts/lean-checker-controls/selftest-20260912T154052Z-4184/negative-native.log) also builds and exports, then rejects the actual Lean 4.33.1 generated axiom `checked._native.native_decide.ax_1_1`. The native fixture uses `(List.range 37).reverse.length = 37`; its observed axiom proves the negative test was not optimized into a kernel-only proof. Both expected failures exit one and are accepted only as rejection controls. No corresponding phase is skipped.

The actual select job also passes 20 project/manifest tests and 12 harness tests. The selftest result explicitly records `mathematical_verification: none; checker fixtures only`.

## Scope and remaining gates

No mismatch or incomplete **required checker control** was found. The nested-namespace coverage limitation above should be retained in descriptions; no sandbox weakening or further rerun is needed merely to hide that successful earlier denial.

The `verify` matrix job is intentionally skipped because this infrastructure branch contains no per-problem Lean projects. Consequently this run does not yet exercise a real NLA project's locked Mathlib/LeanCert dependency setup, actual mathematical exports, or catalog promotion. Each problem needs its own full fresh-project Comparator run and independent semantic reviews. The successful fixture pipeline is adequate operational evidence for the infrastructure PR, not for labeling a problem Lean verified.

Comparator checks formal statements, used definitions, allowed transitive axioms, and kernel acceptance. It does not certify English-to-Lean fidelity; that remains the independent statement reviewers' job. These finite security controls are evidence of the actual configured host's behavior, not a proof against every possible operating-system exploit.

GitHub reports the artifact's expiration as 11 December 2026. The downloaded original archive, extracted logs, immutable source identities, and hashes retained here preserve the audit evidence beyond a transient web view. For the infrastructure PR, describe the scoped checker success and link the actual run. A suggested concise description is in [PR-DESCRIPTION.md](PR-DESCRIPTION.md).
