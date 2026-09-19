# NR-04 independent runtime referee B

**Verdict: APPROVE the runtime evidence for proof commit `f488b0cfe2175e5e50d439c5a4115accc4b07b6d`.** Both official GitHub runs performed and passed the real fresh Comparator/default-kernel/sandbox checks for all 15 NR04 contracts. Their artifacts match every one of the 165 tracked project inputs at that commit. All 42 Lean files also match the frozen source packet approved in my separate mathematical review.

Reviewer: `/root/nr04_mf14_final_referee_b`, an independent nonauthor AI agent. Date: 19 September 2026. This report audits actual remote runtime evidence; it is not a new local Lean, Lake or Comparator execution. I authored no NR04 proof, edited no proof or workflow, and performed no commit, push, publication or status/count promotion. The coordinator retains responsibility for integrating the reports and deciding promotion.

## Official provenance

| Scope | Official run | Verify job | Artifact |
|---|---|---|---|
| Fork push | [35431159955](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35431159955) | 105865911345 | 10580374049, `lean-NR-04`, 25,828 bytes |
| Upstream PR 304 | [35431201248](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35431201248) | 105866043677 | 10580463616, `lean-NR-04`, 25,971 bytes |

Both run records identify `.github/workflows/lean-verification.yml`, head commit `f488b0cfe2175e5e50d439c5a4115accc4b07b6d`, completed status and success. The fork run finished at 08:17:34 UTC; the upstream run finished at 08:17:51 UTC. Each job list and actual selection-job log contains exactly one project: `NR-04`, `nonnegative-and-positive-factorizations/NR-04/lean`. The named fresh-verification and upload steps succeeded. The separate optional `checker-controls` job was skipped because the shared tooling was unchanged; all mandatory controls ran successfully inside each NR04 verify job.

The fork checked the proof commit itself. The upstream checkout and artifact receipt identify merge commit `32675f76a3e1d290dcf4fff68ed496d911896bb2`. I retrieved its official Git commit object and confirmed the ordered parents are base `71563f17926cd826a892c2bba0e294894ee57a5c` and the exact proof commit. Thus I am not identifying the upstream merge SHA with the proof SHA. Official verify-job logs independently show these exact checkout commits.

I retrieved the run, jobs, artifact and checked-commit REST objects, the official artifact ZIPs, and both selection and verification whole-job logs. `RETRIEVAL-COMMANDS.json` preserves the exact CLI arguments, times, exits, output paths and SHA256 hashes. Each ZIP's byte length and SHA256 match GitHub's artifact metadata:

- Fork ZIP: `caeca12f4e7f2ae917782a8de0860969e193af3a061320ca6b923ebee140aff4`.
- Upstream ZIP: `327175592674c027fb2d41d1812ca4da1bb69d28e34aa8326b6fcf393eb14d84`.

Safe extraction rejected absolute/traversal paths, symlinks, special files and duplicate normalized names, bounded total extracted size, and confined all writes to the evidence directory. Each ZIP contains 13 ordinary files; their exact hashes are retained in `ARTIFACT-FILES.json`. The initial whole-job log request was refused by the GitHub CLI because the response contains terminal escapes. The failed response and stderr remain archived. I then used the CLI's explicit escape opt-in to save the raw logs to files; those downloads succeeded. No failed download is counted as success.

## Source and tool binding

`INDEPENDENT-AUDIT.json` compares each artifact's complete `input_sha256` map with independently hashed `git show` blobs at the proof commit. Both maps contain exactly the same 165 files, with no missing or extra input. This includes Lean sources, Challenge, Comparator config, dependency pins, source context and review/metadata files. A separate check compared all 42 Lean source hashes with the frozen NR04 review snapshot (`7664e1a0059009b92b24cc1203033d0b3426a2b523c51b32316626d2addf8301`). The source review therefore applies to the proof that the remote checker actually accepted.

Each receipt contains exactly the published `comparator.json`: 15 unique theorem names, distinct `Challenge` and `Solution` modules, no `definition_names`, and permitted axioms limited to `propext`, `Classical.choice` and `Quot.sound`. The export records list all 15 contracts for both environments. Each actual `Solution.lean` aggregate emits all 15 axiom reports, each containing only those three standard axioms. Both runs finish with default-kernel acceptance, `Your solution is okay!`, and comparator exit status 0.

The shared `tools/lean`, `docs/lean` and workflow files are unchanged between the published base and the proof commit. I inspected the pinned harness and workflow, including non-root Linux enforcement, fresh source-only snapshot construction, refusal of tracked build artifacts, dependency validation, unchanged-input checks before and after cache use and Comparator, environment cleaning, and control execution. There is no Solution build before Comparator; the recorded dependency/cache preparation is followed by Comparator's own fresh Challenge/Solution builds and exports.

The source lock hash in both tool and result receipts is `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`, matching the published lock. Its 58 pinned files refer to Forsythe commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. The unchanged harness checks their hashes before and after tool build and before verification, records and rechecks the Comparator, lean4export and real Landrun executable hashes, and refuses a modified environment or sandbox probe. Both receipts report Lean 4.33.1 on `x86_64-unknown-linux-gnu`, Go 1.27.1 and Linux. All ten actual dependency checkout log entries match the published Lake manifest, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

I independently hashed existing archived copies of the strict adapter, actual kernel replay probe, replay runner, sandbox probe and Comparator regressions against the current source lock. I inspected the adapter and replay probe/runner. The probe invokes the real `Comparator.runBuiltinKernel`, not a substitute predicate. I also independently reproduced the harness's exact text-only noninteractive sandbox adaptation and matched its SHA256 `31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803` to both runtime receipts. This is a provenance/runtime audit, not a new exhaustive source review or independent rebuild of the entire checker toolchain.

## Actual acceptance and rejection controls

Both runs supply the following successful controls in the authenticated artifacts:

- A working unprivileged `systemd-run --user` service, with `XDG_RUNTIME_DIR=/run/user/1001` and AF_UNIX restrictions. Both build and export sandbox probes explicitly report **UID 1001**.
- Writes, creation and truncation outside `.lake` are denied, including a symlink escape. The build's designated `.lake` write succeeds; export writes and truncation are denied. Outer/export fixtures remain unchanged.
- Private user, PID, mount, network, IPC and UTS namespaces; the host parent is absent from `/proc` and cannot be signaled; host loopback is unreachable; AF_UNIX creation is denied; effective capabilities are empty; `no_new_privs` is set; the nested namespace write attempt is rejected.
- Unsupported options, arbitrary `--rw`, arbitrary `--rwx`, and relative writable paths are each rejected with exit 2. The strict wrapper still calls the real pinned Landrun under Bubblewrap; no fake Landrun or permissive fallback appears.
- The actual kernel replay accepts the honest inductive/quotient fixture, rejects a raw `True.intro` proof presented as a proof of `False` at the kernel type check, and rejects a forged `Quot.lift` at the quotient post-check.
- All five Comparator regression cases behave as expected, including positive matching, declaration/axiom rejection and actual theorem-statement mismatch rejection.
- The fresh `sorry` fixture is rejected with exit 1 for `sorryAx`. The fresh `native_decide` fixture is rejected with exit 1 for `checked._native.native_decide.ax_1_1`. These are expected negative-control outcomes.

The actual NR04 comparator logs then show fresh Challenge/Solution builds, all 15 aggregate axiom reports, both exports, default-kernel acceptance and final exit 0. Warnings about the isolated Challenge placeholders and ordinary style lints are distinguishable from the accepted Solution. The detailed checks for both runs are retained in `INDEPENDENT-DETAILS.json` and their source script.

## Audit artifacts and limitations

Evidence root: `.local-recovery-20260918/verification/NR04-linux-20260919`.

- `INDEPENDENT-AUDIT.json` SHA256: `8f1a855be57d325a36997fbd6281fa2afb10bb11fadc8574b6d6f32955626ce4`.
- Fork result receipt SHA256: `7a64499643faed28f88cefc0c58522b69e6e94e91a2c1c49d9696d5b8d3d19f7`.
- Upstream result receipt SHA256: `ac57547f264aaafe77fce704f655354df61dfafea1c59d526b6f4ea0ff110af9`.
- `MANIFEST.json` beside this report binds the complete evidence inventory, auditor scripts, source review and reviewed verifier inputs. `AUDIT-COMMANDS.json` records the audit invocations; the official artifact logs retain the actual remote verification commands.

I made two limited improvements to the provided generic read-only auditor before executing it: additional official repository/workflow-path and checked-commit SHA checks, and configurable reviewer/output fields so my independent run is not falsely attributed to root or written as `ROOT-AUDIT.json`. Default root behavior remains available. These changes only strengthen evidence checks and correct reporting; they do not modify mathematical sources, the published harness, workflow or runtime artifacts.

There is no blocking runtime-evidence finding. This audit covers the named proof commit and downloaded artifacts, not later source changes or hypothetical runs. It complements the separate original-target mathematical/source approvals. No completion count, canonical status or publication record was changed by this referee; coordinator integration and promotion remain separate actions.
