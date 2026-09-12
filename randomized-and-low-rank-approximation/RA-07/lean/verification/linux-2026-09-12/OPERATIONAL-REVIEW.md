# RA-07 independent Linux operational audit — 2026-09-12

**PASS for actual Linux verification of all six RA-07 exports at immutable revision `bf144a8ea84992d64f79f4425b18352843376286`.** [Workflow run 34715563781](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34715563781) was observed completed successfully, with all seven jobs and all recorded steps successful. The RA-07 verification job is `103612082888`; the separate checker-controls job is `103612082819`; selection is `103612054026`. Final run metadata reports completion by 20:03:51 UTC.

Reviewer: OpenAI Codex agent `/root/formal_review_standards`, independent of RA-07 proof implementer `/root/solved_statement_inventory`. This audit checks the actual remote run, its original artifacts, unchanged proof/review inputs and the existing reviewed verifier. It is not a new mathematical proof review, human review, independent verification of the entire Lean implementation, or general security guarantee. I retained and read the RA-07 and checker-control results and relevant raw job logs. The other four inherited project jobs succeeded according to GitHub metadata; their separate mathematical artifacts were not independently audited here.

## Original artifacts and complete input identity

Both original downloaded ZIPs match GitHub's SHA256 artifact digests and the upload digests in their successful raw job logs. Every extracted file is byte-identical to its original ZIP member, with no omitted member, path traversal or symlink extraction.

| Artifact | GitHub artifact ID | Original ZIP SHA256 | Files |
| --- | --- | --- | --- |
| `lean-RA-07` | `10303719852` | `6dc4290003ad74023d07c6d174cabf322b0fa5d0d4cec079cee56f6a61a1bd92` | 13 |
| `lean-checker-controls` | `10304827750` | `cd5cdf75cb93cce76a00b2e6b5c922ed32e2e9c6f5d64330b82c5b8d47cd2b1d` | 10 |

The actual [RA-07 receipt](artifacts/lean-RA-07/verify-20260912T195642Z-4213/result.json) records `comparator-accepted`, the exact commit and **123 input hashes**. I compared its complete input set to the Git tree, not a selected subset. Every input matches its immutable Git blob and current worktree bytes, and all 123 files are retained under `source/randomized-and-low-rank-approximation/RA-07/lean/`. This includes statements, every implementation module, metadata, configurations, pins, both statement reviews, both final proof reviews and their evidence.

All eight core mathematical hashes agree with both final referees. The original canonical source, Colbrook manuscript and original informal review match the three sources bound by the proof freeze and their upstream Git blobs. No mathematical or configuration substitution occurred between approval and Linux execution. The source snapshots retain historical pending-stage wording rather than silently revising the verified inputs.

## Actual six-export check and clean proof rebuild

The actual [Comparator log](artifacts/lean-RA-07/verify-20260912T195642Z-4213/comparator.log) shows separate Challenge and Solution builds and exports, followed by successful default-kernel replay and successful statement comparison. All selected declarations have prefix `NLA.RA07.`:

- `elementary_values`
- `generating_derivative_values`
- `positive_derivative_factorization`
- `power_sum_certificate`
- `second_difference_certificate`
- `errorSequence_convex`

The config has no definition exceptions and permits only `propext`, `Classical.choice`, and `Quot.sound`. The twelve actual internal/public axiom reports contain exactly those three names, and the corresponding source kernel assertions ran during elaboration. The Challenge build contains only its six intended placeholders; the Solution build has no warnings. All actual RA-07 implementation modules were built. The reported build-graph counts are **1410 Challenge jobs and 2893 Solution jobs**; these are graph counts, not claims that every dependency source was rebuilt.

The invocation uses a new temporary project copied from ordinary tracked Git blobs, excluding tracked build artifacts and old project output. The harness checks unchanged trusted inputs after dependency materialization, cache retrieval and Comparator. The logs show **ten fresh dependency clones**, each checked out at its exact manifest revision. The official Mathlib cache downloaded/decompressed **8690 files**. Thus dependency caches were used explicitly; no user project build cache was reused and no full-from-source Mathlib claim is made.

The final theorem is the complete canonical affirmative convexity assertion for every `n ≥ 3`, every strictly positive real tuple and every `2 ≤ j ≤ n−1`. Semantic fidelity, multiplicities, actual derivatives and endpoint cases were approved by the two separate final mathematical referees. This operational command explicitly reports that it does not perform semantic review. The manuscript's additional applications are outside the six exports. LeanCert supplies explicit kernel trust auditing here; no numerical interval certificate or root approximation is claimed.

## Observed controls and isolation

Both the standalone checker job and the RA-07 job executed the full control sequence. Each used real Linux user services, the strict Landrun/bubblewrap wrapper and AF_UNIX restrictions; no fallback sandbox or skipped control is present.

For both build and export modes, the logs confirm six private namespaces, an absent host parent in the private process view, blocked host-parent signaling, blocked host loopback and AF_UNIX sockets, no effective capabilities, `no_new_privs`, and sandbox UID 1001. Writes, truncation, creation and symlink escape outside the build area were denied. The designated build fixture was writable; the export fixture remained read-only. All four unsupported/mis-scoped sandbox option controls rejected with exit 2.

**Nested probe limit:** the adversarial bubblewrap executable actually ran, but its UID-map creation was denied before its inner write command. The audit records that precise observed rejection. It does not claim that the inner write ran or that all possible namespace escapes have been tested.

Each control sequence also ran three actual raw default-kernel cases: the honest inductive/quotient case was accepted, the malformed proof was rejected, and the quotient-mismatch case was rejected by the required post-check after kernel acceptance. Each of five Comparator fixtures built and exported both environments and reached its expected acceptance or rejection phase. Separate end-to-end controls built and exported the `sorry` and nontrivial native-evaluation candidates; they were rejected for `sorryAx` and `checked._native.native_decide.ax_1_1`, respectively. These were actual axiom rejections, not unrelated compilation or sandbox failures. The successful selftest and RA-07 receipts use identical tool receipts.

## Pinned tools and retained evidence

The run reports Lean **4.33.1** at commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Go **1.27.1**, and Linux x86_64. I independently checked all **58** retained Forsythe tool-source files against the exact immutable source lock and reproduced the precise reviewed CI probe adaptation. The Comparator, exporter and Landrun binaries were built successfully in both jobs; their hashes are in the receipts. These are original remote execution records, not claims of new local Linux execution.

The source lock is `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`, at Forsythe commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. The derived probe is `31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803`. The checked harness, entry scripts and lock match the previously audited Linux revision `214c142d6bfe0f0c338808f188062acbbad0fb19`; the complete tools/workflow match this branch's recorded upstream base `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. This is reuse of that reviewed infrastructure, not a fresh independent authorship review of the harness.

Selection ran its 30 metadata/selection tests and 12 harness tests successfully and actually selected RA-07. The actual RA-07 metadata gate passed schema and Comparator coverage validation for six declarations. Initial in-progress run metadata is preserved separately; final successful metadata is retained without rewriting the original artifacts.

The [identity check](identity-verification.json) is SHA256 `df4f371d8ff6b75310074ebd3cbbc8b4f1c53becb9436d95150613473cd81723` and binds the complete input set and all original frozen source files. The [control check](control-verification.json), [tool check](tool-source-verification.json) and [axiom audit](axiom-verification.json), original ZIPs, raw logs, complete source snapshots, and reproducible retrieval/audit drivers are all bound by `EVIDENCE-MANIFEST.json`. Mathematical credit remains Matthew J. Colbrook's; formalization credit remains George Stepaniants with the approved Caltech department affiliation and no George email added.

**No remaining operational failure was found.** This audit made no proof, configuration, canonical status, ID, commit, push or PR change. Canonical promotion and final publication wording remain the parent agent's separately reviewed step.
