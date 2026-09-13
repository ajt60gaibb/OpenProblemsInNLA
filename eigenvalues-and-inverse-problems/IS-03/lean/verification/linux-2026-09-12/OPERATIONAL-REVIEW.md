# IS-03 actual Ubuntu operational review

**Verdict: PASS for the exact candidate and observed execution below.** This is an independent operational review of actual GitHub records, not a simulated Linux check. The coordinator must separately accept the evidence and complete publication review before promotion.

Reviewer: `/root/leancert_examples`, OpenAI Codex agent, 12 September 2026 in America/New_York (execution timestamps are 13 September UTC). I authored neither IS-03's statements nor implementation: `/root` and `/root/solved_statement_inventory` are coauthors. I previously served as independent statement and final mathematical referee 1; this operational role adds no mathematical referee. `/root/formal_review_standards` is the other independent mathematical referee. Root retrieved the original remote records but issued no retrieval-time verdict. Its `context.json`, fetch driver and retrieval-only `FETCH-IDENTITY.json` are retained unchanged.

## Actual candidate and execution

- Candidate: `f87375fa5d7926fe0e065199eaab8f15ac5a5e48`, branch `codex/lean-is03-derivative-realizability`, `sgstepaniants/OpenProblemsInNLA`.
- [Ubuntu verification run 34728101436](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34728101436): all **12 jobs and all steps completed successfully**. This report audits the original IS-03, checker-control and selection records; it retains the whole run's logs without claiming a separate semantic audit of unrelated project artifacts.
- [Permanent-ID run 34728101524](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34728101524): same candidate, all steps successful, including all **17 permanent-ID tests**.
- Project: `eigenvalues-and-inverse-problems/IS-03/lean`. Git, the actual remote receipt and the unchanged local candidate contain the **same complete 303-input set**, with every byte identical. The original commit has George Stepaniants as author/committer and entirely empty email fields.

Actual main verification ran Lean **4.33.1**, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, on Ubuntu 24.04 x86_64, runner image `ubuntu24/20260907.300`. The receipt identifies Linux `6.17.0-1022-azure`. Comparator used a newly copied source project under `nla-fresh-proof-ww_d_ax0/project`, built Challenge (**1718 graph jobs**) and Solution (**3101 graph jobs**), exported both independently, and reported:

```
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
EXIT_STATUS=0
```

Both actual export lists contain all seven selected theorems: `nonnegative_power_trace`, `witness_admissible`, `witness_polynomials`, `trace_moment_certificate`, `negative_moment`, `counterexample`, and `not_derivativeRealizabilityConjecture` in namespace `NLA.IS03`. There are no definition exceptions. All **18 distinct actual axiom reports** contain exactly `propext`, `Classical.choice`, and `Quot.sound`; eighteen explicit source `#assert_trust kernel` checks match them. Challenge's seven deliberate reference holes appear only during its separate build; the Solution phase has no warning or admission.

The material numerical theorem uses **explicit kernel LeanCert** for `-8593/823543 < 0` on a singleton interval, with no subdivision or approximate root computation. Both independent final mathematical reviews bound and replayed its actual retained Boolean helper and confirmed its consumer chain into the seventh-trace contradiction and full original negation. This operational check binds their exact source and evidence bytes to the fresh accepted Linux exports; it does not replace their arbitrary-real-matrix, characteristic-polynomial, spectral, Newton or trace arguments with numerical diagnostics.

## Original evidence identity and complete inventories

Original artifact hashes were independently matched to **both GitHub artifact metadata and the actual upload-job digest/ID lines**. ZIP CRC, unique safe names, no symbolic links, complete extracted file sets, and every extracted byte were checked:

| Artifact | Original ID | Original ZIP SHA-256 | Files |
| --- | --- | --- | --- |
| `lean-IS-03` | `10308926506` | `5a72c6ed55af7aea388b74910cd0b0cbc2c81004427b145390fbe74f4ec1ac1e` | 13 |
| `lean-checker-controls` | `10308311562` | `2ef6c60b6f7e7367fd72ba3e484ab7e350cf8970c8e6ae880bb4bbff494c5cb5` | 10 |

The complete original **152-file run-log ZIP**, containing twelve whole-job logs, is retained with SHA-256 `90333c96cb8f3ec74e7b5d04869c16c6d41cc345c38200b110ce28ddf495b388`. The separately fetched three selected raw job logs are byte-identical to their whole-job archive entries. This is a locally recorded digest of the authenticated original log download, not a claim of a GitHub-published checksum for that archive. Original metadata pages agree exactly with combined metadata inventories.

All **203 proof-freeze inputs**, **34 statement inputs**, and **ten original Git source blobs** remain bound to the candidate. Only the historical README was refreshed during prior packaging, with its exact original bytes archived at `verification/linux-candidate-2026-09-12/README.statement.md`; all **202 non-README proof inputs** are byte-identical. The preceding **288-input** packaging baseline is also preserved through that archive.

The two statement and two final reviewer evidence inventories bind respectively **23, 26, 36 and 45 files**, including adjacent report paths where declared. Their report and inventory hashes, fresh-source receipts, both actual 61-declaration closure reviews and 33/40 required semantic dependency sets match the immutable candidate.

The preparer's manifest has a **historical whole-project scope**, not a folder-local scope: **298 bound inputs**, including all four nested manifests, plus its own outer file form exactly 299 inputs. The four subsequent root-acceptance inputs complete the candidate's 303 files without overlap or omission. Every `../../` path was normalized within the project. The operational outer inventory includes **every nested manifest**, including those inside the retained immutable source snapshot; only its exact own path is excluded.

## Actual checking phases and rejection controls

I read the actual main Comparator, dependency/cache and bootstrap logs, selected raw workflow steps, and all substantive control output. Both independent raw control executions agree after removing only ephemeral invocation IDs, temporary-directory names, elapsed times and resource measurements. Original bytes of both executions remain retained and are also checked separately by the inspector.

- **Build and export sandbox modes:** private user/PID/mount/network/IPC/UTS namespaces, unprivileged UID 1001, zero effective capabilities and `no_new_privs`; outside writes, truncations, creations and symlink escapes denied; parent-process lookup/signalling and host loopback access denied; AF_UNIX socket creation denied. Only the designated build `.lake` fixture was writable, and export `.lake` was read-only. All four unsupported/wrong-path options were rejected with exit 2.
- **Nested namespace scope:** the real `bwrap` executable ran and was denied while setting up its UID map, before the inner write could execute. This is not described as an observed inner-write denial.
- **Actual kernel controls:** an honest inductive/quotient fixture was accepted; an invalid raw proof was rejected for its actual type mismatch; a quotient post-check mismatch was rejected after ordinary kernel acceptance. All three direct `Comparator.runBuiltinKernel` cases reached their intended phases.
- **Actual Comparator controls:** all five fixtures separately built and exported Challenge/Solution and reached their prescribed success, kind/statement mismatch or illegal-axiom phase. Fixture names do not substitute for the observed rejection reason: `simple_kind_mismatch`, as supplied, was rejected for illegal axiom `helper`.
- **Actual axiom controls:** completed build/export of the sorry fixture was rejected for `sorryAx`; completed build/export of the native fixture was rejected for `checked._native.native_decide.ax_1_1`, both exit 1. These were deliberate raw executions, not a source-text grep presented as a control run.

The main actual command used the strict sandbox/exporter, sanitized `env -i`, `systemd-run --user --wait --pipe --collect`, and `RestrictAddressFamilies=~AF_UNIX`; no skip-kernel flag was used. Actual workflow setup configured unprivileged namespaces and then called the pinned shell wrappers with the work root as a positional argument. Original command lines and all phase-specific outcomes are retained.

All **58 locked checker/source files** match the pinned Forsythe snapshot `8d1b0c0545a77b40245e84705aa7d273e6c81e62`, including licenses and control programs. The derived sandbox probe matches its receipt exactly. The actual harness/bootstrap/verify/selftest bytes match the previously audited infrastructure commit `214c142d6bfe0f0c338808f188062acbbad0fb19`; the workflow/tooling and ten original problem-source files are unchanged from the candidate base `f41f1f9ffa2171550d4bb795862c6170c4f26070`. Both remote tool receipts agree, including actual binary hashes.

The remote run freshly cloned and checked out **all ten exact dependency pins**, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. It downloaded/decompressed **8,690 matching Mathlib cache files**, as actually logged. This is a fresh project proof build with official matching dependency objects, **not** a from-source rebuild of all Mathlib. Comparator/exporter and Landrun bootstrap builds succeeded in both jobs.

## Review limitations and retained corrections

The inspector was adapted from this agent's IE-23 audit, with prior campaign/standards attribution retained. Two operational-script assumptions were corrected transparently and their initial scripts/logs archived: a global LeanCert option was over-required in the pure exact Newton module, which already has three explicit kernel audits; and an assumed `--work-root` flag was replaced by the actual positional shell-wrapper invocation. No mathematical input, control outcome, source pin or acceptance criterion was changed.

No local Lean run, dependency rebuild/copy/download, proof change, canonical status change, commit or push was performed for this audit. Colbrook's mathematical credit and George Stepaniants's name/full Caltech Computing and Mathematical Sciences affiliation remain unchanged without publishing George's email. Current candidate metadata's Linux-pending notices remain historical until ordinary publication preparation. This is not external human review, an official Tau Ceti result, or an exhaustive audit of Lean/Mathlib themselves.

Reproducible inspection is in `audit_checks.py` and `inspect_phases.py`; their successful logs and detailed identity, phase, axiom, tool, archive and control results are retained. `EVIDENCE-MANIFEST.json` seals every evidence file except only itself. The coordinator's independent operational acceptance and the later publication review remain separate gates.
