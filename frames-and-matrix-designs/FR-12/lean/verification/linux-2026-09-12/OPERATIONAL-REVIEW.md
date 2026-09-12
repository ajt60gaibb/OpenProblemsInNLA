# FR-12 independent Linux operational audit — 12 September 2026

**PASS.** The actual Linux run completed successfully, its original artifacts match GitHub's published digests, and all **137** recorded project inputs match the complete committed project tree and the reviewed mathematical sources. All seven required exports passed the real Comparator, standard-three axiom restrictions and Lean's default-kernel replay. The actual isolation and rejection controls ran successfully in both the checker job and the FR-12 verification job. No required check was skipped.

Reviewer: independent agent `/root/formal_review_standards`. I did not author FR-12's Lean proof; I previously served as statement and final proof referee 1 and prepared the reviewed candidate documentation. This operational review inspects actual execution and source identity. It is not a new mathematical proof, external human review, historical-priority certification or a claim that Comparator determines the English statement's meaning.

## Actual run and preserved original artifacts

- Repository: `sgstepaniants/OpenProblemsInNLA`.
- Immutable candidate: [`3e20bae9a07b1a33db8fdfb18bdebb9e590071a9`](https://github.com/sgstepaniants/OpenProblemsInNLA/commit/3e20bae9a07b1a33db8fdfb18bdebb9e590071a9).
- Actual [Lean verification run 34718277411](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34718277411): completed **SUCCESS**. All seven jobs and their recorded steps succeeded. The mathematical audit here covers FR-12; the other four problem artifacts are not independently audited by this report.
- Relevant jobs: selection `103619318532`, checker controls `103619349213`, and [FR-12 verification `103619349333`](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34718277411/job/103619349333).
- Companion [permanent-ID run 34718277412](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34718277412), job `103619318570`, also completed **SUCCESS** at the identical commit. Its retained raw log validates 217 permanent IDs and shows the 17 ID tests passing.

| Original archive | GitHub artifact ID | SHA256, matched against GitHub metadata and raw upload log | Extracted files |
| --- | --- | --- | --- |
| `lean-FR-12.zip` | `10305946817` | `8e64089e94c2953d4fae093162b41a3f36540f1888b6f6cd48a11c1dc9a5cc19` | 13 |
| `lean-checker-controls.zip` | `10305911799` | `fdc1eddcbe4c3be6e7747fb87de935597b11706a2eadcec35f6a40226028140a` | 10 |

The complete original `run-logs.zip` is retained as well: SHA256 `f13fa31cf026a7ad05444955d366da6e3dca72cae82b3488bcfef3d0e4216dcf`. It contains 87 log files whose individual hashes and sizes are recorded in [run-log-archive.json](run-log-archive.json). This log ZIP was retrieved from GitHub's authenticated run-log endpoint; unlike the two artifacts above, no GitHub-published digest is claimed for it. The selected raw job logs, all run/jobs/artifact metadata, both original artifact ZIPs and their exact extracted bytes are retained. Archive paths and CRC integrity were checked.

## Source, statement and review identity

The actual [FR-12 receipt](artifacts/lean-FR-12/verify-20260912T205219Z-4137/result.json) records `comparator-accepted`, the exact candidate commit and all 137 SHA256 inputs. I compared its key set with `git ls-tree` for the complete project, rather than trusting a declared file count. Every input's bytes match both the immutable Git blob and the current candidate worktree. The source snapshot under `source/frames-and-matrix-designs/FR-12/lean/` retains all those bytes, including every nested evidence manifest.

The independently approved proof freeze remains `c65d4deaa3e02af8c20a584dd81b944dbdc72f262e326630e115e5fc9070aa87`. All 73 non-README frozen files are unchanged; the historical README is preserved byte-for-byte in its candidate archive. The current README and actual v0.4 manifest match the independently checked candidate packaging hashes and passed the actual Linux metadata/schema check. Their historical pending-Linux labels correctly describe the pre-execution candidate and have not been rewritten in this evidence snapshot.

Both final reports explicitly bind all eight central mathematical inputs, and their report hashes match both the receipt and the candidate packaging record:

- Final referee 1: `b0f455ab34b6d79a0f7fd5c9560a5e1b67eb4bf4a2a6d85772d87e6549428d6f`.
- Final referee 2: `253962587f197745f234aec95b4a3570b3f4f0e4d55feb37bdca6372d62490a9`.
- Statement referee 1: `1f5dacc0d57302b09a2c25c71372c1527d01b3f0b247a9183b1130e4a45fd2fe`.
- Statement referee 2: `d288c647cedf362609a2630c8072ba66331e04d572ca11632cf6065110581e54`.

The four original canonical/source files match the reviewed base `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc` and are separately retained. The original mathematical target and current canonical **Solved** status were not changed by this audit. Detailed machine checks are in [identity-verification.json](identity-verification.json).

## Actual fresh proof verification

The trusted harness copies the project without its old `.lake` outputs into a new temporary directory, constrains the environment, and hashes the inputs before and after dependency preparation and proof checking. The actual log shows a new `nla-fresh-proof-…/project` location and the enforced systemd AF_UNIX restriction. All ten dependencies were freshly cloned at the exact manifest revisions, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

The official Mathlib cache downloaded and decompressed **8690 files**. This was **not a complete source rebuild of Mathlib**. The actual project modules were freshly elaborated; the recorded graph sizes were 2149 jobs for Challenge and 2157 for Solution. Challenge's seven deliberate placeholders are isolated to the reference environment. The Solution phase has no warnings, admitted proof or native axiom; all 14 internal/public axiom reports contain exactly `propext`, `Classical.choice` and `Quot.sound`. The corresponding 14 explicit LeanCert kernel trust commands are present in the exact checked sources and executed during their builds.

The actual config and both exports contain precisely:

1. `NLA.FR12.counting_semantics`
2. `NLA.FR12.injective_doubling`
3. `NLA.FR12.factorial_doubling`
4. `NLA.FR12.power_two_nonempty`
5. `NLA.FR12.power_two_lower_bound`
6. `NLA.FR12.counterexample`
7. `NLA.FR12.not_countingConjecture`

There are no definition exceptions. The main [Comparator log](artifacts/lean-FR-12/verify-20260912T205219Z-4137/comparator.log) shows separate Challenge and Solution builds and exports, actual default-kernel replay, successful kernel acceptance and successful statement/definition comparison, ending with exit status zero. This is an observed executable result, not a future command or a local build relabeled as Linux verification. [axiom-verification.json](axiom-verification.json) records every printed declaration.

## Checker identity and exercised rejection controls

The checked harness/source-lock/bootstrap/selftest/verify bytes are unchanged from the independently audited infrastructure at `214c142d6bfe0f0c338808f188062acbbad0fb19`. Shared tools, workflow and CI toolchain files also match the candidate's reviewed upstream base. All **58** locked Forsythe source files were independently rehashed, checked against lengths and immutable source-lock hashes, and retained with their licenses. The exact CI probe was reconstructed from the pinned original and compared with the Linux receipt.

- Forsythe source commit: `8d1b0c0545a77b40245e84705aa7d273e6c81e62`.
- Source lock SHA256: `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`.
- Harness SHA256: `f81767a17973956fbe9e5765c664d4639cce15ddf8c106f70cdcb32151808c2f`.
- Derived CI probe SHA256: `31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803`.

The standalone checker job and FR-12 job independently built the real comparator/exporter and Landrun tools. Their receipts agree on exact Linux executable hashes, Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, and Go 1.27.1. All bootstrap logs end successfully. Exact hashes and receipts are in [tool-source-verification.json](tool-source-verification.json).

In **each** of those two jobs, the raw logs establish:

- Both build and export sandbox modes execute as non-root UID 1001 with private user/PID/mount/network/IPC/UTS namespaces, no effective capabilities and `no_new_privs`. Host process access and signaling, loopback access and AF_UNIX socket creation are denied. Writes, truncation, creation and symlink escapes outside the permitted area are denied. Build-mode `.lake` writing succeeds; export-mode `.lake` writing and truncation are denied. Outer/export fixture bytes stay unchanged.
- The adversarial nested `bwrap` executable runs, but its **UID-map creation is denied before any inner write executes**. The raw probe's “nested namespace write attempt” label must not be paraphrased as evidence that an inner write occurred and was blocked.
- All four unsupported/widening sandbox-option controls reject with exit status two.
- The actual raw-kernel controls accept an honest inductive/quotient fixture, reject an invalid proof term, and reject a changed `Quot.lift` at the quotient post-check after kernel replay.
- All five Comparator fixtures build and export both environments and return their required phases and statuses. The extra admitted-proof and genuine `native_decide` controls are rejected after export for `sorryAx` and `checked._native.native_decide.ax_1_1`, respectively. Their expected exit status one is checked by the successful enclosing harness.

Thus the control success is not inferred solely from a green job or from expected test names. Actual phases, rejection reasons, modes and statuses were inspected and checked by [audit_checks.py](audit_checks.py); [control-verification.json](control-verification.json) records them.

## Scope and retained evidence

This audit completes the execution gate for the already independently reviewed full negative answer to FR-12's labeled Hadamard counting target. The formally proved doubling factor is **m!**, which suffices for the exact manuscript lower bound and full conjecture negation. The stronger informal all-matching factor `(2m−1)!!`, existence at every admissible order, matching upper bounds and historical priority are outside the formal exports. LeanCert supplies actual kernel trust auditing of this exact proof; there is **no numerical interval certificate** to claim.

The [outer evidence manifest](EVIDENCE-MANIFEST.json) binds **255 files**, and the retained directory contains **256 files including that manifest**. Only that exact outer path is excluded from its own listing; all nested manifests are included. The original complete run-log ZIP, its internal entry inventory, both original artifact ZIPs and all extracted files are preserved. Counts are derived from actual directory contents rather than copied from another problem. [verify_evidence.py](verify_evidence.py) checks exact inventory equality, sizes and hashes offline.

No proof, config, pin, original source, canonical page, registry or existing review byte was changed. No commit, push, PR, status promotion or unnecessary repeat Linux execution was performed. Root's publication review and accurately updated current metadata remain separate subsequent actions.
