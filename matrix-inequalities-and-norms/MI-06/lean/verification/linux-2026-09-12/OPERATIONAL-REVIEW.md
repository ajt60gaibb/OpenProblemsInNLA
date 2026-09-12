# MI-06 independent operational review

**Verdict: PASS.** Reviewed by OpenAI Codex agent `/root/leancert_examples`, 12 September 2026. I did not implement MI-06. This review audits the actual completed Linux execution and its original artifacts; it supplements the two independent mathematical statement reviews and two final proof reviews without claiming external human peer review or changing canonical status.

## Run and original evidence

The full [Linux run 34711237623](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34711237623), at commit `43b3dc65116633a68c32ec582fd093f3adc95597`, completed successfully at 18:36:34 UTC. All seven jobs and every reported step completed successfully. The detailed raw-log review covers selection, the standalone checker controls, and MI-06; the other four projects' job statuses were checked without claiming a new mathematical audit of their proofs.

The original GitHub API metadata, original archive bytes and raw job logs are retained. Both archive hashes equal GitHub's artifact metadata **and** the hashes printed by the corresponding upload steps. Every extracted file was checked byte-for-byte against its original ZIP member, with an exact filename-set comparison and no unsafe paths or symbolic links.

| Artifact | GitHub artifact ID | Original ZIP SHA-256 | Extracted files |
|---|---:|---|---:|
| `lean-MI-06` | 10303710574 | `28dbe65ba6c0f4f727a8b5bf631d380fa4f9ff930831a0949b56e5db14152d0d` | 13 |
| `lean-checker-controls` | 10303422365 | `51559d0cf43a7ae30c71b44711e6264aa180f8bc870a3bbbb6d4447ebadabc2e` | 10 |

Raw job logs: `job-103600297780.log` (selection), `job-103600321902.log` (standalone controls), and `job-103600321907.log` (MI-06). Original receipts are under `artifacts/lean-MI-06/verify-20260912T182834Z-4103/` and `artifacts/lean-checker-controls/selftest-20260912T182832Z-4123/`.

## Complete source identity and mathematical scope

The MI-06 receipt contains **exactly all 117 tracked project inputs** at the audited commit, with no missing or additional input names. I independently recomputed every digest from its Git blob and compared every current worktree file to the same bytes. All nine protected source/configuration files and all four independent review reports match the previously frozen identities. Both final mathematical referee reports explicitly bind the five mathematical statement/proof files below.

| Protected file | SHA-256 |
|---|---|
| `NLA/MI06/Definitions.lean` | `a89c6604d36aec8ae3428df7663a2dbb6f2f923b13ca5f7746aaf4f424cb29d2` |
| `Challenge.lean` | `7774d76c9e362c0f808ee4c1fec3b5607359048d5af82d0e99f60b74c52326dc` |
| `NUMERICAL_TARGETS.md` | `792aa98aa94d18d7b49e4e4b66edca89881f1e38cf51c3aacfed8525644509a4` |
| `NLA/MI06/Proof.lean` | `3c1fdf9ba68e850d26d1307ce6ac2a1e9a1037aba5645bda10aa68e7c3d44145` |
| `Solution.lean` | `389fac775519a84b79b68811e141df5f466e9818469efca889c550e3110b806a` |
| `lakefile.toml` | `94b9d948fbdcfb7cec4b7ae36dff6c5e0cf2927f215d1b7597634ed19961ee09` |
| `lake-manifest.json` | `ff63846f9c3bc57299e95cff597225fb1d99747ab48dad419f97767359b9b102` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `comparator.json` | `1fe56d984d534e7daa8e8eeaacca0543a8be5404f1dc513bf635afb7e54a5dfc` |
| `reviews/statement-referee-1.md` | `e1e8af4ece9a6b1a52b1458141a4b3916e5f68d27c41ef5254188e6e7f6d1ed6` |
| `reviews/statement-referee-2.md` | `fed44f1b753919b466b675f2dc9b4d2fb38df6617d67a0855b5747aef6c17bd5` |
| `reviews/proof-referee-1.md` | `6a12e8ccb1cc02a2b083ac42b4688eff1da948be8317808e1b149e9801c800c4` |
| `reviews/proof-referee-2.md` | `35373f2167259c1685bcee57cfe678953d4e58dabb699521474a604b57fe8cdb` |

I read the complete canonical README, Definitions, Proof and Solution, the exact six-name Comparator configuration, and both mathematical final referee reports. The target retains every positive dimension, arbitrary complex matrices, genuine complex unitaries, actual `CFC.abs` matrix moduli and ordinary positive-semidefinite order at coefficient `sqrt(2)`. The exported counterexample excludes **every** unitary pair. The informal source's stronger claim excluding every finite coefficient is expressly outside the six-export formalization; this operational PASS does not enlarge the formal scope.

The genuine CFC square-root identities, finite-dimensional common orthogonal vector and positive squared Euclidean length, PSD quadratic-form monotonicity, and homogeneous lower/upper bounds occur in the actual proof. The sole LeanCert point certificate is `2 < 9/4` with explicit `trust := kernel`; the printed certificate retained by the final referee calls `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked` on the singleton interval `[0,0]`. Its proof dependency chain reaches the square-root coefficient gap, the all-unitary contradiction, and the complete original negation. It is a substantive proof dependency, not an unused import.

## Actual build, statement comparison and trust checks

The actual MI-06 job passed the schema-v0.4 manifest and exact six-export coverage gate. The selection job passed 30 metadata/selection tests and 12 pinned harness tests. The original Comparator log shows separate fresh Challenge and Solution builds, then both requested export sets, actual default-kernel replay, and final statement acceptance:

- Challenge graph: **2710 jobs**; Definitions and Challenge freshly built. Its six intentional `sorry` warnings belong only to the isolated comparison specification.
- Solution graph: **3147 jobs**; required LeanCert modules, Proof and Solution freshly built, with **no Solution-phase warning**. No proof module imports Challenge.
- **52 unique actual axiom reports**, corresponding to 46 internal and six exported kernel trust checks, contain exactly `propext`, `Classical.choice`, and `Quot.sound`. Long private declaration names wrap some lists across physical log lines; the retained audit parses complete bracketed lists and checks their exact entries.
- Both exported environments contain all six declarations: `modulus_eq_sqrt`, `witness_moduli`, `two_vector_orthogonal`, `witness_quadratic_bounds`, `counterexample`, and `not_dominationConjecture`, all in `NLA.MI06`.
- The actual phases `Running Lean default kernel on solution.`, `Lean default kernel accepts the solution`, and `Your solution is okay!` occur in order, followed by `EXIT_STATUS=0`.

This was a fresh project snapshot, not a claim that every dependency was rebuilt. The run cloned all ten dependencies at their manifest revisions and downloaded/decompressed **8690 matching official Mathlib cache files**. The project source and non-cached LeanCert modules were freshly compiled. The pinned harness forbids tracked build artifacts, hashes the complete Git snapshot, and checks the input files after dependency setup, cache retrieval and Comparator completion.

The tool receipt records Lean **4.33.1** on Linux x86_64, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Both jobs freshly built the locked Comparator/exporter and Landrun binaries and produced identical tool receipts. The source lock hashes to `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`, pins Forsythe `8d1b0c0545a77b40245e84705aa7d273e6c81e62`, and binds the recorded CI sandbox probe. The full tools/workflow match recorded upstream base `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`; the five core harness files also remain identical to previously audited Linux commit `214c142d6bfe0f0c338808f188062acbbad0fb19`.

## Actual rejection and isolation controls

I independently read both complete original control suites. Their distinct invocation IDs and timings are retained; they are separate executions. Each suite shows:

1. **Sandbox build and export modes:** private user/PID/mount/network/IPC/UTS namespaces, UID 1001, no effective capabilities, and `no_new_privs`. Attempts to write, truncate, truncate via read-only open, create outside `.lake`, or escape through a symlink fail with read-only-filesystem errors. Build `.lake` writing succeeds only where designated; export `.lake` writing/truncation fails. Host parent lookup/signalling and loopback/AF_UNIX access fail. All four unsupported permission-option fixtures exit 2.
2. **Nested namespace attempt:** the real nested `bwrap` executable runs, but UID-map setup is denied before its inner write. This is the observed result; an inner write execution is not claimed. The read-only host view is a write-isolation control, not a general confidentiality guarantee; the run uses an isolated GitHub runner.
3. **Three real kernel replay cases:** the honest inductive/quotient fixture is accepted; a raw `True` proof declared as `False` is rejected by the kernel; the forged `Quot.lift` fixture passes the kernel stage but is rejected by the explicit quotient post-check.
4. **Five Comparator cases:** every fixture builds and exports both environments. `simple_match` is accepted. The legacy `simple_mismatch` case reaches constant-kind rejection; both helper-axiom fixtures reach actual illegal-axiom rejection. The separately named `type_mismatch` case reaches genuine theorem-statement mismatch rejection. These labels are not substituted for the actual observed rejection phase.
5. **Two additional axiom controls:** both build/export phases complete before rejection of `sorryAx` and `checked._native.native_decide.ax_1_1`, respectively; each exits 1 for the intended reason.

The user-service, sandbox, kernel-control and Comparator-control logs all exit 0; the intentionally rejected native/sorry fixtures exit 1. Thus this PASS is based on the actual checks running, not merely an outer process succeeding or a missing executable failing early.

## Retention, authorship and limits

`identity-verification.json`, `control-verification.json`, `axiom-verification.json` and `audit-checks-result.json` retain the mechanical checks; `audit_checks.py` and `fetch_artifacts.py` retain their source. The audit logic adapts the previous MI-21 audit and the MI-29 checks by `/root/formal_review_standards`, with attribution in the script. `audit-development-note.json` records exploratory parser/inventory corrections; no original evidence or mathematical source was edited to make a check pass. `EVIDENCE-MANIFEST.json` hashes all other retained files, including this report and the two original archives.

Informal mathematical proof attribution remains Matthew J. Colbrook. Formalization credit remains George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. The audited commit has empty author/committer email fields and no George email was found in the retained text. This review itself makes no commit, push, pull request, canonical promotion or claim of source-author endorsement. Comparator validates the frozen formal boundary and proof; the independent mathematical referees supply the English-to-Lean scope and definition-fidelity review.
