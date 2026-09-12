# MI-07 Linux verification: independent operational review

**PASS.** The actual Linux run accepted all seven reviewed exports and replayed
their exported declaration closure with Lean's default kernel. This verdict is
based on the original artifact ZIPs, executed-stage logs, receipts, committed input
hashes, and separately completed proof reviews, not the workflow exit status alone.

Reviewer: independent agent `/root/solved_statement_inventory`, 12 September 2026.
I did not implement the MI-07 proof. I audited the remote execution locally; I did
not rerun Linux verification on this macOS machine.

## Run and original artifacts

- [GitHub Actions run 34709291624](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34709291624), attempt 1, push event on `codex/lean-mi07-maximal-modulus`.
- Immutable source revision: `f55777156432043de4201747a3759e0c6485e568`.
- MI-07 job: `103594995726`, completed successfully at `2026-09-12T17:56:43Z` on Ubuntu 24.04.5, Linux x86-64. Selection and checker-control jobs also completed successfully.

| Original ZIP | GitHub artifact ID | Verified SHA-256 |
| --- | --- | --- |
| [lean-MI-07.zip](lean-MI-07.zip) | `10302363244` | `540cd1eb9eb9726bef4d7474039982614eaa70359eef9750fd6c0f141c3b1380` |
| [lean-checker-controls.zip](lean-checker-controls.zip) | `10302347800` | `fed66a4de6e4a87d872843a282032107588c2d6eb8c8ec73a68e54c70c682439` |

I retrieved the original ZIP bytes through GitHub's artifact endpoint and matched
both digests and byte lengths to GitHub metadata. Every extracted member matches
its original ZIP member. The unmodified [run metadata](run-metadata.json),
[job stages](jobs.json), [artifact metadata](artifact-metadata.json), and
[full run log](run.log) are retained. These identify actual remote execution;
the GitHub log formatter labels some MI-07 lines `UNKNOWN STEP`, while the original
job metadata records the completed named steps.

## Source and tool binding

All **89 input files** listed by the actual harness result match both their Git
blobs at the immutable revision and the reviewed local bytes. All 18 files in the
author's frozen proof inventory still match. In particular, the statement boundary
and completed proof are identical to those approved by both final referees:

| Source | SHA-256 |
| --- | --- |
| `NLA/MI07/Definitions.lean` | `369e99eaf3df8a8bbfb214973129ab71fbc95445ba9d176e91d52bca3bc46bc5` |
| `Challenge.lean` | `62fee2804dc12a4ad7edecfa8c1dda2dc39acc2d94475d29805e8e55c3288a59` |
| `NUMERICAL_TARGETS.md` | `70272f54de929a95347db186b09b66d534313eed87ab7daa8e7fe5c8aaa8bd1e` |
| `NLA/MI07/FunctionalCalculus.lean` | `0963940bbed1818e7b8240129de01e832660f045dbfcabf578fb11d99949553a` |
| `NLA/MI07/Proof.lean` | `55f400e703994c3967a245495f6ad1ebc1999133cfd748185c81ef263178d8a3` |
| `Solution.lean` | `e460594ac018c8a1e966d88012b07c4ada8743957a414cbdfff8b790d54c07ee` |

[Final referee 1](../../reviews/proof-referee-1.md) has hash
`4c3c425d3b468e9277960f1ba4da9647f8884a9cd7e1495505ac355e8d14c7f7`;
[final referee 2](../../reviews/proof-referee-2.md) has hash
`277e1c9f98387b5a043440b0e26f345290bcb9f80adf229caaa278fc9da96c27`.

The actual receipt pins Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, and the Forsythe checker sources at
`8d1b0c0545a77b40245e84705aa7d273e6c81e62`. I independently checked and retained
all 58 locked source files. The committed source-lock hash is
`b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`.
The reconstructed noninteractive CI probe matches the receipt's hash
`31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803`.
Bootstrap logs show real Landrun, Comparator and lean4export builds; the receipt
enumerates their binary hashes, checked by the harness before execution. The
artifact retains these receipts, not the ephemeral Linux binaries themselves.

## Executed controls and proof phases

I inspected both the separate checker job and the controls executed inside MI-07's
own verification job. Both passed every required case:

- Real strict Landrun/Bubblewrap build and export probes: writes outside `.lake`, truncation, symlink escape, and creation denied; build writes inside `.lake` allowed; export writes there denied.
- Private user, PID, mount, network, IPC and UTS namespaces; inaccessible host process and loopback listener; denied AF_UNIX sockets; no effective capabilities; `no_new_privs`; rejected nested namespace write attempt. Both modes ran as non-root UID 1001.
- Four unsupported/wrong writable-path invocations rejected with exit 2, with original outer/export fixture contents unchanged.
- The actual `Comparator.runBuiltinKernel` accepted the honest inductive/quotient fixture, rejected an ill-typed raw proof at replay, and rejected the altered quotient declaration at its post-check.
- Five Comparator regression fixtures behaved as required, including genuine type/kind mismatch and illegal-axiom rejection; separate `sorryAx` and Lean 4.33.1 native-decision axiom fixtures were rejected at the expected axiom-check phase.

The actual [Comparator log](artifacts/lean-MI-07/verify-20260912T174904Z-4154/comparator.log)
builds and exports Challenge, then builds and exports Solution. Both actual export
lists contain exactly the configured seven `NLA.MI07` targets:

`modulus_eq_sqrt`, `maximalModulus_eq_of_tendsto`,
`root_limit_iff_spectralNorm`, `witness_moduli`, `witness_root_limits`,
`counterexample`, and `not_triangleConjecture`.

Definition replacement is disabled. Comparator's statement comparison and
transitive axiom check accepted the complete seven-target configuration. Its
actual default-kernel replay then printed `Lean default kernel accepts the solution`
and `Your solution is okay!`. All 23 printed axiom audits contain exactly
`propext`, `Classical.choice`, and `Quot.sound`. The seven intentional `sorry`
warnings occur only in Challenge; completed implementation modules have no such
warnings. The frozen proof's substantive kernel LeanCert point certificate and
its consumers were independently inspected by both final referees and are the same
bytes in this successful run.

The [dependency log](artifacts/lean-MI-07/verify-20260912T174904Z-4154/dependencies.log)
shows ten fresh clones checked out at the exact manifest revisions, including
LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The run downloaded and decompressed
**8,690 Mathlib cache artifacts**. Project Definitions, FunctionalCalculus, Proof
and Solution were built freshly inside the sandbox; the actual proof closure was
then replayed by Lean's default kernel. This was not a source rebuild of every
dependency and did not use a second independent kernel.

## Scope and reproduction

The mathematical scope remains the complete original constant-one maximal-modulus
triangle conjecture: arbitrary complex inputs and complex unitary pairs, genuine
PSD order, and actual root-sequence limits at all counterexample arguments. The
stronger informal no-finite-constant result is outside these exports. Comparator
checks formal correspondence and kernel validity; the English-to-Lean assessment
comes from the separate hash-bound statement and proof referees.

Mathematical authorship remains Matthew J. Colbrook. Formalization credit is
George Stepaniants, Department of Computing and Mathematical Sciences, California
Institute of Technology, Pasadena, California, USA. This is independent agent
review, not external human peer review or priority certification.

Reproduction requires the documented non-root Linux environment and pinned source
revision. Follow the repository's [Linux setup](../../../../../docs/lean/README.md),
then run the committed `tools/lean/bootstrap.sh` and `tools/lean/verify.sh` for
`matrix-inequalities-and-norms/MI-07/lean`. The [actual commands and result](artifacts/lean-MI-07/verify-20260912T174904Z-4154/result.json),
[source precheck](SOURCE-IDENTITY-PRECHECK.json),
[download identity](FETCH-IDENTITY.json), and
[independent machine-readable audit](AUDIT-CHECKS.json) retain the evidence.
Original bytes were preserved. No mathematical file, canonical status, project
metadata, commit, or remote state was changed by this audit.
