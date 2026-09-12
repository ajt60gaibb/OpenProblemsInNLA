# MI-19 actual Linux verification audit

**Verdict: PASS for the complete MI-19 formalization at `cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7`.** The actual per-project Comparator run rebuilt both environments, compared the two selected theorem statements and their used definitions, enforced the standard-three axiom whitelist, and replayed the solution with Lean's default kernel. Its input hashes match the previously approved mathematical proof exactly. No required operational check was skipped or failed.

Reviewer: independent Codex agent `/root/formal_review_standards`, 12 September 2026. This reviewer did not author the MI-19 statements or proof and previously performed its independent second proof review. The reviewer did author the original generic verification driver; this report is an audit of the actual Linux execution and its bound inputs, not a purported independent second code review of that driver. The infrastructure and its later root-authored CI adaptations received separately scoped reviews. No mathematical source, canonical entry, branch, or status was changed during this audit.

## Run identity and archive integrity

- Repository and branch: `sgstepaniants/OpenProblemsInNLA`, `codex/lean-mi19-q-permanent`.
- [Run 34703363593](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34703363593), exact head `cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7`, push event created `2026-09-12T15:49:01Z`, completed successfully `15:56:20Z`.
- [Actual MI-19 verification job 103578942995](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34703363593/job/103578942995) succeeded. Its fresh verification step ran from `15:50:09Z` to `15:56:13Z`. The select and separate checker-control jobs also succeeded; none of these three jobs was skipped.
- The actual manifest validator reported `PASS (2 declarations)`. The select job passed 20 metadata/project-selection tests and 12 harness tests.

The original artifact ZIPs were independently downloaded through GitHub's API, hashed locally, matched to the API's SHA-256 digests, and compared byte-for-byte with every extracted file:

| Artifact | ID | Original ZIP SHA-256 | Files |
| --- | --- | --- | --- |
| `lean-MI-19` | `10301476532` | `bf7872acf3574fa91a7f464df0b871386fd27f67697b581ed40d78b12c55bd53` | 13 |
| `lean-checker-controls` | `10300591986` | `26c2c1ceca53ff13c40fd8c27ef720209ab877523c72216f3ab63de79084db2c` | 10 |

The archives, [run metadata](run-metadata.json), [artifact metadata](artifact-metadata.json), full [run log](run.log), extracted logs, and exact source copies are retained here. [Identity verification](identity-verification.json) records the checks. GitHub reports expiration on 11 December 2026; the retained ZIPs and hashes preserve the evidence independently of that expiration.

## Input and tool identities

All **37** recorded project input hashes were independently recomputed from the exact Git commit, checked against the current worktree bytes, and confirmed to be the complete tracked project file set. The statement and implementation hashes coincide with the independently approved boundary:

| Mathematical input | SHA-256 |
| --- | --- |
| Definitions | `170e406d1f6bf0ca60e5b65998308b030cf08cc0def51c25c9860524ad3441ac` |
| Challenge | `9c838a34cbff20eceb5e842eeca77c310bccb442843925343a7827a1020063cb` |
| Numerical obligations | `cd93a4cefb529b69755c10bae600718442e0e6b8749c37df87c6dabec9b751aa` |
| Proof | `53ab38bfef6e52f6c039eba5056659be43f9b8e7a7b3453a62769dc3f0ef3c37` |
| Solution | `18bf53ea1d745b4488718297559c3c77e3bcb902596b9c9aae5f448bdcb800c4` |

The checked configuration names exactly `NLA.MI19.counterexample` and `NLA.MI19.not_subsetConjecture`, allows no definition holes, and permits only `propext`, `Classical.choice`, and `Quot.sound`. It matches both the previously reviewed configuration and the actual result receipt.

The workflow, harness, source lock, and CI toolchain are byte-for-byte unchanged from independently operationally audited infrastructure commit `214c142d6bfe0f0c338808f188062acbbad0fb19`. The source-lock SHA-256 is `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`, pinning the attributed Forsythe sources to `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. The actual CI probe hash is `31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803`, matching the reviewed adaptation. The actual fresh 20-job build of Comparator and lean4export, and the Landrun build, completed successfully. The Linux binary hashes are recorded in the receipt and match the preceding successful infrastructure run; this audit does not claim to have independently rebuilt those Linux executables on this macOS review host.

## Fresh project, dependencies, and actual proof check

The receipt and invocation identify a fresh temporary project, `nla-fresh-proof-sj32yqcg/project`. Inspection of the exact harness confirms that it copies ordinary tracked Git blobs, rejects tracked build artifacts and symlinks, starts without the project's local `.lake`, and rechecks the input hashes after dependency materialization, cache download, and Comparator completion. It does not build Solution before Comparator's own ordered Challenge/export/Solution/export process.

The [dependency log](artifacts/lean-MI-19/verify-20260912T155027Z-3941/dependencies.log) records fresh clones of all ten locked dependencies and checks out every exact manifest revision. In particular, LeanCert is `621a43d7cf21f87872392a01e874f2f1dbddc926` and mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`. Each checkout line was independently matched to the manifest. The [mathlib cache log](artifacts/lean-MI-19/verify-20260912T155027Z-3941/mathlib-cache.log) transparently records downloading and decompressing 8690 upstream cache files. This is fresh dependency materialization with the pinned mathlib cache, **not a claim to rebuild every dependency from source**. The problem Definitions, Challenge, Proof, and Solution were actually rebuilt in the isolated project.

The [actual Comparator log](artifacts/lean-MI-19/verify-20260912T155027Z-3941/comparator.log) shows, in order:

1. A fresh Challenge build, including Definitions, completed on a 2159-job graph. Its two deliberate placeholder warnings are confined to Challenge.
2. Both requested declarations and their environment were exported from Challenge.
3. The actual Solution build, including LeanCert and `NLA.MI19.Proof`, completed on a 3640-job graph. The mathematical Solution has no sorry warning.
4. All five inspected internal declarations and both public exports printed precisely the standard-three axiom set. The corresponding source `#assert_trust kernel` commands were part of this successful build.
5. Both requested declarations were exported from Solution. The checker printed `Lean default kernel accepts the solution` followed by `Your solution is okay!` and final `EXIT_STATUS=0`.

The [result receipt](artifacts/lean-MI-19/verify-20260912T155027Z-3941/result.json) records `comparator-accepted` on those exact inputs. The source's LeanCert scalar certificate uses explicit kernel mode and contributes to the strict counterexample. Compiling the tactic library's available native-bridge module does not add native trust to a theorem; the actual target closures and the separate native-rejection test establish the relevant distinction.

## Isolation and rejection controls actually executed

The full controls ran twice, once in the checker job and again as a prerequisite in the MI-19 verification job. I checked both artifact sets, including expected rejection phases rather than merely accepting nonzero status. [Control verification](control-verification.json) records this audit.

Both build and export sandbox modes ran as UID 1001, with private user/PID/mount/network/IPC/UTS namespaces, absent host-parent access, denied host signal lookup, unreachable host loopback, denied AF_UNIX creation, no effective capabilities, and `no_new_privs` set. Both modes rejected outer writes, truncation, read-only-plus-truncation, symlink escape, and outer creation. The designated `.lake` write succeeded only in build mode; export writes and truncation were denied. Final fixtures were checked unchanged. All four malformed sandbox arguments were rejected with exit two. The bounded user-service preflight also passed.

The nested Bubblewrap executable actually started and was rejected at UID-map setup in both modes. Its inner write payload was not reached. This is successful earlier containment, not evidence that an inner write was attempted after a successfully created nested namespace; the distinct direct-write controls did execute their write attempts.

All three raw kernel controls passed: honest declarations with inductives and quotients accepted, a raw `True.intro` proof of `False` rejected at kernel replay, and a fake exported `Quot.lift` rejected by the quotient post-check. All five full Comparator fixtures built and exported both environments and returned their exact expected outcomes: genuine match accepted; constant-kind mismatch, custom axiom, the retained second custom-axiom fixture, and theorem-type mismatch rejected. The additional sorry and native fixtures likewise reached build/export and were rejected for `sorryAx` and the actual generated axiom `checked._native.native_decide.ax_1_1`, respectively.

## Promotion scope

No operational mismatch or incomplete required gate remains for the two selected MI-19 exports at this immutable revision. Together with the two independently approved statement reviews and two independently approved final proof reviews on these same hashes, this evidence supports promoting the **complete original MI-19 target** to `Lean verified` after linking the retained proof and logs in the repository's required form.

The formalized resolution is negative: an admissible complex PSD order-four witness at `q=7/8`, with the interior singleton and original full inversion ordering, yields full minus restricted sum `-3235575/16384`, and refutes the full universal conjecture. Exact rank, the all-parameter polynomial identities, and persistence under positive diagonal perturbations are outside the formalized theorem claims. Matthew J. Colbrook retains mathematical credit; George Stepaniants receives formalization credit with his approved Caltech Computing and Mathematical Sciences affiliation and no email.

Comparator checks formal identity, permitted axioms, and kernel replay; it does not itself certify the translation from the informal problem. That fidelity is supplied by the independent semantic reviews. These operational controls are evidence for this configured Linux execution, not a proof of operating-system security against every possible exploit. The proof commit's publication files accurately recorded Linux as pending when written; the proposed promotion must add this subsequent successful record rather than rewriting that historical evidence. This reviewer has not performed the promotion or made a pull request.
