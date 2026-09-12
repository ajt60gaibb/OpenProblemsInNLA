# MI-23 independent Linux operational audit — 12 September 2026

**PASS for actual Linux verification of all eight MI-23 exports at commit `17194f9060609acae429e14d3dc3c4562b84f2bd`.** [Run 34716784038](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34716784038) completed successfully. All seven jobs and every top-level recorded step succeeded; the final metadata was updated at 20:29:38 UTC. The audited MI-23 job is `103615395920`, the separate checker-controls job is `103615395897`, and selection is `103615351787`.

Reviewer: independent agent `/root/leancert_examples`, who did not implement MI-23. The implementation author is `/root/formal_review_standards`. This audit reviews the actual remote execution, original artifacts, complete input identity and previously reviewed verifier. It does not replace the two mathematical proof reviews, certify all of Lean's implementation, claim human review, or give a general sandbox-security guarantee. I read the full project Comparator output, both sets of checker/control outputs and relevant raw job sections. The four inherited project jobs succeeded according to GitHub metadata; their mathematical artifacts are outside this audit.

## Original artifacts and immutable input identity

Both original ZIPs match GitHub's recorded SHA256 digests and the digests printed by the actual successful uploads. Every extracted file matches its original ZIP member; member sets agree exactly. Retrieval rejects absolute/traversing paths and symlinks.

| Artifact | ID | ZIP SHA256 | Files |
| --- | --- | --- | --- |
| `lean-MI-23` | `10304074963` | `9a7fad97c70da8ebcdca8880017a045ca6bd997118c23a44c4b652c79d3c4d2a` | 13 |
| `lean-checker-controls` | `10305385334` | `0c607888bd0d8bbaa903c75820f138056834a9f0c4adb2c27bb14122e8e120ee` | 10 |

The actual [project receipt](artifacts/lean-MI-23/verify-20260912T202130Z-4146/result.json) identifies this commit and records **133 input hashes**. I compared the complete receipt input set against the immutable Git tree, then compared every byte with both its Git blob and current worktree file. All 133 match and are retained under `source/matrix-inequalities-and-norms/MI-23/lean/`. This includes all definitions, implementations, statements, numerical targets, metadata, configurations, dependency pins, both statement reviews, both final reviews and their evidence.

The proof freeze SHA256 is `18fbf9a74e6006ca2b4159be62730c6df4faf38d472250b8ca1e7e54bf392ecb`. All 24 protected unchanged entries match; the remaining historical README is preserved byte-for-byte at the declared archive path, while the candidate README truthfully describes its later stage. All ten core mathematical hashes agree with both final reports. Final referee 1 is bound by `37985a31879f155da1b52d1cb9c955bb844d16edc862ccca327b3f0aaade8da1`, and referee 2 by `707f40dc07f789e0a201ebf2c158c86897e047ae898e7b776854f92d0f94ff02`. All four original canonical/source files also match their reviewed hashes and upstream base `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.

The [identity result](identity-verification.json), SHA256 `96c47cc781df706895e5b4eb9f25ba92132e56cc68f9adda053372664948657e`, records these full comparisons. No source, proof, configuration or review substitution was found.

## Actual mathematical build, export and acceptance

The [complete Comparator log](artifacts/lean-MI-23/verify-20260912T202130Z-4146/comparator.log) records separate Challenge and Solution builds, two actual declaration exports, successful **Lean default-kernel replay**, and successful statement comparison. The eight selected `NLA.MI23` exports are:

- `positive_powers_and_means`
- `product_eigenvalue_semantics`
- `squared_product_largest`
- `operator_norm_bounds`
- `witness_data`
- `witness_squared_gap`
- `counterexample`
- `not_generalizedGeometricMeanConjecture`

The exact config has no definition exceptions and permits only `propext`, `Classical.choice`, and `Quot.sound`. All **64 distinct internal/public axiom reports** contain exactly those names, and all corresponding source `#assert_trust kernel` assertions executed during elaboration. Challenge has its eight intended specification placeholders; Solution has no warnings. All seven project modules and Solution were built. The reported graph counts are **2710 Challenge jobs and 3152 Solution jobs**, not assertions that every dependency source was rebuilt.

The verified harness creates a new temporary project from ordinary tracked Git blobs, excludes tracked build artifacts, and checks trusted input hashes after dependency materialization, cache retrieval and Comparator. The log shows ten fresh dependency clones at the exact pinned revisions. The official Mathlib cache downloaded and decompressed **8690 files**. No old user-project output was reused; this is explicitly not a full-from-source Mathlib build.

Lean-action's optional built-in build/test/lint/nanoda/axiom sub-actions were configured to skip, as the raw setup logs show. Those skips are not evidence of verification. The later explicit `tools/lean/verify.sh` invocation actually performed the project build, strict sandbox, axiom checks, export, default-kernel replay and Comparator run documented above. The standalone `tools/lean/selftest.sh` also actually ran its controls.

The full semantic target and certificate consumption were approved by two separate mathematical referees. Their frozen proofs retain the original complex positive-definite matrix domain, both real parameter regions, actual CFC powers, complete characteristic-root multiplicities, genuine Euclidean norms and full log-majorization. The single actual kernel LeanCert point certificate is the exact positive rational gap, consumed through the norm and largest-eigenvalue contradictions. This operational command correctly declares that it does not itself perform semantic review; it did not substitute a finite scalar inequality for the original target.

## Actual isolation and rejection controls

The MI-23 job and independent checker-controls job each completed the full control sequence. Build and export run through the real strict Landrun/bubblewrap wrapper and Linux user service, with AF_UNIX denied. Both modes demonstrated private user, process, mount, network, IPC and UTS namespaces; the host parent was absent and unsignalable; host loopback and AF_UNIX sockets were blocked; capabilities were empty; `no_new_privs` was set; the sandbox UID was 1001.

Writes, truncation, creation and symlink escapes outside the permitted build area were denied. The designated build fixture was writable and the export fixture remained read-only. All four malformed/mis-scoped sandbox-option controls rejected with exit 2. **Nested-probe limit:** the adversarial bubblewrap executable ran, but UID-map creation was denied before the inner write command. The record supports that observed rejection, not a claim that the inner write executed or that every escape technique was tested.

Each sequence executed three raw default-kernel cases: the honest inductive/quotient fixture was accepted; the malformed proof was rejected by the kernel; and the quotient mismatch was rejected by the required post-check after kernel acceptance. Five Comparator fixtures built and exported both environments and reached their designated acceptance/rejection phases. Separate end-to-end `sorry` and nontrivial native-evaluation fixtures were built and exported, then rejected for `sorryAx` and `checked._native.native_decide.ax_1_1`. These were actual axiom rejections, not unrelated compilation or sandbox failures. The two successful control receipts contain identical tool receipts.

## Tool provenance and retained evidence

The actual receipts record Linux x86_64, Lean **4.33.1** at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Go **1.27.1**, and hashes of the built Comparator, exporter and Landrun executables. Both jobs successfully built those tools. I checked all **58** retained Forsythe tool-source files against the immutable source lock and reproduced the exact reviewed CI sandbox-probe adaptation.

The lock is `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`, at Forsythe commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`; the derived probe is `31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803`. The relevant harness/entry scripts match previously audited revision `214c142d6bfe0f0c338808f188062acbbad0fb19`; tools and workflow match this branch's upstream base. This reuses previously reviewed infrastructure and original remote execution records, without claiming a new local Linux run.

Selection actually passed its 30 metadata/selection tests and 12 harness tests and selected MI-23. The actual MI-23 metadata step passed schema and coverage validation for eight declarations. Original run/job/artifact metadata, ZIPs, raw logs, complete source snapshots, input/tool/control/axiom results and reproducible scripts are retained here. The outer `EVIDENCE-MANIFEST.json` includes **every nested manifest**, including nested files with that same basename; only the exact outer manifest itself is excluded from its self-hash list.

**No operational failure remains.** No mathematical, canonical status, ID, commit, push or PR change was made in this audit. Matthew J. Colbrook retains mathematical authorship; George Stepaniants retains formalization credit with his approved Caltech department affiliation and no George email added. Canonical promotion and publication wording remain a separately reviewed parent-agent action.
