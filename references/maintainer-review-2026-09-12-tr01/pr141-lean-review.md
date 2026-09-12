# PR141 independent Lean and semantic review

**Verdict: PASS for the pinned formal proof, its correspondence to the original TR-01 target, and the independently executed cold build, dependency/axiom/boundary/semantic checks, and fresh kernel replay. The optional graph recipe needs the documented auxiliary build below; this does not change the proof.**

Reviewed PR head: `2c7655f234bbb3b3134133ebae34eb479e9469e1`.
Pinned public proof source: [`yuningyang19/OpenProblemsInNLA_TR-01@ed21181197ac839eac95f549404f94e7e3aa6e10`](https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/tree/ed21181197ac839eac95f549404f94e7e3aa6e10).
The source manifest identifies the mathematical export commit as `e71f836451e1485c06ff478be97ac83f0ac44687`; the public repository pin above is the independently fetched and reviewed object.

## What the final theorem proves

I read the actual primitive definitions, `PaperV7/Expected.lean`, `PaperV7/Certification.lean`, the complete final assembly in `PaperV7/Main.lean`, exact-width arithmetic, sampling interfaces, and the spectral-to-squared-norm bridge. The three final declarations are `Problem56.PaperV7.certified_main`, `certified_explicit_main`, and `main_prescribed_width_ose`.

`WalshIndex m` has exactly `2^m` elements. The Walsh entries are the real characters divided by `sqrt(n)`. `rerandomizedSRHT` is exactly `sqrt(n/k) D1 F D2 F S`; `compressedGram` is `Vᵀ Ω Ωᵀ V`. Orthonormality means `VᵀV=I`, and the operator norm is the supremum over genuine Euclidean unit vectors, with a proved equality to mathlib's Euclidean operator norm.

The random law is uniform counting measure on the **entire Cartesian product** of both Boolean sign layers and all exact-cardinality `k`-subsets. This is the independent Rademacher/Rademacher/uniform-subset law. The supremum over fixed orthonormal frames lies outside the failure probability, so the conclusion is the fixed-subspace assertion, not a simultaneous assertion over all subspaces.

The final statement has only `1≤r≤n` and `0<ε<1`, and uses exactly `k=min(n,ceil(C*r/ε²))`. Its explicit universal constant is `200*2^20000 + 8196*576*4^24`. Full sample, smaller rank, and larger rank cases are all discharged; no extra rank cutoff, density condition, smaller selected width, or logarithmic width remains in the final theorem. The prescribed width satisfies `r≤k≤n`, so the sample space cannot be empty. The large constant does not make the theorem vacuous: there are non-full widths in both rank branches (exact integer witnesses recorded in the static evidence).

I wrote and compiled a separate Lean client, `pr141-independent-endpoint.lean`, deriving the literal `99/100` probability of both squared-norm inequalities simultaneously for every vector in the fixed frame at the prescribed width. It uses `certified_explicit_main`, the bounded-supremum lemma, and the spectral-event equivalence; it does not invoke the older selected-width conclusion. A second reviewer independently checked this client's quantifier and subspace interpretation. Passing between an arbitrary fixed real subspace and a fixed orthonormal basis is the standard deterministic finite-dimensional identification; Lean does not itself certify the English statement.

## Independent mechanical checks

- Downloaded the official [Lean4.33.0 release](https://github.com/leanprover/lean4/releases/tag/v4.33.0) for Apple Silicon and verified its archive against the release's published SHA-256, `db5274b669be270af048b5e4f1e0ce571df6750e411956b3e1e6fcc2012410c2`. The executable reports compiler commit `d8b18978322de05a8f3dba51ef03cf5461676c17`.
- Fetched all nine dependency sources; their Git revisions exactly match `lake-manifest.json` and tracked sources are clean. Mathlib is exactly [`db584cd6d46c92f209a44c0f1c829460d327499d`](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d). All 191 certified input hashes match. Independently traced the final Certification/Boundary import closure: 176 local source files, all covered by the manifest.
- Cold project build passed in **473.92 seconds**, with `.lake/build` absent at the start and `lake --no-cache build Problem56.PaperV7.Certification Problem56.PaperV7.BoundaryChecks`. Only the pinned official dependency cache was reused.
- The independent literal endpoint client compiled successfully. Its theorem and all three final declarations report exactly `propext`, `Classical.choice`, and `Quot.sound`.
- A separate reviewer-written traversal checked the final dependency closures (61,605 / 61,603 / 61,600 declarations). No unsafe or partial declaration and no additional axiom occurs. Source scans also found no proof placeholders, custom mathematical axioms, native-decide escape, or environment mutation.
- Fresh graph generation passed for 407 target theorems and 63,646 nodes. Independently parsed and compared **every target record and dependency-node record** against the published archive: identical. Final closures contain the new prescribed-width proof branches and do not contain `Problem56.main_universal_ose`, the older selected-width theorem.
- All seven isolated positive/negative semantic clients passed. In particular, the older selected-width and half-density statements are rejected at the new boundaries, while the current boundary and full-sample/epsilon extension clients succeed.
- Fresh kernel replay **PASS**: `lake env leanchecker --fresh -v Problem56.PaperV7.Certification` returned exit 0 with **700.29 seconds reported by the verifier’s `time.monotonic` timer**. The observed UTC interval between kernel-log creation and final write was longer and included substantial time without CPU execution. These are different clocks; neither measurement is asserted to be CPU time. The complete wrapper returned PASS with all 191 input hashes unchanged. Final checks reconfirmed all nine dependency revisions and clean tracked source states.

## Reproduction correction

The immutable companion's optional `verify.py --graph` recipe omits an auxiliary build. `CombinedAudit.lean` imports `Problem56.PaperV6.AuditTools`, which is absent from the Certification/Boundary build closure. On the cold clone I reproduced the exact failure: `AuditTools.olean ... does not exist` (exit 1). Running the command below successfully builds the helper, without changing any proof source:

```sh
lake build Problem56.PaperV6.AuditTools
python3 verify.py --graph --semantic --fresh-kernel
```

The default archived-graph verifier is unaffected. This is a documentation/reproduction issue; the corrected recipe must accompany any maintained full-replay instructions. The original `cold_rebuild.json` is also an initial failed checking-client receipt; `cold_recovery.json` records the successful recovery after a universe annotation repair. They must not be conflated. Both facts were reported to the integration reviewer.

## Scope and evidence

The formal source was rebuilt in `/private/tmp/nla-review-tensors/pr141-proof-build`; neither the PR worktree nor the pinned shared proof checkout was edited. No remote mutation was performed. The full manuscript proof was separately reviewed by the mathematical reviewer; this report covers the Lean endpoint, its correspondence, actual dependency trust, and the executed checks.

Lean's `--fresh` replay uses the same Lean kernel, not a second independent kernel implementation. I inspected `LeanChecker.lean` and `Lean/Replay.lean`: it replays safe declarations into an empty environment at trust level 0 and checks reconstructed constructors/recursors. The independent closure check above closes the skipped-unsafe/partial scope concern for the actual final theorems. Dependency source recompilation from scratch, novelty, and an independent implementation of Lean's kernel are not claimed.

Evidence is under `/private/tmp/nla-review-tensors`: `pr141-static-review-evidence.json`, `pr141-cold-build.json/.log`, `pr141-final-runtime.json`, `pr141-independent-endpoint.lean/.log`, `pr141-independent-closure.lean/.log`, `pr141-fresh-graph-independent.json`, and the exact missing-helper/helper-build logs. Fresh wrapper output and detailed graph/axiom/semantic/kernel logs are in the isolated clone's `lean/build/` directory. Completed wrapper receipt: `pr141-complete-verification.json`; final runtime and post-run source/dependency identity: `pr141-final-runtime.json`; fresh replay output: `pr141-fresh_kernel.log`. All claimed runtime checks above actually returned successfully.
