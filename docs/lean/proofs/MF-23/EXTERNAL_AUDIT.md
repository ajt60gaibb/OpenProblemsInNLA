# MF-23 external Lean proof audit

**Reviewer:** `/root/fr05_proof_audit`
**Date:** 2026-10-09
**Verdict:** The pinned external source contains a theorem proof for the sharp finite matrix-valued Crouzeix bound. Its source and statement were inspected, but no successful local or Linux kernel, Comparator, or LeanCert run has yet been reproduced for this revision. This is an external proof **claim**, not a certified local proof.

## Exact target and pinned source

The [canonical MF-23 page](../../../../matrix-functions-and-stability/MF-23/README.md) asks for the constant-two Euclidean operator-norm inequality for every positive base size `n`, positive coefficient size `m`, complex square matrix `A`, and finite matrix polynomial `F`. The maximum is over the full numerical range, including singleton and line-segment cases. Its block evaluation has coefficients on the first tensor factor: `Σ B_k ⊗ (A^k)`.

The source lock in `tools/statement_inventory.py` identifies `openai/math` revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, challenge `lean/ComparatorChallenges/DirectCrouzeix.lean`, and proof entry point `lean/OAI/Analysis/DirectCrouzeix/Main.lean`. A clean local checkout at that exact Git revision was inspected read-only. The [proof source](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/DirectCrouzeix/CompleteBound.lean) declares `OAI.DirectCrouzeix.complete_crouzeix : UniversalBound 2` with a proof body, not an axiom. `UniversalBound` quantifies over every such size, degree, matrix, and coefficient family. `rangeMaximum` is the supremum of the polynomial norm on the numerical range; the source proves the maximum is attained when `n > 0`.

The exact definition block from `Model.lean` through `UniversalBound` is byte-identical to the pinned Comparator challenge prefix (1,158 bytes). The 42 direct-proof source modules import only Mathlib or other modules in that direct-proof family. The import closure of `CompleteBound.lean` contains 41 of them. A scan of the 42 files found no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, or `sorryAx` token. This scan does not replace a transitive kernel or axiom audit.

The external theorem evaluates `Σ (A^k) ⊗ B_k`, whereas the canonical page uses `Σ B_k ⊗ (A^k)`. The two norms are mathematically equal under the factor-swap permutation, but the pinned challenge and proof both use the external order. A **Lean-proved permutation/norm bridge** is required before claiming literal formal proof of the canonical block-matrix statement. The original target and ID must remain unchanged.

## Feasibility and verification plan

The external source pins Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, and LeanCert `7f91b6eb3567437f6cfac03ed279706603ee22f4`. A Lean 4.34.1 binary is available locally at `/private/tmp/mf23-elan/toolchains/leanprover--lean4---v4.34.1/bin`; the inspected existing Mathlib cache is for a different revision. No fresh build or proof-trust run was made in this read-only audit.

The current NLA Linux verifier cannot be applied unchanged: it accepts a TOML Lakefile and a root Comparator configuration, and pins Lean 4.33.1 and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. The external project has `lakefile.lean`, a nested Comparator configuration, and the 4.34.1/7f91 pins. For a reproducible run:

1. Create a committed verification project that hash-locks and copies the exact pinned direct-proof import closure and the original challenge, with a minimal TOML Lakefile for the external Lean/Mathlib/LeanCert revisions. Keep the external Git revision, source hashes, and dependency manifest in its receipt. Select only `complete_crouzeix` for the MF-23 gate; upstream's additional `uniform_sharpness` is not part of this canonical target.
2. Add a separately reviewed 4.34.1 verifier profile. Retain the existing real Linux isolation, checker controls, immutable dependency checks, exact statement comparison, theorem-constant check, and standard-axiom allowlist. Run Comparator in a fresh Linux checkout before any solution build, then `#assert_trust kernel` and `#print axioms` on the actual proved theorem with the compatible pinned LeanCert. Treat any custom axiom, `sorryAx`, or failed check as failure.
3. Independently specify and review the canonical block-order bridge, implement it as a Lean theorem using the index-swap permutation, and run the same kernel/axiom checks on the bridged canonical conclusion. Record the full logs and pinned-source hashes. Do not import the external conclusion as an axiom or equate a declared signature with a checked proof.

Only successful receipts for these steps would close the external proof-verification gap. The source scan and upstream Comparator configuration are insufficient by themselves.

## Hash-bound audit inputs

The external paths below are relative to `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`; the local checkout had a clean worktree when inspected.

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-23/README.md` | `ce65d34a504156e52e9b917419b7f3a0bf605cea219a4b627197de470ffbe324` |
| `reviews/2026-10-08-claimed-solutions/MF-23.md` | `a627ad1e20f6d92fe31404dec6fbc5f494a65fdb3e4ca7e8d96ef64440ad594d` |
| `tools/statement_inventory.py` | `7133fe9124b36a7299977f3160fec829c175b378b0020a7ccf1c0e6ac8dc9df6` |
| External `lean/OAI/Analysis/DirectCrouzeix/Model.lean` | `3be01360e343e41c9712883d81e8845122ef13b2418640fa32c5e2fd22cdba84` |
| External `lean/OAI/Analysis/DirectCrouzeix/CompleteBound.lean` | `c8f0706d92662aaca2d1a26fe7647b3719035f72177d68fbf5b490028f12e891` |
| External `lean/ComparatorChallenges/DirectCrouzeix.lean` | `6aff79e03dee428cf5a677dba39da0fe14fe3d9a989a7e6d4bc0f3bf2a148d22` |
| External `lean/ComparatorChallenges/DirectCrouzeix.json` | `26346f0920c9862517f30c4c3a016a5aea03913cca5c151dd1a26eee3e7a9f82` |
| External `lean/lean-toolchain` | `d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b` |
| External `lean/lakefile.lean` | `4cca977ebece444b6c999d99755c1ad3c93119bafc127ea761f7f703c7279e74` |
| External `lean/lake-manifest.json` | `cf6105a25d9dca2f166b241d9191bd12c7e13305890dc9c4d0952351cccc0794` |
| External `lean/formalization.yaml` | `2dcbd0d6e6a22475f53d49bfdfcac9b6d2b470653c332a9f56522f5be166edb9` |

No canonical problem file, ID registry entry, or external Lean source was modified.
