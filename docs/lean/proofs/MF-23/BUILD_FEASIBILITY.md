# MF-23 pinned proof build feasibility

**Audit date:** 2026-10-09. **Result:** A fresh local macOS Lean 4.34.1 build of the pinned external `complete_crouzeix` proof passed. A pinned LeanCert kernel-mode audit of that theorem also passed, with only `propext`, `Classical.choice`, and `Quot.sound` in its transitive axiom report. This is **not** a Linux Comparator receipt and does not yet formalize the canonical tensor-factor order.

## Exact scratch inputs

The read-only source was clean `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a` at `/private/tmp/openai-math-mf23-audit`. I copied its 42 `lean/OAI/Analysis/DirectCrouzeix/*.lean` files, original `ComparatorChallenges/DirectCrouzeix.lean` and `.json`, and `lean-toolchain` into `/private/tmp/mf23-verification-fr05`. The copies were checked byte-for-byte against the pinned checkout. The upstream direct-proof directory Git tree is `5374ca34f6707460b2d2a3eb98b1ae7af6ea25ff`. The SHA-256 of sorted lines `relative/path SHA256(file)\n` for all 42 copied modules is `41850ed6e2636ce5a14104887b7f6fc65ad791681e05bd162093a8c8bcf41dea`.

The scratch `lakefile.toml` required only the direct proof's dependencies: LeanCert `7f91b6eb3567437f6cfac03ed279706603ee22f4` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, with `OAI.Analysis.DirectCrouzeix.+` as the Lean library glob. The generated manifest and checked package HEADs retained those exact revisions. The Lean executable reported `4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`.

| Scratch input | SHA-256 |
| --- | --- |
| `lean-toolchain` | `d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b` |
| `lakefile.toml` | `2c8f9059546d92a9cb07e0ad43512298953da8b4ec1a85fdd6cad0fdf53124b6` |
| `lake-manifest.json` | `7b646788d95f679f71434da2648140a2204ade8f583b21f4312753a65f4ea552` |
| Original `ComparatorChallenges/DirectCrouzeix.lean` | `6aff79e03dee428cf5a677dba39da0fe14fe3d9a989a7e6d4bc0f3bf2a148d22` |
| Original `ComparatorChallenges/DirectCrouzeix.json` | `26346f0920c9862517f30c4c3a016a5aea03913cca5c151dd1a26eee3e7a9f82` |
| `ProofAxioms.lean` | `8427339fdaf4ee245ed8c16fd96307d1ca96fdfb0007051ee0a672ea02741194` |
| `ProofTrustAudit.lean` | `f685037bdd6d59fac05e349258c29ead78c09c440fae188920d7342338abaf6b` |

## Commands and observed result

The sandboxed `lake update` initially failed at DNS resolution for `github.com`, before compiling anything. An approved retry fetched the exact public Git revisions and Mathlib cache. From the scratch project, with `ELAN_HOME=/private/tmp/mf23-elan` and that elan directory's `bin` on `PATH`, these commands then succeeded:

```text
lake update
lake build OAI.Analysis.DirectCrouzeix.CompleteBound
lake env lean ProofAxioms.lean
lake build LeanCert.Tactic.Verification
lake env lean ProofTrustAudit.lean
```

The proof build ended `Build completed successfully (8964 jobs)`. `ProofAxioms.lean` imported `CompleteBound`, checked `OAI.DirectCrouzeix.complete_crouzeix : OAI.DirectCrouzeix.UniversalBound 2`, and printed its axioms. `ProofTrustAudit.lean` imported the proved module and `LeanCert.Tactic.Verification`, set `leancert.trust` to `"kernel"`, required the declaration to be `.thmInfo`, ran `#assert_trust kernel OAI.DirectCrouzeix.complete_crouzeix`, and printed its axioms. Both axiom outputs were exactly `[propext, Classical.choice, Quot.sound]`; the LeanCert command exited successfully without a trust error. The first attempt at this audit failed solely because the LeanCert module had not yet been built; `lake build LeanCert.Tactic.Verification` fixed that missing `.olean`.

This local check establishes that the exact pinned external proof term is compilable and passes a local LeanCert kernel trust check with the pinned dependency set. It does not supply an isolated Linux Comparator run or a fresh independent audit of every imported Mathlib theorem. The scratch `.lake` occupied approximately 7.9 GB after fetching the 8,908-file Mathlib cache, which matters for CI disk planning.

## Minimal repository path to the remaining gates

1. Commit the 41-file `CompleteBound` import closure from the immutable upstream tree as a self-contained MF-23 proof project, together with the original challenge, a root Comparator configuration selecting `complete_crouzeix`, the exact TOML Lakefile/manifest/toolchain pins, and a source-hash lock. Keep `uniform_sharpness` out of the MF-23 selected target: sharpness is an additional upstream result. All copied proof bodies must remain byte-identical to the pinned source.
2. Add an independently reviewed Lean 4.34.1 profile to the Linux verification job. The current shared harness accepts only Lean 4.33.1, a different LeanCert pin, and TOML projects; the upstream project uses a Lean Lakefile and nested Comparator JSON. Preserve the real Linux isolation, checker negative controls, immutable dependency validation, proof-constant check, standard-axiom allowlist, and fresh Comparator-before-build ordering. A passing local macOS LeanCert audit does not substitute for this job.
3. Specify and independently review a Lean bridge from the external `Σ (A^k) ⊗ B_k` evaluation to the canonical `Σ B_k ⊗ (A^k)` block evaluation, prove the operator-norm equality under the factor-swap permutation, and certify the bridged canonical theorem. The current upstream Comparator challenge uses the external tensor order, so it alone does not close this fidelity gap.

No canonical README, permanent ID, external checkout, or shared harness was changed during this feasibility run.
