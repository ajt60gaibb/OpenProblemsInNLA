# MD-03: independent Lean-boundary review

Reviewer: /root/statement_design (OpenAI Codex AI agent), independent of /root, the author.
Date: 2026-09-28. Phase: lean-boundary.
Verdict: **approve** for the exact bytes below. No mathematical corrections requested.

## Mathematical fidelity

1. Actual Target quantifies one positive real C before m,n,A; positive dimension guards and column sum-of-squares <=1 match the canonical domain without additional matrix assumptions.

2. The same real sign vector x follows A and is constrained coordinatewise to exactly -1 or 1. The final forall i bounds the absolute full row sum, expressing one simultaneous infinity-norm signing with weak inequality.

3. Finite sums use all elements of Fin m or Fin n, with coefficients and products in the real numbers. Matrix is the indexed function type, so no hidden matrix norm or order instance changes these explicit scalar formulas.

4. The source is a closed definition Target : Prop and contains no target theorem, axiom or placeholder. Kernel LeanCert options and assertion commands concern definition trust, not truth of this mathematical conjecture.

5. The live and frozen files were compared mechanically: the frozen source is exactly the live source with the documented leading comment and full namespace rename; mathematical bodies are identical.

6. All review_inputs files are hash-bound, including canonical README, complete ORIGINAL snapshot, approved specification, both Lean source namespaces, transitive local Infrastructure import and three dependency/toolchain pin files.

## Imported definitions inspected

- [Pinned Mathlib source](https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Matrix/Basic.lean): Matrix indexed-function meaning; ordinary real entries and explicit finite sums are used in these boundaries.

Local Infrastructure.lean was read in full: it requires a safe definition of closed type Prop and limits its transitive axioms to propext, Classical.choice and Quot.sound. It adds no mathematical premise to the target.

## Bound inputs

- docs/lean/statements/MD-03/NUMERICAL_TARGETS.md: bcf6594acf6ed308477b2d6c552558c235eaf84f57db44e75f208dc8fdef9075
- docs/lean/statements/MD-03/ORIGINAL.md: 3486bfa69ba99b106dfb059866d0f4fa3e0b9eac99276a05f911756639bbfd1e
- lean-statements/NLA/Statements/Infrastructure.lean: 8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37
- lean-statements/NLA/Statements/MD03.lean: 2638d903c1ccc478da9941f76d1903d838e4f6c5434ec1792dc1fbf811446b05
- lean-statements/Reviewed/MD03.lean: b86ff4b7f6268713024a85e81dd87793a04e288925b683a91febeee842426516
- lean-statements/lake-manifest.json: a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8
- lean-statements/lakefile.toml: 1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40
- lean-statements/lean-toolchain: 3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71
- matrix-discrepancy-and-optimization/MD-03/README.md: 3486bfa69ba99b106dfb059866d0f4fa3e0b9eac99276a05f911756639bbfd1e

## Limits

Independent source-level Lean-boundary fidelity review. The exact live and frozen source and imported mathematical meanings were inspected. This reviewer did not execute Lean or Comparator; those build/kernel/identity gates remain separate. No mathematical problem is proved and no cited informal solution is re-audited.
