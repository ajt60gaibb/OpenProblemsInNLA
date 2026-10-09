# MD-04: independent Lean-boundary review

Reviewer: /root/statement_design (OpenAI Codex AI agent), independent of /root, the author.
Date: 2026-09-28. Phase: lean-boundary.
Verdict: **approve** for the exact bytes below. No mathematical corrections requested.

## Mathematical fidelity

1. Actual Target quantifies a single positive real C before positive m,n and natural t with 1<=t<=m. This exactly retains the canonical parameter domain.

2. Every real matrix entry is explicitly 0 or 1. Each full column sum is bounded by the real cast of t; there is no signed cancellation or alternative sparsity definition.

3. The post-matrix sign vector has every coordinate -1 or 1, and all rows obey C * Real.sqrt(t) non-strictly. The pinned Real.sqrt is the nonnegative square root, defined through NNReal.sqrt after toNNReal; for these positive natural casts it is precisely the source square root.

4. No online, algorithmic, positivity-of-A-beyond-incidence or higher-sparsity restriction was introduced. The zero-column and t=1,t=m cases remain covered.

5. Target is a proposition definition only. No catalog target proof, axiom or placeholder has been added, and the assertion commands do not prove the target.

6. The live and frozen files were compared mechanically: the frozen source is exactly the live source with the documented leading comment and full namespace rename; mathematical bodies are identical.

7. All review_inputs files are hash-bound, including canonical README, complete ORIGINAL snapshot, approved specification, both Lean source namespaces, transitive local Infrastructure import and three dependency/toolchain pin files.

## Imported definitions inspected

- [Pinned Mathlib source](https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Matrix/Basic.lean): Matrix indexed-function meaning; ordinary real entries and explicit finite sums are used in these boundaries.
- [Pinned Mathlib source](https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Real/Sqrt.lean): Real.sqrt definition and sqrt_nonneg, mul_self_sqrt; relevant to MD-04 only.

Local Infrastructure.lean was read in full: it requires a safe definition of closed type Prop and limits its transitive axioms to propext, Classical.choice and Quot.sound. It adds no mathematical premise to the target.

## Bound inputs

- docs/lean/statements/MD-04/NUMERICAL_TARGETS.md: b1713525efa62b36a87fcad78a1718a0b8d5d3a30015b7bfa303d9bedc8d79d8
- docs/lean/statements/MD-04/ORIGINAL.md: a8be36a5217cb0b3031c8f87cfc25e5421ca78dd8c42ecc151219fa62eb8156e
- lean-statements/NLA/Statements/Infrastructure.lean: 8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37
- lean-statements/NLA/Statements/MD04.lean: c3536d295078f8223c82046f80f2d4a02eee5310cd07125013d303991ae41894
- lean-statements/Reviewed/MD04.lean: e7893db1c2656e6834009267738b6244c1b0e60dde582a525b0009ae079c7257
- lean-statements/lake-manifest.json: a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8
- lean-statements/lakefile.toml: 1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40
- lean-statements/lean-toolchain: 3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71
- matrix-discrepancy-and-optimization/MD-04/README.md: a8be36a5217cb0b3031c8f87cfc25e5421ca78dd8c42ecc151219fa62eb8156e

## Limits

Independent source-level Lean-boundary fidelity review. The exact live and frozen source and imported mathematical meanings were inspected. This reviewer did not execute Lean or Comparator; those build/kernel/identity gates remain separate. No mathematical problem is proved and no cited informal solution is re-audited.
