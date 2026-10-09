# PF-04: independent Lean-boundary review

Reviewer: /root/statement_design (OpenAI Codex AI agent), independent of /root, the author.
Date: 2026-09-28. Phase: lean-boundary.
Verdict: **approve** for the exact bytes below. No mathematical corrections requested.

## Mathematical fidelity

1. HasFactor uses a real 6-by-r indexed matrix B, entrywise nonnegativity, and A_ij=sum_k B_ik B_jk. This is the full exact Gram definition; symmetry of A follows from the formula rather than a restrictive premise.

2. CompletelyPositive quantifies over every natural finite width r, including zero. The empty finite sum is zero, preserving the source cp-rank convention at the zero matrix.

3. The universal target conjunct supplies width exactly 9 to every CP matrix; zero padding makes this the at-most-nine statement. The separate existential conjunct requires a CP witness with no factor of every width r<9, preserving sharpness.

4. No rank, support, nonsingularity, strict positivity, approximation tolerance or computational restriction replaces the full order-six domain.

5. All three declarations are explicit safe proposition definitions, with no target theorem, axiom or placeholder. Local infrastructure performs trust checks but does not supply mathematical assumptions.

6. The live and frozen files were compared mechanically: the frozen source is exactly the live source with the documented leading comment and full namespace rename; mathematical bodies are identical.

7. All review_inputs files are hash-bound, including canonical README, complete ORIGINAL snapshot, approved specification, both Lean source namespaces, transitive local Infrastructure import and three dependency/toolchain pin files.

## Imported definitions inspected

- [Pinned Mathlib source](https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Matrix/Basic.lean): Matrix indexed-function meaning; ordinary real entries and explicit finite sums are used in these boundaries.

Local Infrastructure.lean was read in full: it requires a safe definition of closed type Prop and limits its transitive axioms to propext, Classical.choice and Quot.sound. It adds no mathematical premise to the target.

## Bound inputs

- docs/lean/statements/PF-04/NUMERICAL_TARGETS.md: 3294326a93bf021afac3caae3349b01e6f5c23425060cbc22c8cba8c08af1e02
- docs/lean/statements/PF-04/ORIGINAL.md: acbf30a432e4ee1898661c05a9efc2f24f9ec32183da33836315b58e6c46e08a
- lean-statements/NLA/Statements/Infrastructure.lean: 8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37
- lean-statements/NLA/Statements/PF04.lean: 0b374f4b5efdc770cf678264b99085bb4961ad2993b3edae725db0b1908fa01f
- lean-statements/Reviewed/PF04.lean: 4111d1beaadf78565c112f7a29cfb89960479d4f48566f5b1660c165ff8cc41f
- lean-statements/lake-manifest.json: a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8
- lean-statements/lakefile.toml: 1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40
- lean-statements/lean-toolchain: 3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71
- nonnegative-and-positive-factorizations/PF-04/README.md: acbf30a432e4ee1898661c05a9efc2f24f9ec32183da33836315b58e6c46e08a

## Limits

Independent source-level Lean-boundary fidelity review. The exact live and frozen source and imported mathematical meanings were inspected. This reviewer did not execute Lean or Comparator; those build/kernel/identity gates remain separate. No mathematical problem is proved and no cited informal solution is re-audited.
