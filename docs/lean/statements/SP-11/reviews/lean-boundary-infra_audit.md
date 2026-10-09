# SP-11 independent Lean-boundary review

Reviewer: `/root/infra_audit`, an OpenAI Codex AI agent independent of target author `/root`. Phase: lean-boundary. Verdict: **approve**.

I compared the complete actual live and frozen Lean definitions with the previously approved specification and full canonical README. I inspected the pinned SimpleGraph, minimum-degree, matrix-rank, matrix-product, Nat sInf, complex-number, and full finite-sum/product definitions as applicable; details appear in the findings. Local semantic source hashes are listed below; dependency meanings are additionally identified by their pinned package sources.

HasPattern requires real symmetry and the full off-diagonal equivalence Aij != 0 iff G.Adj i j, while leaving the diagonal unrestricted. It does not add PSD, SAP, connectedness or sign constraints. SimpleGraph in the inspected pinned source is a symmetric irreflexive relation, so it denotes exactly finite simple undirected graphs on Fin n.

MinimumDegree uses the actual pinned G.minDegree. Its definition is the minimum of all finite neighbor cardinalities, with a fallback only for an empty vertex type. Since Target requires 0<n, the type is nonempty and the fallback does not apply; isolated vertices and singleton graphs yield degree zero correctly.

The inspected A.rank is the real finrank of the range of A.mulVecLin and is at most its width n. Rank-nullity therefore identifies natural subtraction n-A.rank with dim ker A. The weak MinimumDegree inequality is exactly the canonical witness formulation, for every graph and every positive dimension.

The target is a closed Prop definition with concrete helper definitions. Its frozen namespace is a full byte-for-byte mathematical duplicate after namespace renaming, and independent equality elaboration succeeds. No proposition proof or numerical approximation is asserted.

I independently elaborated the live and frozen modules with Lean 4.33.1 into a separate review build directory, then checked all three frozen identities by reflexivity. All commands exited 0. Each target axiom report contains only propext, Classical.choice, Quot.sound; #assert_statement and LeanCert #assert_trust kernel both passed. Retained logs are under lean-boundary-infra-audit-evidence/. These are local macOS development checks, not authoritative Linux Comparator execution and not proofs of Target. No numerical domain was reduced and no status promotion is supported by this review.

## Reviewed repository inputs

- `docs/lean/statements/SP-11/NUMERICAL_TARGETS.md`: `a0cd200e8bd4dca2a9b0c7a690e874d67b1d4df9f7179ab9db738c4a8ee88b00`
- `docs/lean/statements/SP-11/ORIGINAL.md`: `8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865`
- `eigenvalues-and-inverse-problems/SP-11/README.md`: `8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865`
- `lean-statements/NLA/Statements/Infrastructure.lean`: `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37`
- `lean-statements/NLA/Statements/SP11.lean`: `7de112a24cb0b78894d495b840a77a58572cce574d5d77eda15381410c65b131`
- `lean-statements/Reviewed/SP11.lean`: `3a294de54f52a4287ed22b80d5b0721859154b642fe3c1ac62f7d4609be38222`
- `lean-statements/lake-manifest.json`: `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`
- `lean-statements/lakefile.toml`: `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40`
- `lean-statements/lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`
- `docs/lean/statements/SP-11/reviews/lean-boundary-infra-audit-evidence/NLA-Statements-SP11.log`: `ab03a7474f80d10fb9885b7b8c2d5853112ba1f61069229926b58bc6e11ee5c2`
- `docs/lean/statements/SP-11/reviews/lean-boundary-infra-audit-evidence/Reviewed-SP11.log`: `34f6983c7d669ab85f796d8ac64290e3f87e783bea56eac420f21fe8dbabcd6f`
- `docs/lean/statements/SP-11/reviews/lean-boundary-infra-audit-evidence/identity.log`: `2a3954627795f50423fd88b74045fed1aa6fcc709aa93aa4113bc4d4ac5d9a30`

## Inspected pinned dependency meaning

- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/LinearAlgebra/Matrix/Defs.lean`: `d4e5b5a2762eb91e47bd4d913ed72cd3fac2f7ebf40b32ae4dc0db7f34332d54`
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`: `2f39541f66288cb9ae9f77d97fd3656825a1dd1a4b5ca6a156f938d8fa1678a8`
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/Combinatorics/SimpleGraph/Basic.lean`: `e45d2248020078b2b2f853e6c6000af23cc0808e28ef54fda0471924bc4c9f8a`
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/Combinatorics/SimpleGraph/Finite.lean`: `1aa6eeffe77fd243fb2659ceb377843206bfa62fdeeae9e64741bedadd411934`
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/LinearAlgebra/Matrix/Rank.lean`: `67b4fa7bee02c1806f29562718bfb34c0e1f40af5ec6a91ef91cc33610657491`
