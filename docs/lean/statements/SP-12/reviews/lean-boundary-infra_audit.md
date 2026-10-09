# SP-12 independent Lean-boundary review

Reviewer: `/root/infra_audit`, an OpenAI Codex AI agent independent of target author `/root`. Phase: lean-boundary. Verdict: **approve**.

I compared the complete actual live and frozen Lean definitions with the previously approved specification and full canonical README. I inspected the pinned SimpleGraph, minimum-degree, matrix-rank, matrix-product, Nat sInf, complex-number, and full finite-sum/product definitions as applicable; details appear in the findings. Local semantic source hashes are listed below; dependency meanings are additionally identified by their pinned package sources.

HasPattern is the exact real symmetric graph pattern with unrestricted diagonal. NonnegativeQuadraticForm quantifies every real vector and uses the complete double sum xi*Aij*xj, exactly x-transpose A x; together with HasPattern symmetry this is real positive semidefiniteness.

StrongArnold quantifies every real symmetric X. The inspected Matrix multiplication instance makes A*X=0 the ordinary matrix product constraint. The separate all-entry Ai j*Xi j=0 is the Hadamard constraint, while Xi i=0 is precisely I Hadamard X=0. These constraints conclude the full matrix equality X=0.

ChromaticNumber is the sInf of actual proper-coloring cardinalities, not a supplied graph invariant. The inspected Nat sInf uses Nat.find on a nonempty set. The identity coloring gives c=n because SimpleGraph has no loops; for n>0 there is no function Fin n to Fin 0. Hence the number is the positive minimum proper color count and its natural subtraction by one is exact.

As in SP11, A.rank is the real range finrank and n-A.rank is nullity. The single existential matrix simultaneously meets pattern, PSD, SAP and the required chromatic nullity bound. No connectedness, vertex-criticality, rank positivity, or nonempty-edge requirement is introduced. Feasible nullities have an attained finite maximum, as checked in the specification review, so the witness statement is the original maximum inequality.

Live and frozen definitions independently elaborate and compare by rfl. The mathematical target is defined, not proved, and all trust assertions concern only its complete axiom closure.

I independently elaborated the live and frozen modules with Lean 4.33.1 into a separate review build directory, then checked all three frozen identities by reflexivity. All commands exited 0. Each target axiom report contains only propext, Classical.choice, Quot.sound; #assert_statement and LeanCert #assert_trust kernel both passed. Retained logs are under lean-boundary-infra-audit-evidence/. These are local macOS development checks, not authoritative Linux Comparator execution and not proofs of Target. No numerical domain was reduced and no status promotion is supported by this review.

## Reviewed repository inputs

- `docs/lean/statements/SP-12/NUMERICAL_TARGETS.md`: `6dae7d486ecaeab1903b31e816e34f57fef417ef15627574f4c4a307b902cae7`
- `docs/lean/statements/SP-12/ORIGINAL.md`: `cdc8003bc5160604408ce6b95c344a4ea1b9bfbf8af0f99ae1e8e016648d53e1`
- `eigenvalues-and-inverse-problems/SP-12/README.md`: `cdc8003bc5160604408ce6b95c344a4ea1b9bfbf8af0f99ae1e8e016648d53e1`
- `lean-statements/NLA/Statements/Infrastructure.lean`: `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37`
- `lean-statements/NLA/Statements/SP12.lean`: `c41acae980a06e3f1e8d59e2c552f85812c521ed5e66473b74e01542bfd80f2b`
- `lean-statements/Reviewed/SP12.lean`: `adfb89f439ce5e2959aaeeb4b3ef6c432bf38f364567765715fdd8f9a1510d86`
- `lean-statements/lake-manifest.json`: `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`
- `lean-statements/lakefile.toml`: `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40`
- `lean-statements/lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`
- `docs/lean/statements/SP-12/reviews/lean-boundary-infra-audit-evidence/NLA-Statements-SP12.log`: `eb3a68507b1ffa62f8d56cb7d7b59298a74edb6bdcebe330f9e6634f3a4b1ce3`
- `docs/lean/statements/SP-12/reviews/lean-boundary-infra-audit-evidence/Reviewed-SP12.log`: `40ae315348592f1d7605ccddde311bbe84e4a3d4b4a24fe97432c5e10104e459`
- `docs/lean/statements/SP-12/reviews/lean-boundary-infra-audit-evidence/identity.log`: `2a3954627795f50423fd88b74045fed1aa6fcc709aa93aa4113bc4d4ac5d9a30`

## Inspected pinned dependency meaning

- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/LinearAlgebra/Matrix/Defs.lean`: `d4e5b5a2762eb91e47bd4d913ed72cd3fac2f7ebf40b32ae4dc0db7f34332d54`
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`: `2f39541f66288cb9ae9f77d97fd3656825a1dd1a4b5ca6a156f938d8fa1678a8`
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/Combinatorics/SimpleGraph/Basic.lean`: `e45d2248020078b2b2f853e6c6000af23cc0808e28ef54fda0471924bc4c9f8a`
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/Order/Lattice/Nat.lean`: `f231ec6e610f9b0f38eaea3fd48730f3d8068eeeadd03668564846bf4dd072c3`
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/Data/Matrix/Mul.lean`: `9ce6ecd0751e977f58fc47d6f271dff381e59868474a6955730ff07a99aa0e6b`
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/LinearAlgebra/Matrix/Rank.lean`: `67b4fa7bee02c1806f29562718bfb34c0e1f40af5ec6a91ef91cc33610657491`
