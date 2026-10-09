# MD-04 independent Lean-boundary review

Reviewer: `/root/infra_audit`, an OpenAI Codex AI agent independent of target author `/root`. Phase: lean-boundary. Verdict: **approve**.

I compared the complete actual live and frozen Lean definitions with the previously approved specification and full canonical README. I inspected the pinned Matrix definition (a two-index function), finite-sum notation (sum over Finset.univ), and the real-square-root definition where used. Local semantic source hashes are listed below; dependency meanings are additionally identified by their pinned package sources.

Actual Target is a closed Prop definition with one real C>0 preceding m,n,t and A. The natural bounds 1<=t<=m are exactly the integer sparsity range in the source, with positive dimensions and no case silently dropped.

The explicit real entry restriction is a disjunction Aij=0 or Aij=1, and the whole column sum is at most the real cast of t. This is literal incidence sparsity, not a cancellation-prone signed constraint.

The one n-entry sign vector is chosen after all columns are known, with each value exactly -1 or 1. The conclusion uses weak simultaneous row bounds by C*Real.sqrt(t). The inspected pinned Real.sqrt is the nonnegative square root and agrees with the standard root at nonnegative arguments; here t>=1 ensures positivity.

The final source imports Mathlib.Analysis.Real.Sqrt. I independently reran that final import version, both live and frozen, without the earlier deprecated-import warning. Frozen identity succeeds by rfl. This remains a statement, with no proof of the discrepancy conjecture or runtime assertion.

I independently elaborated the live and frozen modules with Lean 4.33.1 into a separate review build directory, then checked all three frozen identities by reflexivity. All commands exited 0. Each target axiom report contains only propext, Classical.choice, Quot.sound; #assert_statement and LeanCert #assert_trust kernel both passed. Retained logs are under lean-boundary-infra-audit-evidence/. These are local macOS development checks, not authoritative Linux Comparator execution and not proofs of Target. No numerical domain was reduced and no status promotion is supported by this review.

## Reviewed repository inputs

- `docs/lean/statements/MD-04/NUMERICAL_TARGETS.md`: `b1713525efa62b36a87fcad78a1718a0b8d5d3a30015b7bfa303d9bedc8d79d8`
- `docs/lean/statements/MD-04/ORIGINAL.md`: `a8be36a5217cb0b3031c8f87cfc25e5421ca78dd8c42ecc151219fa62eb8156e`
- `lean-statements/NLA/Statements/Infrastructure.lean`: `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37`
- `lean-statements/NLA/Statements/MD04.lean`: `c3536d295078f8223c82046f80f2d4a02eee5310cd07125013d303991ae41894`
- `lean-statements/Reviewed/MD04.lean`: `e7893db1c2656e6834009267738b6244c1b0e60dde582a525b0009ae079c7257`
- `lean-statements/lake-manifest.json`: `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`
- `lean-statements/lakefile.toml`: `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40`
- `lean-statements/lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`
- `matrix-discrepancy-and-optimization/MD-04/README.md`: `a8be36a5217cb0b3031c8f87cfc25e5421ca78dd8c42ecc151219fa62eb8156e`
- `docs/lean/statements/MD-04/reviews/lean-boundary-infra-audit-evidence/NLA-Statements-MD04.log`: `6cd3898376706d42f089990cb54e86796321674c6848d741c2814320c196250d`
- `docs/lean/statements/MD-04/reviews/lean-boundary-infra-audit-evidence/Reviewed-MD04.log`: `b687df1aeee8019957a195253cf0785efc5b0145c4136af3c0c7640b05c751c5`
- `docs/lean/statements/MD-04/reviews/lean-boundary-infra-audit-evidence/identity.log`: `2a3954627795f50423fd88b74045fed1aa6fcc709aa93aa4113bc4d4ac5d9a30`

## Inspected pinned dependency meaning

- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/LinearAlgebra/Matrix/Defs.lean`: `d4e5b5a2762eb91e47bd4d913ed72cd3fac2f7ebf40b32ae4dc0db7f34332d54`
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`: `2f39541f66288cb9ae9f77d97fd3656825a1dd1a4b5ca6a156f938d8fa1678a8`
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/Analysis/Real/Sqrt.lean`: `d6055b85eb3279133dd76eead0e1306032314c2c42c99b431b07e6aad654da86`
