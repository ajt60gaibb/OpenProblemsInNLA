# SP-11: independent Lean-boundary review

Reviewer: /root/statement_design (OpenAI Codex AI agent), independent of author /root.
Date: 2026-09-28. Verdict: **approve**. No mathematical correction requested.

## Source and meaning checks

1. The actual HasPattern explicitly requires real symmetry and the nonzero-if-and-only-if-adjacency condition at distinct indices. Both directions are present; diagonal entries are unrestricted.

2. Target quantifies every positive natural n and every SimpleGraph on Fin n, then one real matrix. No PSD, SAP, connectedness, edge-sign, rank or graph restriction was imported from the stronger resolution.

3. MinimumDegree uses the pinned SimpleGraph.minDegree. Its source is the minimum of all finite neighbor degrees, defaulting to zero only on empty vertex types. The target n>0 excludes that default branch; isolated vertices and n=1 are handled correctly.

4. Matrix.rank in the pinned dependency is real finrank of the range of A.mulVecLin. It is bounded by n; rank-nullity makes n-A.rank exactly the real kernel dimension, so the natural inequality matches the canonical nullity bound.

5. Every declaration is an actual mathematical definition, with classical decidability used for finite graph adjacency. There is no target axiom, target proof or assumed invariant.

6. Live and frozen mathematical bodies agree exactly after the documented namespace substitution and leading comment. Canonical source and ORIGINAL snapshot are byte-identical. All local review_inputs and immutable pins are hash-bound below.

7. Infrastructure.lean was read in full. It checks safe definition, closed type Prop and permitted axiom closure. It supplies no mathematical hypothesis; kernel trust assertions do not assert target truth.

## Bound review inputs

- docs/lean/statements/SP-11/NUMERICAL_TARGETS.md: a0cd200e8bd4dca2a9b0c7a690e874d67b1d4df9f7179ab9db738c4a8ee88b00
- docs/lean/statements/SP-11/ORIGINAL.md: 8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865
- eigenvalues-and-inverse-problems/SP-11/README.md: 8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865
- lean-statements/NLA/Statements/Infrastructure.lean: 8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37
- lean-statements/NLA/Statements/SP11.lean: 7de112a24cb0b78894d495b840a77a58572cce574d5d77eda15381410c65b131
- lean-statements/Reviewed/SP11.lean: 3a294de54f52a4287ed22b80d5b0721859154b642fe3c1ac62f7d4609be38222
- lean-statements/lake-manifest.json: a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8
- lean-statements/lakefile.toml: 1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40
- lean-statements/lean-toolchain: 3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71

## Imported source inspected

- /Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Basic.lean: e45d2248020078b2b2f853e6c6000af23cc0808e28ef54fda0471924bc4c9f8a, dependency revision 0df444a360eaa60ab8c11dca51a86af692955474
- /Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Finite.lean: 1aa6eeffe77fd243fb2659ceb377843206bfa62fdeeae9e64741bedadd411934, dependency revision 0df444a360eaa60ab8c11dca51a86af692955474
- /Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Rank.lean: 67b4fa7bee02c1806f29562718bfb34c0e1f40af5ec6a91ef91cc33610657491, dependency revision 0df444a360eaa60ab8c11dca51a86af692955474

## Development evidence inspected

{
  "path": "/private/tmp/nla-statements-development/SP11.log",
  "sha256": "0d3e7e248cc69155040da498a625430e1277c95fbb6dc3baf250b4d677a137a7",
  "observed": "Author-generated development log reports only propext, Classical.choice and Quot.sound for Target. Reviewer read the log but did not execute the compilation."
}

## Limits

Independent Lean-boundary source/fidelity review. Pinned imported meanings and author-generated axiom logs were inspected; this reviewer did not run Lean or Comparator. This certifies neither the truth of the catalog proposition nor a new audit of its cited informal proof. Authoritative build and Linux Comparator gates remain separate.
