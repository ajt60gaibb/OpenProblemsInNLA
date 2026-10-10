# MF-23 canonical Lean statement: exact mathematical and numerical review

**Prepared:** 2026-10-09 by `/root/mf23_canonical_bridge`. **Status:**
Awaiting an independent second review before any bridge implementation.

## Source lock and formal target

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-23/README.md` | `ce65d34a504156e52e9b917419b7f3a0bf605cea219a4b627197de470ffbe324` |
| pinned `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/DirectCrouzeix/Model.lean` | `3be01360e343e41c9712883d81e8845122ef13b2418640fa32c5e2fd22cdba84` |
| pinned `.../CompleteBound.lean` | `c8f0706d92662aaca2d1a26fe7647b3719035f72177d68fbf5b490028f12e891` |

The exact local statement is `NLA.MF23.Target` in
`matrix-functions-and-stability/MF-23/lean/CanonicalStatement.lean`.
`Target` unfolds to `CanonicalUniversalBound 2`. There is currently no
`NLA.Statements.MF23.Target` in the shared statement project; MF-23 is one of
its explicitly listed external-statement-source gaps.

The target quantifies over every natural `n,m,d` with `0 < n` and `0 < m`,
every complex square `n × n` matrix `A`, and every coefficient function
`B : Fin (d+1) → Matrix (Fin m) (Fin m) ℂ`. A finite polynomial with
matrix coefficients has exactly such a representation (trailing zeros are
allowed). No spectral or numerical-range regularity condition is added.

`blockEvaluation A B` is exactly `Σ_{k=0}^d B_k ⊗ A^k`, indexed by
`Fin m × Fin n`, so its `(i,r),(j,s)` entry is the `(r,s)` entry of
`Σ_k (B_k)_{ij} A^k = f_{ij}(A)`. It is therefore the README's
`mn × mn` block matrix `F(A)` with block indices first. The upstream
`OAI.DirectCrouzeix.tensorEvaluation` has factors in the reverse order
`Σ_k A^k ⊗ B_k`; equality of their operator norms still needs a Lean proof.

The right side is the *same* upstream `rangeMaximum A B` definition,
`sSup ((fun z => ‖Σ_k z^k • B_k‖) '' numericalRange A)`, using the Euclidean
operator norm scope for both matrix sizes. `numericalRange A` consists of all
`⟪u,Au⟫` with `‖u‖=1`; it includes point and line-segment ranges. Because
`0<n`, the upstream proof establishes that the supremum is attained, so this
is the README's maximum, not an alternative larger bound. The numerical
constant is the literal real `2`, independent of `n`, `m`, and `d`.

No theorem is asserted in `CanonicalStatement.lean`. An exact bridge must
prove `OAI.DirectCrouzeix.UniversalBound 2 → NLA.MF23.Target`, with the
tensor-factor swap preserving the L2 operator norm for every `A,B`.

## Specific fidelity questions for the independent reviewer

1. Does `Fin m × Fin n` and `B_k ⊗ A^k` match the published block indices?
2. Does the matrix `L2Operator` norm coincide with the README's Euclidean
   induced operator norm at both levels?
3. Does `rangeMaximum` describe exactly the full numerical range maximum,
   including degenerate numerical ranges and arbitrary finite degree?
4. Are the positive-size quantifiers and literal constant `2` intact?
5. Is the lack of a shared frozen MF-23 target correctly stated, with no
   claim that this local definition already proves the original problem?
