# TR-13 exact-statement bridge correspondence and build record

**Author/checker:** `/root/proof_inventory` (AI agent), 9 October 2026.
**Scope:** This agent authored `NLA/TR13/ExactStatementBridge.lean` and checked
its source correspondence and local build. This is **not an independent review
of the new module**. The earlier independent [statement review](statement-review-proof_inventory.md)
concerns the existing solution statement; another reviewer must inspect this
new bridge before treating its correspondence as independently approved.

## Why the bridge is needed

The local `generic_rank_equality` proves equality of five `sInf` rank values
at the expected rank. The frozen shared `NLA.Statements.TR13.Target` asks for
equivalence of four width predicates with ordinary width for **every** natural
width `q`, including zero. The new `NLA/TR13/WidthDefinitions.lean` imports
only `Definitions.lean` and defines local `EqualFiveWidths` with that latter
quantifier and conjunction shape. Both Challenge and Solution can import this
proposition without importing the bridge proof. `generic_width_equivalence`
in `ExactStatementBridge.lean` proves it on a
nonempty principal Zariski-open set for every odd `m ≥ 5` and `n ≥ 2`.

The proof does not derive width equivalence from equality of infima alone.
It uses the existing actual Vandermonde decomposition at
`expectedRank m n` and the lower bound for **every** ordinary-border width.
`vandermondeRankAtMost_mono` pads a decomposition to any larger `q` with zero
coefficients and valid projective pairs `(1,0)`. The proof then takes each
candidate ordinary or border width through the lower bound, pads the upper
witness to that width, and uses the existing implications between the four
decomposition kinds. No source theorem, target axiom, placeholder, or native
decision step is introduced. The construction works when `q = 0`.

## Correspondence with the frozen shared proposition

The shared frozen source uses `NLA.Statements.TR13.EqualFiveRanks`; the local
bridge uses `NLA.TR13.EqualFiveWidths`. Their terms correspond as follows.
These are mathematical/source correspondences, not separately formalized
cross-package equivalence theorems.

| Frozen shared term | Local bridge term | Exact meaning |
| --- | --- | --- |
| `TR14.Hankel h` | `hankel h` | Both index `h` by the sum of zero-based entries `i k`. The source's one-based sum minus `m` is exactly this index. The finite-bound proofs differ only as proof terms. |
| `TR14.OrdinaryWidth H q` | `OrdinaryRankAtMost q T` | Both assert a width-`q` sum of arbitrary complex pure products over all `m` factors. The shared form is pointwise; the local form is equality of coordinate functions. Function extensionality relates them. |
| `TR14.SymmetricWidth H q` | `SymmetricRankAtMost q T` | Both assert a width-`q` sum of complex scalar multiples of one vector's `m`-fold pure power. The local `c • symmetricTensor` is pointwise scalar multiplication, equal to the shared `c * ∏`. |
| `OrdinaryBorderWidth H q` | `OrdinaryBorderRankAtMost q T` | Both permit approximating sequences of arbitrary full ambient complex tensors of ordinary width `q`. The local `Tendsto U atTop (nhds T)` in a finite Pi space is equivalent to the shared convergence at every coordinate; no Hankel or symmetry restriction enters. |
| `SymmetricBorderWidth H q` | `SymmetricBorderRankAtMost q T` | Both require symmetric width `q` for each approximant, but do not require Hankel approximants. The same finite Pi versus coordinatewise topology equivalence applies. |
| `VandermondeWidth H q` | `VandermondeRankAtMost q T` | Both use `a^(n−1−i) b^i` for every coordinate, including `a=0` or `b=0`, with a nonzero projective pair. The local `(a,b) ≠ (0,0)` is equivalent to the shared `a ≠ 0 ∨ b ≠ 0`. Both allow zero coefficients for padding. |

Both `EqualFiveRanks` and `EqualFiveWidths` compare ordinary width with each
of the other four at the same natural `q`, and quantify over every `q`. The
polynomial parameter type is the full complex moment vector of length
`m*(n−1)+1`. The new theorem explicitly supplies a point where the polynomial
does not vanish; thus its principal open is nonempty, as the frozen target
requires. The polynomial is built by multiplying the existing nonzero upper
and lower certificates. No expected-rank formula is added as an assumption.

The local proof project and the shared statement package are separate pinned
Lake projects. This module proves the **local analogue** and does not import
or literally prove `NLA.Statements.TR13.Target`. A future selected export or
Comparator boundary must account for the term correspondences above in a
self-contained comparison; the local build alone cannot establish literal
cross-package definitional identity.

## Local verification

From `tensor-computations/TR-13/lean`, using Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`:

```sh
lake build NLA.TR13.ExactStatementBridge
```

Exit code 0: `Build completed successfully (3413 jobs)`. The module runs
LeanCert `#assert_trust kernel` on the padding theorem, the general
width-equivalence theorem, and `generic_width_equivalence`; all pass. Its
`#print axioms generic_width_equivalence` reports only
`[propext, Classical.choice, Quot.sound]`. A separate `lake env lean` import
checked the exported signature. A source scan found no `axiom`, `sorry`,
`admit`, `unsafe`, `opaque`, `constant`, `native_decide`, `run_tac`, or
`implemented_by`. No `Solution.lean`, `Challenge.lean`, or `comparator.json`
was edited by this work.

## SHA-256 of inspected inputs

| Repository-relative path | SHA-256 |
| --- | --- |
| `tensor-computations/TR-13/README.md` | `fa34e46c5869e28c9f198a1aa78a4a5e026ba99dcbe67ce10d3410e426f7f70b` |
| `tensor-computations/TR-13/lean/NLA/TR13/WidthDefinitions.lean` | `1d354a06e9da5111ecd6ae7a7af80199f4d90f3136cd71d3a96823fc63360305` |
| `tensor-computations/TR-13/lean/NLA/TR13/ExactStatementBridge.lean` | `3a80b6f4b38e792bea5f8f639f7a982c487d0d585c77ab484bc43feccbc23f28` |
| `tensor-computations/TR-13/lean/NLA/TR13/Definitions.lean` | `f026f45877d8e2bfc94a96c8be0dece8a1f2a843d8c1b7249891d720c42240c7` |
| `tensor-computations/TR-13/lean/NLA/TR13/Upper.lean` | `f02165febe8d37e531ba767e2bfdc3bd8467c68a39556e4e55b67bcb8867e8d9` |
| `tensor-computations/TR-13/lean/NLA/TR13/Lower.lean` | `55a8d56cb1c5afed1894da71e92eb77a0fc002825fe97d32563489e285733b76` |
| `tensor-computations/TR-13/lean/NLA/TR13/RankComparison.lean` | `555d6e6ee61f29a4ddc3c199a1ee9ab71ea6a132961f92d2ce352a9817fdd6e3` |
| `lean-statements/NLA/Statements/TR13.lean` | `5b43b0a5410d91a7ec9a796a3e6d7cdd50f75929797d2eca4587cb2b0905a99d` |
| `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| `lean-statements/Reviewed/TR13.lean` | `8b876a24f87eeecdb983ca6044b7548aa629db0a3f0fe9c3878516cba8b29b16` |
| `lean-statements/Reviewed/TR14.lean` | `9990f933adf8a8593f6a1fcc70aeeaeed8abdfe05e7738bd5b538e719ad9c356` |
| `tensor-computations/TR-13/lean/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `tensor-computations/TR-13/lean/lakefile.toml` | `aded4a942bb9a98929e564c1ac8464a7f8f43c08e4e0d6d2833a9b91f60b6ff5` |
| `tensor-computations/TR-13/lean/lake-manifest.json` | `431a2cba1225a9ab974b43b11a366f735f4c5b6621039b72c2044a8451bda293` |
