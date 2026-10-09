# TR-13 independent review of the all-width bridge

**Reviewer:** `/root`, 9 October 2026. **Verdict:** APPROVE the new local
all-width theorem as a faithful mathematical form of the published TR-13
target. This review does not claim a literal Lean proof of the separate
`NLA.Statements.TR13.Target` constant, because the statement and proof live
in separate Lake projects.

I compared the frozen `EqualFiveRanks` and `Target` with `EqualFiveWidths` and
`generic_width_equivalence`. Both quantify over every natural width `q`,
including zero, and compare ordinary width against symmetric, ordinary
border, symmetric border, and Vandermonde width. Both use every odd `m ≥ 5`
and `n ≥ 2`, one nonempty polynomial principal open in the full complex
moment space, and every Hankel tensor parametrized by a point in that open.
The local theorem adds no numerical bound or hypothesis to the target.

I inspected the five local decomposition definitions and their frozen
counterparts. Ordinary factors are unrestricted; symmetric summands carry
complex coefficients; Vandermonde parameter pairs remain nonzero even when a
padding coefficient is zero. Ordinary border approximants range over the
entire ambient tensor space. The local whole-function `Tendsto` and frozen
coordinatewise `Tendsto` are mathematically equivalent for this finite Pi
space, but that equivalence is not itself a theorem in the local project.
The pointwise versus function-equality decomposition forms, and the two
Hankel index expressions, have the same analogous source-level relationship.

The proof uses an actual Vandermonde width witness and a lower bound for
every ordinary-border witness. Its padding lemma extends the upper witness
to any larger `q` with zero coefficients and valid `(1,0)` pairs. Every
candidate width then forces `expectedRank m n ≤ q`, so padding and the
existing width implications establish all four equivalences. This avoids
inferring arbitrary-width equivalence from equality of infimum values alone.
I found no new assumption, axiom, `sorry`, native decision, or imported
challenge in the bridge's dependency path.

With the pinned Lean 4.33.1, Mathlib, and LeanCert project, I reran
`lake build NLA.TR13.ExactStatementBridge`. It succeeded (3413 jobs,
including cached dependencies); its `#assert_trust kernel` commands passed
and the final transitive axiom report lists only `propext`,
`Classical.choice`, and `Quot.sound`. The repository's fresh Linux Comparator
check is a separate pending gate. I then added the identical new theorem
signature to the separate `Challenge.lean` comparison hole, imported the
proved bridge into `Solution.lean`, and selected both final theorems in
`comparator.json`. `lake build Challenge Solution` passed (3417 jobs), and a
generated audit of the two selected Solution constants passed LeanCert kernel
trust with only the three standard axioms. The Challenge's two `sorry`s are
intentional comparison holes and are not imported by Solution. The literal
cross-package identification remains a documented limit.

## SHA-256 review inputs

| Repository-relative path | SHA-256 |
| --- | --- |
| `tensor-computations/TR-13/lean/NLA/TR13/WidthDefinitions.lean` | `1d354a06e9da5111ecd6ae7a7af80199f4d90f3136cd71d3a96823fc63360305` |
| `tensor-computations/TR-13/lean/NLA/TR13/ExactStatementBridge.lean` | `3a80b6f4b38e792bea5f8f639f7a982c487d0d585c77ab484bc43feccbc23f28` |
| `tensor-computations/TR-13/lean/NLA/TR13/Definitions.lean` | `f026f45877d8e2bfc94a96c8be0dece8a1f2a843d8c1b7249891d720c42240c7` |
| `lean-statements/NLA/Statements/TR13.lean` | `5b43b0a5410d91a7ec9a796a3e6d7cdd50f75929797d2eca4587cb2b0905a99d` |
| `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| `tensor-computations/TR-13/lean/Challenge.lean` | `8f736fde37cbf9086556e4427e2193feafafd26fdea0cefb2f48186c6dba4b04` |
| `tensor-computations/TR-13/lean/Solution.lean` | `8348d51d4e03280672393ca67ff015a32115bb9bfb063e7cca10f1f91733773c` |
| `tensor-computations/TR-13/lean/comparator.json` | `5e0d71f158aec50a818209001106fef0c8c0092c503b279bb0af59cb34a980cb` |

The generated temporary audit source had SHA-256
`ea747b87a4eb2528d5186965d3be845f0516a74186d2d9a2e72e10d4aaa52ff4`.
