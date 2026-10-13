# SP-14 frozen Lean statement boundary: independent review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE the frozen live and reviewed Lean declarations as faithful statements of the complete original SP-14 conjecture and its negative Solved target. This approves statement identity only. Neither file proves `Target` or formalizes the particular counterexample witness.

## Mathematical fidelity

The canonical `## Statement` quantifies over every continuous complex symbol on the unit circle, assumes the absence of both one-sided annular analytic extensions, and requires the canonical eigenvalue distribution for every continuous compactly supported complex test along the **full sequence** of actual Toeplitz sections. `OriginalConjecture` preserves precisely this implication and quantifier order; `Target := ¬ OriginalConjecture` is its literal negative resolution. There is no Jordan-range, winding, normality, subsequence, or selected-test restriction.

`Circle.exp t` is defined in the pinned Mathlib as the circle element with complex value `Complex.exp (t * Complex.I)`, so the real interval integral from `0` to `2π` uses `e^{it}`, not a hidden `2πt` parametrization. `FourierCoefficient a k` multiplies by the complex cast of the real `1/(2π)` and by `Complex.exp (-(k : ℂ) * I * (t : ℂ))`, for every integer `k`. `Toeplitz a n` has index type `Fin n × Fin n` and entry `a_(row−column)`, with no wraparound or sign reversal.

`InnerExtension` existentially supplies an actual complex function differentiable on `r<‖z‖<1`, continuous on `r<‖z‖≤1`, and equal to `a` on the unit circle, for some `0<r<1`. `OuterExtension` analogously uses `1<‖z‖<R`, `1≤‖z‖<R`, and `R>1`. These relative continuity sets impose the intended boundary continuity from the relevant side while making no demand at the unrelated radius. The two negated predicates in `OriginalConjecture` preserve the original absence of both extensions.

`Empirical` maps the test through `(Toeplitz a n).charpoly.roots` as a **multiset**, sums all mapped roots, and divides by the actual order `n`; characteristic roots therefore retain algebraic multiplicity even for a nondiagonalizable section. `Canonical` is the corresponding `1/(2π)` complex interval integral of `F(a(e^{it}))`. The quantified test has both `Continuous F` and `HasCompactSupport F`. `Tendsto ... atTop` asserts the full natural-number sequence's complex limit. The definition at `n=0` uses division by zero in the field, but changes only one initial term and does not affect that limit.

The reviewed numerical contract's `θ=2^(-10000)`, `γ=2^(-1000)`, finite multiplicity fraction `⌊θm⌋/(2m+1)`, and `liminf≥θ/2` belong to a **future witness proof**, not to the original universal proposition. Their absence from these two statement files does not weaken `Target`. In particular, the README's informal “at least `θ/2` along” wording must not later become a false pointwise finite-order lemma; the approved numerical contract records the exact finite fraction and limiting consequence.

## Frozen boundary and checks

After replacing only the namespace name, the live and reviewed source bodies differ only by the reviewed file's leading freeze comment. An independent Lean audit imported both modules and proved by `rfl` that their `OriginalConjecture` declarations are equal and their `Target` declarations are equal. This checks definitional identity, beyond a textual comparison. Both source files' own `#assert_statement` and `#assert_trust kernel` commands compiled directly under pinned Lean 4.33.1 and LeanCert kernel mode. `lake build NLA.Statements.SP14 Reviewed.SP14` passed. The transitive axioms printed for each `Target` are exactly `[propext, Classical.choice, Quot.sound]`. The files define propositions; these checks do not establish the truth of `Target`.

## SHA-256 of reviewed inputs

| Input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Statements/SP14.lean`** | **`2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`** |
| **`lean-statements/Reviewed/SP14.lean`** | **`bff729881ee4591e73290e57fb1910e15b3cb3421044e5cdc1a3e5b44e1e5c52`** |
| Canonical `eigenvalues-and-inverse-problems/SP-14/README.md` | `9d0c6376080838ea50e8736cb4249276c06a528479fb9c9f565cc7747a485075` |
| `docs/lean/statements/SP-14/NUMERICAL_TARGETS.md` | `f507ad236fc7c9e9547ce23ebe74ddffac84872d66648cc8b543ff89d6f39efc` |
| Earlier `docs/lean/proofs/SP-14/STATEMENT_INDEPENDENT_REVIEW.md` | `4eb5983573dae403fb3a0daaedd14371c1e656683a25497261f5f7a78ef9665b` |
| Pinned Mathlib `Analysis/Complex/Circle.lean` | `235156c199e71932971e06154290c0f6d60ffd69986927f7c45efa3018e18d13` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| Independent `/private/tmp/sp14-boundary-independent-audit.lean` | `6fd614d599bd7b23296a9030d3ee274d6f59b601c1bc69c1c3343ceb6d83399c` |

Changing either formal declaration or any mathematical source above reopens the corresponding fidelity check.
