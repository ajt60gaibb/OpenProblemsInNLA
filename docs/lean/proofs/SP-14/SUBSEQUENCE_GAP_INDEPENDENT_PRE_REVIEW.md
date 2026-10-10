# SP-14 subsequence-gap lemma: independent pre-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE the exact conditional lemma contract in `SUBSEQUENCE_GAP_PRE_REVIEW.md` for Lean implementation. This is an implication from a supplied counterexample witness and gap, not a proof of the SP-14 counterexample or `Target` without premises.

The proposed conclusion is the frozen `NLA.Statements.SP14.Target := ¬ OriginalConjecture`. The supplied symbol is continuous and lacks both actual one-sided annular extensions; the supplied complex test is continuous and compactly supported. These are exactly the premises that let one instantiate the original universal conjecture. `Canonical a F = 0` and `∀ᶠ j in atTop, δ ≤ (Empirical a F (n j)).re` with `δ>0` refer to the original canonical integral and actual characteristic-root empirical average. They do not replace the all-test, full-sequence target by a restricted proposition.

If the conjecture held, its full-sequence complex limit applied to this `a,F` would be zero. `StrictMono n` on natural numbers makes `n j → ∞`; subsequence composition and continuity of `Complex.re` would force the selected real parts to tend to zero. Their eventual lower bound by a fixed positive `δ` is impossible. No reality or sign assumption on other empirical averages is required. The unspecified values at order zero have no effect on the limit.

The source's selected orders `n_j=2m_j+1` and exact finite bound `⌊θm_j⌋/(2m_j+1)`, `θ=2^(-10000)`, yield an eventual gap such as `δ=θ/4` because the lower-bound fraction tends to `θ/2` as `m_j→∞`. This does **not** claim a pointwise finite-order `θ/2` bound. The lemma leaves the hard obligations to construct `a`, `F`, and `m_j`, establish the annular-extension failures, tent-test separation, algebraic multiplicities and finite lower bound, and prove the positive limiting gap. Its generic `StrictMono n` premise is consistent with, and weaker in form than, the source's particular odd selected orders.

| Reviewed input | SHA-256 |
| --- | --- |
| **`docs/lean/proofs/SP-14/SUBSEQUENCE_GAP_PRE_REVIEW.md`** | **`01babfcb793e4bbf51ba810fad419a485a7b7c49d8bbb09fabe616c8d4c33f78`** |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Canonical `eigenvalues-and-inverse-problems/SP-14/README.md` | `9d0c6376080838ea50e8736cb4249276c06a528479fb9c9f565cc7747a485075` |
| Approved `docs/lean/statements/SP-14/NUMERICAL_TARGETS.md` | `f507ad236fc7c9e9547ce23ebe74ddffac84872d66648cc8b543ff89d6f39efc` |

This verdict is prior to implementation. A changed contract or frozen statement requires a new review.
