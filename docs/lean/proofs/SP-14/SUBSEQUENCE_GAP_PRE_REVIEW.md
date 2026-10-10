# SP-14 subsequence-gap lemma: pre-implementation review

**Author:** `/root/sp14_base_proof`, 9 October 2026. **Status:** proposed for independent review before Lean implementation. This reviews one proof bridge, not the source counterexample or the full Solved target.

## Exact proposed Lean contract

In `NLA.Statements.SP14`, for `a : Circle → ℂ`, `F : ℂ → ℂ`, `n : ℕ → ℕ`, and `δ : ℝ`, prove `Target` from these assumptions:

```lean
ha       : Continuous a
hinner   : ¬ InnerExtension a
houter   : ¬ OuterExtension a
hFcont   : Continuous F
hFcompact : HasCompactSupport F
hcanon   : Canonical a F = 0
hn       : StrictMono n
hδ       : 0 < δ
hgap     : ∀ᶠ j in atTop, δ ≤ (Empirical a F (n j)).re
```

The conclusion is the *existing* `Target := ¬ OriginalConjecture`, with `OriginalConjecture` and its full complex test class unchanged. The gap is an eventual lower bound on the real part of the actual characteristic-root average along genuine finite Toeplitz orders. It is not a redefinition of the target or an existence assumption disguised as an axiom.

## Mathematical check

Assume `OriginalConjecture`. Applying it to this `a` and `F` gives `Empirical a F k → Canonical a F = 0` as `k → ∞` along **all** natural orders. Strict increase of `n` implies `n j → ∞`, so composition gives `Empirical a F (n j) → 0`. Continuity of `Complex.re` gives `(Empirical a F (n j)).re → 0` in `ℝ`. Since `δ > 0`, the real interval `(-∞,δ)` is a neighborhood of zero, so eventually the real part is `< δ`. This contradicts `hgap`. The proof needs no assumption that the averages are real or nonnegative away from the selected subsequence.

For the manuscript's eventual witness, the explicit tent test `Φ` has `Canonical a Φ = 0` from its support being separated from the symbol range. If the source construction yields selected orders `n_j = 2m_j+1`, strictly increasing `m_j`, and the exact finite bound

```text
Re Empirical(a, Φ, n_j) ≥ floor(θ m_j)/(2m_j+1), θ = 2^(-10000),
```

then the right side tends to `θ/2 > 0`, allowing `δ = θ/4` and eventual `hgap`. This lemma itself proves neither the finite bound nor its limit, the tent-test properties, nor the existence of the source symbol. In particular it does **not** assert the false finite-order pointwise lower bound `θ/2`.

## Fidelity and trust scope

The lemma uses the frozen `SP14.lean` definitions: actual Fourier Toeplitz sections, characteristic-root multiset with algebraic multiplicity, continuous compactly supported complex tests, and the literal negation of the universal full-sequence conjecture. A kernel-checked proof would certify only the stated implication. It would leave the analytical construction and multiplicity proof open; no claim of a complete formal solution follows from it.
