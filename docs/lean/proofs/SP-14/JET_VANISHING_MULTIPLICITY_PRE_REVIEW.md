# SP-14 jet vanishing implies spectral multiplicity: pre-proof contract

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen for independent mathematical and Lean-signature review before implementation. The frozen original statement is `lean-statements/NLA/Statements/SP14.lean` (SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`); the source is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex` (SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`), especially the first-`h` equations in “Exact selection and the infinite symbol.” Permanent problem identity and negative `Target` remain unchanged.

The independently reviewed generic finite theorem `OddFrequencyToeplitzCharpoly.lean` (SHA-256 `aa6de57a4b247b81296d36fb2ed70f47d9c0b1863d0290792f6f3c16b3d4aff5`) gives, under exact `OddFourierSupport a`, the identity

\[
\chi_{2m+1,a}(X)=X\,R_{m,a}(X^2-1),\quad
R_{m,a}(t)=\operatorname{charpoly}(\mathrm{oddC}_{m,a}\mathrm{oddB}_{m,a})(t+1).
\]

The frozen `FourierCoefficient`, `Toeplitz`, matrix dimensions, and `oddJetPolynomial=R_{m,a}` are used without alteration. The new implication starts with a **hypothesis** that the source's jet equations have been solved; it does not solve them.

## Exact public claims

Define vanishing of the first `h` ordinary polynomial coefficients in the source coordinate `t=X²−1`:

```lean
def JetVanishing (a : Circle → ℂ) (m h : ℕ) : Prop :=
  ∀ d : ℕ, d < h → (oddJetPolynomial a m).coeff d = 0
```

Prove the following for all `m,h:ℕ` with the explicit source-relevant bound `h≤m` and actual even-frequency vanishing:

```lean
theorem jetVanishing_X_pow_dvd (a : Circle → ℂ) (m h : ℕ)
    (hJet : JetVanishing a m h) :
  (Polynomial.X : Polynomial ℂ) ^ h ∣ oddJetPolynomial a m

theorem jetVanishing_charpoly_factor (a : Circle → ℂ) (m h : ℕ)
    (hOdd : OddFourierSupport a) (hBound : h ≤ m)
    (hJet : JetVanishing a m h) :
  (Polynomial.X ^ 2 - 1 : Polynomial ℂ) ^ h ∣
    (Toeplitz a (2 * m + 1)).charpoly

theorem jetVanishing_roots_count (a : Circle → ℂ) (m h : ℕ)
    (hOdd : OddFourierSupport a) (hBound : h ≤ m)
    (hJet : JetVanishing a m h) :
  h ≤ ((Toeplitz a (2 * m + 1)).charpoly.roots.count (1 : ℂ)) ∧
  h ≤ ((Toeplitz a (2 * m + 1)).charpoly.roots.count (-1 : ℂ))
```

The last statement uses **algebraic multiplicity in the characteristic-root multiset**, exactly the object summed by the frozen `Empirical`. If a helper states the same inequalities using `Polynomial.rootMultiplicity`, it must also prove the displayed multiset-count theorem using `Polynomial.count_roots`. A mere `IsRoot` statement does not satisfy this contract.

Add a direct finite-source corollary by taking `a=finiteCorrectedSymbol u vCount pM pτ nM nQ nv` and its independently reviewed `OddFourierSupport`; it keeps `hJet` explicit and concludes the same two root-count inequalities. The exact dependent `Fin` family signature may be verbose but must not replace the actual corrected symbol by a surrogate polynomial. The source's selected value `h=⌊θm⌋` satisfies `h≤m` because `0<θ<1`; formalizing that numerical inequality is a later selection-specific obligation and is not silently assumed here.

## Proof and endpoint checks

Mathlib has `Polynomial.X_pow_dvd_iff`: `X^h ∣ R` iff every coefficient at `d<h` is zero. Use it for the exact ordinary coefficients, not derivatives or Taylor coefficients with factorial normalization. Composition of a polynomial divisibility witness by `X²−1` gives `(X²−1)^h ∣ R.comp(X²−1)`, and hence divisibility of `X·R.comp(X²−1)=χ` with no division by a value of `X`. In `ℂ[X]`,

\[
X^2-1=(X-1)(X+1),\qquad
(X^2-1)^h=(X-1)^h(X+1)^h.
\]

Thus both `(X-C(1:ℂ))^h` and `(X-C(-1:ℂ))^h` divide the **nonzero monic** characteristic polynomial. Apply `Polynomial.le_rootMultiplicity_iff` with `charpoly_monic.ne_zero`, then `Polynomial.count_roots` to obtain the two exact multiset count bounds. The values `1` and `-1` are distinct in `ℂ`; the theorem claims at least `h` occurrences at each, not exactly `h` and not a statement about geometric eigenspaces.

At `h=0`, `X^0=1` and both counts are at least zero, so the statements are valid without a positive-order exception. At `m=0`, the explicit `h≤m` forces `h=0`; the reviewed `oddQuotient_zero` makes the `1×1` characteristic polynomial `X`. The theorem does not state an impossible positive multiplicity at `m=0`. For `h>m`, the source-relevant theorem has no premise `hBound`; no implication about an inconsistent jet system is asserted. A separate degree argument could show first-`h` vanishing impossible because `R` is monic of degree `m`, but that argument is not needed for the source's choice and is outside this contract.

## Scope and remaining Target obligations

This is an exact **conditional** algebraic bridge from source jet equations to algebraic root counts. It does not prove any vector `v` satisfies those equations, that their Jacobian has full row rank, that stage norm budgets hold, or that the infinite stage construction exists. It also does not prove either one-sided nonextension, spectral range separation, a compactly supported test, or the canonical-versus-empirical gap required by the frozen `Target`. The base exterior symbol has an outer extension and is not the final counterexample.
