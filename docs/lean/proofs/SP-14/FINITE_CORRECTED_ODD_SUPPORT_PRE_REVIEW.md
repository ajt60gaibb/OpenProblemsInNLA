# SP-14 finite corrected symbols retain odd Fourier support: pre-proof contract

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen for independent mathematical and Lean-signature review before implementation. The frozen original statement is `lean-statements/NLA/Statements/SP14.lean` (SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`), and the mathematical source is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex` (SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`). The source forms finite stage backgrounds from the exterior base symbol and finitely many positive `Q_j` and restored negative `D_j` packets under `a(z)=zg(z²)`. Permanent problem identity and the negative `Target` stay unchanged.

This contract depends on the audited `BaseExteriorPattern.lean`, `PositivePacketInvisibility.lean` (SHA-256 `90df55a41491c60d442df3679d1808c2c77a66d8e66fe8dbffe940151c3c8d1f`), and frozen `NegativeRestorationInvisibility.lean` (SHA-256 `318f9d1b2a0af4bf8355aa78afc7440b9c83449b6b2f5de8bd1bc361ac36e476`). It also uses the independently pre-reviewed, currently unintegrated `OddFrequencyToeplitzCharpoly.lean` (SHA-256 `aa6de57a4b247b81296d36fb2ed70f47d9c0b1863d0290792f6f3c16b3d4aff5`) only after that source receives its final audit. Its exact premise is `OddFourierSupport a := ∀p:ℤ, FourierCoefficient a (2*p)=0` under the frozen real interval integral.

## Exact public claims

First prove exact support and continuity for each constituent, for every index and parameter including zero:

```lean
theorem oddSupport_baseExterior : OddFourierSupport baseExteriorSymbol

theorem oddSupport_positivePacket (τ : ℂ) (m : ℕ) :
  OddFourierSupport (positivePacket τ m)

theorem continuous_restoredNegativePacket (m q : ℕ) (v : Fin q → ℂ) :
  Continuous (restoredNegativePacket m q v)

theorem oddSupport_restoredNegativePacket (m q : ℕ) (v : Fin q → ℂ) :
  OddFourierSupport (restoredNegativePacket m q v)
```

Define the exact finite corrected symbol with arbitrary finite numbers of source-form packets:

```lean
noncomputable def finiteCorrectedSymbol (u vCount : ℕ)
    (pM : Fin u → ℕ) (pτ : Fin u → ℂ)
    (nM nQ : Fin vCount → ℕ)
    (nv : ∀ j : Fin vCount, Fin (nQ j) → ℂ)
    (z : Circle) : ℂ :=
  baseExteriorSymbol z +
    (∑ i : Fin u, positivePacket (pτ i) (pM i) z) +
    (∑ j : Fin vCount, restoredNegativePacket (nM j) (nQ j) (nv j) z)

theorem continuous_finiteCorrectedSymbol (u vCount : ℕ)
    (pM : Fin u → ℕ) (pτ : Fin u → ℂ)
    (nM nQ : Fin vCount → ℕ)
    (nv : ∀ j : Fin vCount, Fin (nQ j) → ℂ) :
  Continuous (finiteCorrectedSymbol u vCount pM pτ nM nQ nv)

theorem oddSupport_finiteCorrectedSymbol (u vCount : ℕ)
    (pM : Fin u → ℕ) (pτ : Fin u → ℂ)
    (nM nQ : Fin vCount → ℕ)
    (nv : ∀ j : Fin vCount, Fin (nQ j) → ℂ) :
  OddFourierSupport (finiteCorrectedSymbol u vCount pM pτ nM nQ nv)

theorem finiteCorrectedSymbol_odd_charpoly_in_jet (u vCount m : ℕ)
    (pM : Fin u → ℕ) (pτ : Fin u → ℂ)
    (nM nQ : Fin vCount → ℕ)
    (nv : ∀ j : Fin vCount, Fin (nQ j) → ℂ) :
  (Toeplitz (finiteCorrectedSymbol u vCount pM pτ nM nQ nv)
      (2 * m + 1)).charpoly =
    Polynomial.X *
      (oddJetPolynomial (finiteCorrectedSymbol u vCount pM pτ nM nQ nv) m).comp
        (Polynomial.X ^ 2 - 1)
```

The final identity is a direct use of the reviewed generic odd-frequency theorem once the explicit support is proved. It does not impose stage separation or norm budgets: odd Fourier support is an algebraic property of each packet's frequencies, independent of whether a packet is visible to a particular Toeplitz section.

## Exact proof route and endpoints

`oddSupport_baseExterior` is the even half of the independently audited `baseExteriorSymbol_fourier_pattern`; `continuous_baseExteriorSymbol` is already proved. The two positive modes are `2m+1` and `2m+3`; neither equals `2p` for any integers `m≥0,p`, by `positivePacket_fourier`. The negative raw modes `1+2(d-m)` for `d:Fin q` and restoring modes `1-2(m+1+r)` for `0≤r≤m` are also odd for every `m,q`, including `m=0` and `q=0`. To prove their actual frozen Fourier integrals vanish at even `k`, expand the finite sums and use `FourierCoefficient_circle_mode` with the exact negative exponential and `1/(2π)` normalization. Since each finite mode is continuous, every use of interval-integral additivity has interval-integrability witnesses. Do not use linearity of totalized integrals for an arbitrary background.

The public `continuous_restoredNegativePacket` is needed for finite-sum additivity; it follows from the finite Laurent definitions on `Circle`, whose complex powers have no zero-domain problem. State a helper `OddFourierSupport` closure under addition **with both continuous premises**, and prove finite sums by induction. The base is continuous, every positive packet is finite and continuous, every negative restored packet is finite and continuous. At `u=vCount=0`, both sums are empty and `finiteCorrectedSymbol` is exactly `baseExteriorSymbol`; at `q=0`, `negativeL` and its endpoint value are zero, so the restored negative packet is zero. At `m=0`, `K_0(s)=-s^{-1}`, whose actual symbol contribution is mode `-1`; its Fourier support remains odd.

The Fin-indexed family generalizes the source's consecutive stage labels without changing the packets. The source's real `v_d` are included via `ℝ→ℂ`, and its `q=3m/8` and `m≥8m_prev` choices are specializations, but neither support nor continuity needs those inequalities. The proof must preserve the definitions of `positivePacket`, `negativeL`, `restoringK`, and `restoredNegativePacket` exactly; it must not replace them by a surrogate symbol.

## Scope and remaining Target obligations

This proves only continuity, even-Fourier vanishing, and the consequent finite odd-order characteristic-polynomial shape for arbitrary finite packet combinations. It does not prove any jet coefficients vanish, choose a regular correcting vector, establish positive asymptotic multiplicity at `±1`, control stage norms, construct the infinite limit, or show either one-sided nonextension. It does not supply the compactly supported test, canonical integral, or positive empirical gap required by the frozen `Target`. The base exterior symbol has an outer extension and is not itself the counterexample.
