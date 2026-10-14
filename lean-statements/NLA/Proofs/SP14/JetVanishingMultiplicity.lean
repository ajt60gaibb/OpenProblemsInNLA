import NLA.Proofs.SP14.FiniteCorrectedOddSupport

/-!
The source's exact first-jet equations imply algebraic multiplicity at
both excluded points in each selected odd Toeplitz section. The jet
equations remain hypotheses; this module does not construct their roots.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped Polynomial

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

/-- The first `h` ordinary coefficients in the source coordinate `t=w²-1`
vanish. This is exactly the finite polynomial equation system. -/
def JetVanishing (a : Circle → ℂ) (m h : ℕ) : Prop :=
  ∀ d : ℕ, d < h → (oddJetPolynomial a m).coeff d = 0

theorem jetVanishing_X_pow_dvd (a : Circle → ℂ) (m h : ℕ)
    (hJet : JetVanishing a m h) :
    (Polynomial.X : Polynomial ℂ) ^ h ∣ oddJetPolynomial a m := by
  exact Polynomial.X_pow_dvd_iff.mpr hJet

/-- A zero `h`-jet yields the exact characteristic-polynomial factor,
including the value `X=0` and `h=0`. -/
theorem jetVanishing_charpoly_factor (a : Circle → ℂ) (m h : ℕ)
    (hOdd : OddFourierSupport a) (_hBound : h ≤ m)
    (hJet : JetVanishing a m h) :
    (Polynomial.X ^ 2 - 1 : Polynomial ℂ) ^ h ∣
      (Toeplitz a (2 * m + 1)).charpoly := by
  obtain ⟨Q, hQ⟩ := jetVanishing_X_pow_dvd a m h hJet
  refine ⟨Polynomial.X * Q.comp (Polynomial.X ^ 2 - 1), ?_⟩
  rw [toeplitz_odd_charpoly_in_jet a m hOdd, hQ]
  simp [Polynomial.mul_comp, Polynomial.pow_comp]
  ring

/-- The factor gives at least `h` algebraic copies of each of `1` and
`-1` in the actual characteristic-root multiset. -/
theorem jetVanishing_roots_count (a : Circle → ℂ) (m h : ℕ)
    (hOdd : OddFourierSupport a) (hBound : h ≤ m)
    (hJet : JetVanishing a m h) :
    h ≤ ((Toeplitz a (2 * m + 1)).charpoly.roots.count (1 : ℂ)) ∧
    h ≤ ((Toeplitz a (2 * m + 1)).charpoly.roots.count (-1 : ℂ)) := by
  classical
  let χ := (Toeplitz a (2 * m + 1)).charpoly
  have hdiv : (Polynomial.X ^ 2 - 1 : Polynomial ℂ) ^ h ∣ χ :=
    jetVanishing_charpoly_factor a m h hOdd hBound hJet
  obtain ⟨Q, hQ⟩ := hdiv
  have hfactor : (Polynomial.X ^ 2 - 1 : Polynomial ℂ) =
      (Polynomial.X - 1) * (Polynomial.X + 1) := by ring
  have hχ : χ = (Polynomial.X - 1) ^ h * (Polynomial.X + 1) ^ h * Q := by
    rw [hQ, hfactor, mul_pow]
  have hplus : (Polynomial.X - Polynomial.C (1 : ℂ)) ^ h ∣ χ := by
    refine ⟨(Polynomial.X + 1) ^ h * Q, ?_⟩
    simpa [mul_assoc] using hχ
  have hminus : (Polynomial.X - Polynomial.C (-1 : ℂ)) ^ h ∣ χ := by
    refine ⟨(Polynomial.X - 1) ^ h * Q, ?_⟩
    simpa [mul_assoc, mul_comm, mul_left_comm] using hχ
  have hχ0 : χ ≠ 0 := (Toeplitz a (2 * m + 1)).charpoly_monic.ne_zero
  have hrplus : h ≤ Polynomial.rootMultiplicity (1 : ℂ) χ :=
    (Polynomial.le_rootMultiplicity_iff hχ0).mpr hplus
  have hrminus : h ≤ Polynomial.rootMultiplicity (-1 : ℂ) χ :=
    (Polynomial.le_rootMultiplicity_iff hχ0).mpr hminus
  constructor
  · simpa only [Polynomial.count_roots] using hrplus
  · simpa only [Polynomial.count_roots] using hrminus

/-- The finite source packets inherit the root-count implication once
their explicit jet equations are supplied. -/
theorem finiteCorrectedSymbol_jet_roots_count (u vCount m h : ℕ)
    (pM : Fin u → ℕ) (pτ : Fin u → ℂ)
    (nM nQ : Fin vCount → ℕ)
    (nv : ∀ j : Fin vCount, Fin (nQ j) → ℂ)
    (hBound : h ≤ m)
    (hJet : JetVanishing
      (finiteCorrectedSymbol u vCount pM pτ nM nQ nv) m h) :
    h ≤ ((Toeplitz (finiteCorrectedSymbol u vCount pM pτ nM nQ nv)
      (2 * m + 1)).charpoly.roots.count (1 : ℂ)) ∧
    h ≤ ((Toeplitz (finiteCorrectedSymbol u vCount pM pτ nM nQ nv)
      (2 * m + 1)).charpoly.roots.count (-1 : ℂ)) := by
  exact jetVanishing_roots_count _ m h
    (oddSupport_finiteCorrectedSymbol u vCount pM pτ nM nQ nv)
    hBound hJet

#assert_trust kernel jetVanishing_X_pow_dvd
#assert_trust kernel jetVanishing_charpoly_factor
#assert_trust kernel jetVanishing_roots_count
#assert_trust kernel finiteCorrectedSymbol_jet_roots_count
#print axioms finiteCorrectedSymbol_jet_roots_count

end NLA.Proofs.SP14
