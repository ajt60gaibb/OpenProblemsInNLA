import NLA.FR05.Probability

/-! ## Assembly -/

section

/-
The purely numerical final step of Theorem 1.4. The analytic work in the
source is precisely what supplies `comparison`; no asymptotic notation or
unnamed constant crosses this finite algebraic boundary.
-/


set_option autoImplicit false

namespace NLA.FR05

/-- The final Cauchy--Schwarz inequality in Li's proof closes at rate `d⁻¹`.

If a nonnegative probability `p` obeys the bound obtained from a planted-law
failure estimate `a / d²` and an `L²` comparison estimate `b / d`, then it is
bounded by `(2a+b)/d`. -/
theorem inverse_bound_of_source_comparison (d : ℕ) (hd : 1 ≤ d)
    (p a b : ℝ) (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (comparison : p ≤ a / (d : ℝ) ^ 2 + Real.sqrt (b * p / d)) :
    p ≤ (2 * a + b) / d := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  have hdR' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  rw [mul_comm b p, mul_div_assoc] at comparison
  have young : Real.sqrt (p * (b / (d : ℝ))) ≤ (p + b / (d : ℝ)) / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (p - b / (d : ℝ))]
  have hsmall : a / (d : ℝ) ^ 2 ≤ a / (d : ℝ) := by
    gcongr
    nlinarith
  simp only [add_div, mul_div_assoc]
  nlinarith

/-- The standard finite-prefix absorption step used after an eventual inverse
bound. This makes the final quantifier in the source theorem explicit. -/
theorem global_inverse_bound_of_eventual (D : ℕ) (p : ℕ → ℝ) (a b : ℝ)
    (at_most_one : ∀ d, p d ≤ 1)
    (eventual : ∀ d, D ≤ d → p d ≤ (2 * a + b) / d) :
    ∃ C : ℝ, 0 < C ∧ ∀ d, 2 ≤ d → p d ≤ C / d := by
  let C : ℝ := max (2 * a + b) (D : ℝ) + 1
  have hCpos : 0 < C := by
    have hDnonneg : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
    have hmax : (D : ℝ) ≤ max (2 * a + b) (D : ℝ) := le_max_right _ _
    dsimp [C]
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  by_cases hlarge : D ≤ d
  · have hmain := eventual d hlarge
    have hcoef : 2 * a + b ≤ C := by
      dsimp [C]
      exact le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one)
    exact hmain.trans ((div_le_div_iff_of_pos_right hdR).2 hcoef)
  · have hsmall : d ≤ D := Nat.le_of_not_ge hlarge
    apply (le_div_iff₀ hdR).2
    have hnat : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast hsmall
    have hDC : (D : ℝ) ≤ C := by
      dsimp [C]
      exact le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
    have hbound : (d : ℝ) ≤ C := hnat.trans hDC
    nlinarith [at_most_one d]

end NLA.FR05

end
/-! ## MainReduction -/

section

/-
The source-independent numerical reduction of the quantitative theorem.
`FinalAssembly` supplies the explicit eventual comparison from the proved
sampler identities and Propositions 3.1 and 3.2.
-/


set_option autoImplicit false

namespace NLA.FR05

/-- An eventual instance of the source's final comparison is sufficient for
the advertised inverse bound. `FinalAssembly` discharges this interface for
the original Gaussian injectivity probability. -/
theorem phaseRetrieval_injective_probability_le_inv_of_source_comparison
    (D : ℕ) (a b : ℝ) (hD : 1 ≤ D) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (comparison : ∀ d : ℕ, D ≤ d →
      phaseRetrievalProbability d ≤ a / (d : ℝ) ^ 2 +
        Real.sqrt (b * phaseRetrievalProbability d / d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      phaseRetrievalProbability d ≤ C / d := by
  apply global_inverse_bound_of_eventual D phaseRetrievalProbability a b
  · exact phaseRetrievalProbability_le_one
  · intro d hd
    exact inverse_bound_of_source_comparison d (hD.trans hd)
      (phaseRetrievalProbability d) a b
      (phaseRetrievalProbability_nonneg d) ha hb (comparison d hd)

end NLA.FR05

end
