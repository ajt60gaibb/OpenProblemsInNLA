import NLA.Proofs.MF03.Uniqueness

/-! Transport of an MF-03 disk certificate to every reduced Padé pair. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

open NLA.Statements.MF03

/-- A disk estimate for one normalized Padé pair applies to every reduced
normalized pair of the same order. The witness pair itself need not be
coprime: coprimeness of the tested pair makes its denominator divide the
witness denominator. -/
theorem disk_bound_for_every_reduced_pair
    (m : ℕ) (P₀ Q₀ : Polynomial ℂ)
    (h₀ : NormalizedPadeRepresentation m P₀ Q₀)
    (hdisk₀ : ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
      Q₀.eval z ≠ 0 ∧ ‖(1 : ℂ) - P₀.eval z / Q₀.eval z‖ ≤ (2 : ℝ))
    (P Q : Polynomial ℂ) (h : ReducedPadeRepresentation m P Q) :
    ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
      Q.eval z ≠ 0 ∧ ‖(1 : ℂ) - P.eval z / Q.eval z‖ ≤ (2 : ℝ) := by
  have hcross : P * Q₀ = P₀ * Q :=
    normalized_cross_product_eq m P Q P₀ Q₀ h.1 h₀
  have hdiv : Q ∣ P * Q₀ := by
    refine ⟨P₀, ?_⟩
    calc
      P * Q₀ = P₀ * Q := hcross
      _ = Q * P₀ := mul_comm _ _
  have hQdvd : Q ∣ Q₀ :=
    h.2.symm.dvd_of_dvd_mul_left hdiv
  obtain ⟨R, hR⟩ := hQdvd
  intro z hz
  obtain ⟨hQ₀ne, hbound₀⟩ := hdisk₀ z hz
  have hQne : Q.eval z ≠ 0 := by
    intro hzero
    apply hQ₀ne
    rw [hR, Polynomial.eval_mul, hzero]
    simp
  refine ⟨hQne, ?_⟩
  have heval : P.eval z * Q₀.eval z = P₀.eval z * Q.eval z := by
    have h' := congrArg (fun T : Polynomial ℂ => T.eval z) hcross
    simpa only [Polynomial.eval_mul] using h'
  have hquot : P.eval z / Q.eval z = P₀.eval z / Q₀.eval z :=
    (div_eq_div_iff hQne hQ₀ne).2 heval
  rw [hquot]
  exact hbound₀

#print axioms disk_bound_for_every_reduced_pair
#assert_trust kernel disk_bound_for_every_reduced_pair

end NLA.Proofs.MF03
