import NLA.Proofs.SP14.CanonicalFirstWienerSizes
import NLA.Proofs.SP14.NegativeLaurentEndpointDivision

/-!
The actual strictly positive Laurent correction factors at the boundary
endpoint, and the source's negative quotient by g₀ has a continuous
extension through its sole zero. Wiener bounds are a separate gate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

private def positiveSourceCoeff (v : ℕ) (p : Fin v → ℝ) (j : ℕ) : ℝ :=
  if hj : j < v then p ⟨j, hj⟩ else 0

private def positiveQuotientCoeff (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => p j - positiveQuotientCoeff p j

private theorem positiveQuotientCoeff_zero (p : ℕ → ℝ) :
    positiveQuotientCoeff p 0 = 0 := rfl

private theorem positiveQuotientCoeff_succ (p : ℕ → ℝ) (j : ℕ) :
    positiveQuotientCoeff p (j + 1) =
      p j - positiveQuotientCoeff p j := rfl

private noncomputable def positiveRange (p : ℕ → ℝ) (v : ℕ) (s : Circle) : ℂ :=
  ∑ j ∈ Finset.range v, (p j : ℂ) * (s : ℂ) ^ (((j + 1 : ℕ) : ℤ))

private theorem positiveRange_succ (p : ℕ → ℝ) (v : ℕ) (s : Circle) :
    positiveRange p (v + 1) s =
      positiveRange p v s + (p v : ℂ) * (s : ℂ) ^ (((v + 1 : ℕ) : ℤ)) := by
  simp [positiveRange, Finset.sum_range_succ]

private theorem positiveRange_identity (p : ℕ → ℝ) (v : ℕ) (s : Circle) :
    positiveRange p v s =
      (1 + (s : ℂ)) *
        positiveRange (fun j => positiveQuotientCoeff p (j + 1)) v s -
      (positiveQuotientCoeff p v : ℂ) * (s : ℂ) ^ (((v + 1 : ℕ) : ℤ)) := by
  induction v with
  | zero => simp [positiveRange, positiveQuotientCoeff]
  | succ v ih =>
    rw [positiveRange_succ, positiveRange_succ, ih]
    have hpow : (s : ℂ) * (s : ℂ) ^ ((v : ℤ) + 1) =
        (s : ℂ) ^ ((v : ℤ) + 1 + 1) := by
      calc
        (s : ℂ) * (s : ℂ) ^ ((v : ℤ) + 1) =
            (s : ℂ) ^ (1 : ℤ) * (s : ℂ) ^ ((v : ℤ) + 1) := by simp
        _ = (s : ℂ) ^ ((v : ℤ) + 1 + 1) := by
          rw [← zpow_add₀ (Circle.coe_ne_zero s)]
          congr 1
          omega
    rw [positiveQuotientCoeff_succ]
    push_cast
    rw [← hpow]
    ring

private theorem positiveLaurent_eq_positiveRange (v : ℕ) (p : Fin v → ℝ)
    (s : Circle) :
    positiveLaurent v p s = positiveRange (positiveSourceCoeff v p) v s := by
  unfold positiveLaurent positiveRange
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hju : j < v := Finset.mem_range.mp hj
  simp [positiveSourceCoeff, hju]

theorem positiveLaurent_endpoint_factor (v : ℕ) (pPlus : Fin v → ℝ)
    (hcontact : positiveLaurent v pPlus (-1 : Circle) = 0) :
    ∃ qPlus : Fin v → ℝ,
      ∀ s : Circle,
        positiveLaurent v pPlus s =
          (1 + (s : ℂ)) * positiveLaurent v qPlus s := by
  let pn := positiveSourceCoeff v pPlus
  let qn := positiveQuotientCoeff pn
  let qPlus : Fin v → ℝ := fun j => qn (j.val + 1)
  refine ⟨qPlus, ?_⟩
  intro s
  have hterminal : qn v = 0 := by
    have hident := positiveRange_identity pn v (-1 : Circle)
    have hP : positiveRange pn v (-1 : Circle) = 0 := by
      rw [← positiveLaurent_eq_positiveRange]
      exact hcontact
    rw [hP] at hident
    have hcoef : (qn v : ℂ) * ((-1 : Circle) : ℂ) ^ (((v + 1 : ℕ) : ℤ)) = 0 := by
      simpa [qn, pn] using hident.symm
    have hpow : (((-1 : Circle) : ℂ) ^ (((v + 1 : ℕ) : ℤ))) ≠ 0 :=
      zpow_ne_zero _ (Circle.coe_ne_zero _)
    have hqc : (qn v : ℂ) = 0 := (mul_eq_zero.mp hcoef).resolve_right hpow
    exact_mod_cast hqc
  rw [positiveLaurent_eq_positiveRange]
  have hq : positiveLaurent v qPlus s =
      positiveRange (fun j => qn (j + 1)) v s := by
    rw [positiveLaurent_eq_positiveRange]
    apply Finset.sum_congr rfl
    intro j hj
    have hju : j < v := Finset.mem_range.mp hj
    simp [positiveSourceCoeff, qPlus, qn, hju]
  rw [hq]
  simpa [pn, qn, hterminal] using positiveRange_identity pn v s

noncomputable def negativeRatioExtension (u : ℕ) (qMinus : Fin u → ℝ)
    (s : Circle) : ℂ :=
  (s : ℂ) * baseExteriorFactor s * negativeLaurent u qMinus s

theorem continuous_negativeRatioExtension (u : ℕ) (qMinus : Fin u → ℝ) :
    Continuous (negativeRatioExtension u qMinus) := by
  unfold negativeRatioExtension
  exact (continuous_subtype_val.mul continuous_baseExteriorFactor).mul
    (continuous_negativeLaurent u qMinus)

theorem negativeRatioExtension_at_neg_one (u : ℕ) (qMinus : Fin u → ℝ) :
    negativeRatioExtension u qMinus (-1 : Circle) = 0 := by
  simp [negativeRatioExtension, baseExteriorFactor_at_neg_one]

theorem baseExteriorFactor_ne_zero_of_ne_neg_one
    (s : Circle) (hs : s ≠ (-1 : Circle)) :
    baseExteriorFactor s ≠ 0 := by
  intro hz
  have hsq := baseExteriorFactor_sq s
  rw [hz] at hsq
  have hzero : 1 + (s : ℂ)⁻¹ = 0 := by simpa using hsq.symm
  have hcoe : (s : ℂ) = -1 := by
    have hs0 : (s : ℂ) ≠ 0 := Circle.coe_ne_zero s
    calc
      (s : ℂ) = (1 + (s : ℂ)⁻¹) * (s : ℂ) - 1 := by
        field_simp [hs0]
        ring
      _ = -1 := by rw [hzero]; ring
  apply hs
  apply Subtype.ext
  simpa using hcoe

theorem negativeRatioExtension_eq_div (u : ℕ)
    (pMinus qMinus : Fin u → ℝ)
    (hfactor : ∀ s : Circle,
      negativeLaurent u pMinus s =
        (1 + (s : ℂ)) * negativeLaurent u qMinus s)
    (s : Circle) (hs : s ≠ (-1 : Circle)) :
    negativeLaurent u pMinus s / baseExteriorFactor s =
      negativeRatioExtension u qMinus s := by
  have hg : baseExteriorFactor s ≠ 0 :=
    baseExteriorFactor_ne_zero_of_ne_neg_one s hs
  have hs0 : (s : ℂ) ≠ 0 := Circle.coe_ne_zero s
  have hsg : (s : ℂ) * baseExteriorFactor s ^ 2 = 1 + (s : ℂ) := by
    rw [baseExteriorFactor_sq]
    field_simp [hs0]
    ring
  rw [hfactor s]
  unfold negativeRatioExtension
  apply (div_eq_iff hg).2
  rw [← hsg]
  ring

#assert_trust kernel positiveLaurent_endpoint_factor
#assert_trust kernel continuous_negativeRatioExtension
#assert_trust kernel negativeRatioExtension_at_neg_one
#assert_trust kernel baseExteriorFactor_ne_zero_of_ne_neg_one
#assert_trust kernel negativeRatioExtension_eq_div

end NLA.Proofs.SP14
