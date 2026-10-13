import NLA.Proofs.RA06.GraphFinite
import NLA.Proofs.RA06.Asymptotic

/-! The numerical specialization and final contradiction for the frozen RA-06 target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA06

open NLA.Statements.RA06

private theorem accuracy_power_identity (p b : ℝ) (hb : 0 < b) :
    Real.rpow (6 * (1 / b)) (-p) =
      Real.rpow 6 (-p) * Real.rpow b p := by
  have hinv : (b⁻¹)^(-p) = b^p := by
    rw [Real.rpow_neg_eq_inv_rpow]
    simp
  have h : (6 * b⁻¹)^(-p) = 6^(-p) * b^p := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6)
      (by positivity : 0 ≤ b⁻¹), hinv]
  simpa only [Real.rpow_eq_pow, one_div] using h

private theorem inverse_accuracy_square (b : ℝ) :
    Real.rpow (1 / b) (-2) = b^2 := by
  have h : (b⁻¹)^(-2 : ℝ) = b^2 := by
    rw [Real.rpow_neg_eq_inv_rpow]
    simp
  simpa only [Real.rpow_eq_pow, one_div] using h

private theorem dimension_regime_for_ceiling
    (p : ℝ) (b v : ℕ) (hp : 2 < p) (hb : 3 ≤ b)
    (hvceil : v = Nat.ceil (Real.rpow (b : ℝ) (p + 2))) :
    Real.rpow (6 * (1 / (b : ℝ))) (-p) ≤
      ((v - 1 : ℕ) : ℝ) * (1 / (b : ℝ)) := by
  have hbR : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hdim := accuracy_parameter_dimension_regime p (b : ℝ) hp hbR
  have hvbound : Real.rpow (b : ℝ) (p + 2) ≤ (v : ℝ) := by
    rw [hvceil]
    exact Nat.le_ceil _
  have hv1 : 1 ≤ v := by
    have hpowpos := Real.rpow_pos_of_pos hb0 (p + 2)
    have : (0 : ℝ) < v := lt_of_lt_of_le hpowpos hvbound
    exact_mod_cast (show 1 ≤ v by exact_mod_cast this)
  have hvsub : (((v - 1 : ℕ) : ℝ)) = (v : ℝ) - 1 := by
    rw [Nat.cast_sub hv1]
    norm_num
  rw [accuracy_power_identity p (b : ℝ) hb0, hvsub]
  have hcore : Real.rpow 6 (-p) * Real.rpow (b : ℝ) (p + 1) ≤
      (v : ℝ) - 1 := by linarith
  have hpow : Real.rpow (b : ℝ) (p + 1) =
      Real.rpow (b : ℝ) p * (b : ℝ) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      (Real.rpow_add hb0 p 1)
  rw [hpow] at hcore
  calc
    Real.rpow 6 (-p) * Real.rpow (b : ℝ) p ≤ ((v : ℝ) - 1) / (b : ℝ) :=
      (le_div_iff₀ hb0).2 (by nlinarith [hcore])
    _ = ((v : ℝ) - 1) * (1 / (b : ℝ)) := by ring

/-- The exact frozen target, with the original all-matrix quantifiers and
the original floor and saturation sampler. -/
theorem target : NLA.Statements.RA06.Target := by
  intro p hp hpositive
  obtain ⟨C, c, hC, hc, hpositive⟩ := hpositive
  let K : ℝ := 2 * Real.rpow 2 (p - 1) + 1
  let L : ℝ := (3 / 8) * Real.rpow 6 (-p)
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨b, hb, hsep⟩ :=
    exists_large_accuracy_parameter_for_coefficients p C c L K
      hp hC hc hL hK
  let v : ℕ := Nat.ceil (Real.rpow (b : ℝ) (p + 2))
  let d : ℕ := v - 1
  let n : ℕ := Fintype.card (Edge (d + 1))
  let A := GraphMatrix d
  have hbR : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hb0
  have hpowerB : (b : ℝ) ≤ Real.rpow (b : ℝ) (p + 2) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le
        (by linarith : (1 : ℝ) ≤ b) (by linarith : (1 : ℝ) ≤ p + 2))
  have hv3R : (3 : ℝ) ≤ v := by
    dsimp [v]
    exact hbR.trans (hpowerB.trans (Nat.le_ceil _))
  have hv3 : 3 ≤ v := by exact_mod_cast hv3R
  have hvpos : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  have hd : 0 < d := by dsimp [d]; omega
  have hdplus : d + 1 = v := by dsimp [d]; omega
  have hn : 0 < n := by
    dsimp [n]
    exact graphMatrix_rows_pos d hd
  have hcount : n ≤ v * v := by
    dsimp [n]
    rw [hdplus]
    simpa only [Edge, Fintype.card_prod, Fintype.card_fin] using
      (Fintype.card_subtype_le
        (fun ij : Fin v × Fin v => ij.1 < ij.2))
  have hε : (0 : ℝ) < 1 / (b : ℝ) := by positivity
  have hεhalf : (1 / (b : ℝ)) < 1 / 2 := by
    exact (div_lt_iff₀ hb0).2 (by nlinarith [hbR])
  have hregime : Real.rpow (6 * (1 / (b : ℝ))) (-p) ≤
      (d : ℝ) * (1 / (b : ℝ)) := by
    simpa only [d] using dimension_regime_for_ceiling p b v hp hb rfl
  obtain ⟨α, hα, hbudget, hsuccess⟩ :=
    hpositive n d hn hd A (by exact graphMatrix_fullColumnRank d)
      (1 / (b : ℝ)) (1 / 4) hε hεhalf (by norm_num) (by norm_num)
  let S : ℝ := TotalSensitivity A p + (d : ℝ)
  let E : ℝ := ExpectedSize A p α
  have hS : S ≤ K * (v : ℝ) := by
    simpa only [S, K, A, hdplus] using
      graphMatrix_totalSensitivity_bound d hd p (by linarith)
  have hElowerRaw := expectedSize_lower_from_graph_success d hd p
    (1 / (b : ℝ)) (1 / 4) α (by linarith : 1 < p)
    hε hεhalf hα hregime hsuccess
  have hElower : L * (v : ℝ) * Real.rpow (b : ℝ) p ≤ E := by
    calc
      L * (v : ℝ) * Real.rpow (b : ℝ) p =
          (1 - (1 / 4 : ℝ)) *
            (((d + 1 : ℕ) : ℝ) / 2 *
              Real.rpow (6 * (1 / (b : ℝ))) (-p)) := by
        rw [hdplus, accuracy_power_identity p (b : ℝ) hb0]
        dsimp only [L]
        ring
      _ ≤ E := hElowerRaw
  have hlog := budget_log_upper_for_ceiling_card_bound p b v n hp hb
    rfl hn hcount
  have hSnonneg : 0 ≤ S := by
    dsimp [S, TotalSensitivity, A]
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro i _
      exact sensitivity_nonneg (GraphMatrix d) p
        (graphMatrix_fullColumnRank d) hd i
    · positivity
  have hlogarg : 1 ≤ 2 * (n : ℝ) * (d : ℝ) /
      ((1 / (b : ℝ)) * (1 / 4)) := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hnd : (1 : ℝ) ≤ (n : ℝ) * (d : ℝ) := by nlinarith
    have heq : 2 * (n : ℝ) * (d : ℝ) /
        ((1 / (b : ℝ)) * (1 / 4)) = 8 * (b : ℝ) * ((n : ℝ) * (d : ℝ)) := by
      field_simp [hbne]
      ring
    rw [heq]
    nlinarith [mul_nonneg (by linarith : 0 ≤ (b : ℝ) - 3)
      (by linarith : 0 ≤ (n : ℝ) * (d : ℝ) - 1)]
  have hlogpow : Real.rpow
      (Real.log (2 * (n : ℝ) * (d : ℝ) /
        ((1 / (b : ℝ)) * (1 / 4)))) c ≤
      Real.rpow (Real.log
        (32 * Real.rpow (b : ℝ) (3 * p + 7))) c :=
    Real.rpow_le_rpow (Real.log_nonneg hlogarg) hlog hc.le
  have hEupper : E ≤ C * (b : ℝ)^2 * S *
      Real.rpow (Real.log
        (32 * Real.rpow (b : ℝ) (3 * p + 7))) c := by
    calc
      E ≤ C * Real.rpow (1 / (b : ℝ)) (-2) * S *
          Real.rpow (Real.log (2 * (n : ℝ) * (d : ℝ) /
            ((1 / (b : ℝ)) * (1 / 4)))) c := hbudget
      _ = C * (b : ℝ)^2 * S *
          Real.rpow (Real.log (2 * (n : ℝ) * (d : ℝ) /
            ((1 / (b : ℝ)) * (1 / 4)))) c := by
        rw [inverse_accuracy_square (b : ℝ)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogpow
        (mul_nonneg (mul_nonneg hC.le (sq_nonneg _)) hSnonneg)
  exact finite_bounds_contradict_for_coefficients p C c L K b v S E
    hp hC hL hK hb hvpos hsep hS hElower hEupper

#print axioms target
#assert_trust kernel target

end NLA.Proofs.RA06
