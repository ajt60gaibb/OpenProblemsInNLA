import NLA.Proofs.SP14.WienerAdd

/-!
The literal W^(9/8) size of the square of an actual finite real Laurent
correction is bounded by the square of its separate positive/negative sizes.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

private theorem summable_wiener_constant_one :
    Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient (fun _ : Circle => (1 : ℂ)) k‖) := by
  have hmode : (fun _ : Circle => (1 : ℂ)) =
      (fun s : Circle => (s : ℂ) ^ (0 : ℤ)) := by
    funext s
    simp
  rw [hmode]
  simp_rw [FourierCoefficient_circle_mode 0]
  apply summable_of_ne_finset_zero (s := {0})
  intro k hk
  have hne : (0 : ℤ) ≠ k := (by simpa using hk : k ≠ 0).symm
  simp [hne]

theorem summable_negativeLaurent_wiener (u : ℕ) (pMinus : Fin u → ℝ) :
    Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient (negativeLaurent u pMinus) k‖) := by
  have h := summable_mul_negativeLaurent_wiener
    (fun _ : Circle => (1 : ℂ)) continuous_const
    summable_wiener_constant_one u pMinus
  simpa only [one_mul] using h

theorem summable_finiteLaurentCorrection_wiener
    (u v : ℕ) (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ) :
    Summable (fun k : ℤ =>
      wienerWeight k *
        ‖FourierCoefficient (finiteLaurentCorrection u v pMinus pPlus) k‖) := by
  change Summable (fun k : ℤ =>
    wienerWeight k *
      ‖FourierCoefficient
        (fun s => negativeLaurent u pMinus s + positiveLaurent v pPlus s) k‖)
  exact summable_wiener_add (negativeLaurent u pMinus) (positiveLaurent v pPlus)
    (continuous_negativeLaurent u pMinus) (continuous_positiveLaurent v pPlus)
    (summable_negativeLaurent_wiener u pMinus)
    (summable_positiveLaurent_wiener v pPlus)

theorem weightedWienerSize_finiteLaurentCorrection_le
    (u v : ℕ) (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ) :
    weightedWienerSize (finiteLaurentCorrection u v pMinus pPlus) ≤
      weightedWienerSize (negativeLaurent u pMinus) +
        weightedWienerSize (positiveLaurent v pPlus) := by
  change weightedWienerSize
    (fun s => negativeLaurent u pMinus s + positiveLaurent v pPlus s) ≤ _
  exact weightedWienerSize_add_le
    (negativeLaurent u pMinus) (positiveLaurent v pPlus)
    (continuous_negativeLaurent u pMinus) (continuous_positiveLaurent v pPlus)
    (summable_negativeLaurent_wiener u pMinus)
    (summable_positiveLaurent_wiener v pPlus)

theorem summable_finiteLaurentCorrection_sq_wiener
    (u v : ℕ) (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ) :
    Summable (fun k : ℤ =>
      wienerWeight k *
        ‖FourierCoefficient
          (fun s => finiteLaurentCorrection u v pMinus pPlus s ^ 2) k‖) := by
  let P := finiteLaurentCorrection u v pMinus pPlus
  let Pm := negativeLaurent u pMinus
  let Pp := positiveLaurent v pPlus
  have hP : Continuous P := continuous_finiteLaurentCorrection u v pMinus pPlus
  have hPs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient P k‖) :=
    summable_finiteLaurentCorrection_wiener u v pMinus pPlus
  have hPm : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient (fun s => P s * Pm s) k‖) :=
    summable_mul_negativeLaurent_wiener P hP hPs u pMinus
  have hPp : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient (fun s => P s * Pp s) k‖) :=
    summable_mul_positiveLaurent_wiener P hP hPs v pPlus
  have heq : (fun s : Circle => P s ^ 2) =
      (fun s => P s * Pm s + P s * Pp s) := by
    funext s
    dsimp [P, Pm, Pp, finiteLaurentCorrection]
    ring
  rw [heq]
  exact summable_wiener_add (fun s => P s * Pm s) (fun s => P s * Pp s)
    (hP.mul (continuous_negativeLaurent u pMinus))
    (hP.mul (continuous_positiveLaurent v pPlus)) hPm hPp

theorem weightedWienerSize_finiteLaurentCorrection_sq_le
    (u v : ℕ) (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ) :
    weightedWienerSize
        (fun s => finiteLaurentCorrection u v pMinus pPlus s ^ 2) ≤
      (weightedWienerSize (negativeLaurent u pMinus) +
        weightedWienerSize (positiveLaurent v pPlus)) ^ 2 := by
  let P := finiteLaurentCorrection u v pMinus pPlus
  let Pm := negativeLaurent u pMinus
  let Pp := positiveLaurent v pPlus
  have hP : Continuous P := continuous_finiteLaurentCorrection u v pMinus pPlus
  have hPs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient P k‖) :=
    summable_finiteLaurentCorrection_wiener u v pMinus pPlus
  have hPm : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient (fun s => P s * Pm s) k‖) :=
    summable_mul_negativeLaurent_wiener P hP hPs u pMinus
  have hPp : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient (fun s => P s * Pp s) k‖) :=
    summable_mul_positiveLaurent_wiener P hP hPs v pPlus
  have heq : (fun s : Circle => P s ^ 2) =
      (fun s => P s * Pm s + P s * Pp s) := by
    funext s
    dsimp [P, Pm, Pp, finiteLaurentCorrection]
    ring
  have hmulm := weightedWienerSize_mul_negativeLaurent_le P hP hPs u pMinus
  have hmulp := weightedWienerSize_mul_positiveLaurent_le P hP hPs v pPlus
  have hsum := weightedWienerSize_add_le
    (fun s => P s * Pm s) (fun s => P s * Pp s)
    (hP.mul (continuous_negativeLaurent u pMinus))
    (hP.mul (continuous_positiveLaurent v pPlus)) hPm hPp
  have hPbound : weightedWienerSize P ≤
      weightedWienerSize Pm + weightedWienerSize Pp :=
    weightedWienerSize_finiteLaurentCorrection_le u v pMinus pPlus
  have hPmnonneg : 0 ≤ weightedWienerSize Pm := by
    unfold weightedWienerSize
    apply tsum_nonneg
    intro k
    exact mul_nonneg (by unfold wienerWeight; positivity) (norm_nonneg _)
  have hPpnonneg : 0 ≤ weightedWienerSize Pp := by
    unfold weightedWienerSize
    apply tsum_nonneg
    intro k
    exact mul_nonneg (by unfold wienerWeight; positivity) (norm_nonneg _)
  rw [heq]
  have hPmn : weightedWienerSize Pm = finiteNegativeWienerSize u pMinus :=
    negativeLaurent_wiener_eq u pMinus
  have hPpn : weightedWienerSize Pp = finitePositiveWienerSize v pPlus :=
    positiveLaurent_wiener_eq v pPlus
  calc
    weightedWienerSize (fun s => P s * Pm s + P s * Pp s) ≤
      weightedWienerSize (fun s => P s * Pm s) +
        weightedWienerSize (fun s => P s * Pp s) := hsum
    _ ≤ weightedWienerSize P *
        (weightedWienerSize Pm + weightedWienerSize Pp) := by
      rw [hPmn, hPpn]
      nlinarith [hmulm, hmulp]
    _ ≤ (weightedWienerSize Pm + weightedWienerSize Pp) ^ 2 := by
      nlinarith [hPbound, hPmnonneg, hPpnonneg]

#assert_trust kernel summable_finiteLaurentCorrection_wiener
#assert_trust kernel weightedWienerSize_finiteLaurentCorrection_le
#assert_trust kernel summable_finiteLaurentCorrection_sq_wiener
#assert_trust kernel weightedWienerSize_finiteLaurentCorrection_sq_le

end NLA.Proofs.SP14
