import NLA.KE03.Search

noncomputable section

namespace NLA.KE03

/-- Multiplicative power estimates and the arithmetic root search recover the
radius up to the stated factor. No root is an algorithmic primitive. -/
theorem radius_from_powers {m : ℕ} (hm : 0 < m) {F a R H r : ℝ}
    (_hF : 0 ≤ F) (ha : 1 ≤ a) (hR : 0 ≤ R) (hH : 0 ≤ H) (hr : 0 ≤ r)
    (hFm : F ≤ a ^ m) (hlo : R ^ m ≤ F * H) (hup : H ≤ F * R ^ m)
    (hrlo : r ^ (2 * m) ≤ H ^ 2) (hrhi : H ^ 2 ≤ (a * r) ^ (2 * m)) :
    R ≤ a ^ 2 * r ∧ r ≤ a ^ 2 * R := by
  have ha0 : 0 ≤ a := by linarith
  rw [show 2 * m = m * 2 by omega, pow_mul] at hrlo hrhi
  have hrpow : r ^ m ≤ H := le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) hH hrlo
  have hHpow : H ≤ (a * r) ^ m :=
    le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (by positivity) hrhi
  constructor
  · apply le_of_pow_le_pow_left₀ hm.ne' (by positivity)
    calc
      R ^ m ≤ F * H := hlo
      _ ≤ a ^ m * (a * r) ^ m := mul_le_mul hFm hHpow hH (by positivity)
      _ = (a ^ 2 * r) ^ m := by rw [← mul_pow]; congr 1; ring
  · have hsmall : r ≤ a * R := by
      apply le_of_pow_le_pow_left₀ hm.ne' (by positivity)
      calc
        r ^ m ≤ H := hrpow
        _ ≤ F * R ^ m := hup
        _ ≤ a ^ m * R ^ m := mul_le_mul_of_nonneg_right hFm (by positivity)
        _ = (a * R) ^ m := (mul_pow _ _ _).symm
    have haa : a ≤ a ^ 2 := by nlinarith
    exact hsmall.trans (mul_le_mul_of_nonneg_right haa hR)

/-- Maximizing the computed norm also approximately maximizes the shifted
spectral radius, because one good seed controls every shift simultaneously. -/
theorem shifted_radius_from_powers {m : ℕ} (hm : 0 < m) {F a Rs Rz Hs Hz : ℝ}
    (hF : 0 ≤ F) (ha : 0 ≤ a) (hRz : 0 ≤ Rz) (hFm : F ≤ a ^ m)
    (hlo : Rs ^ m ≤ F * Hs) (hsel : Hs ≤ Hz) (hup : Hz ≤ F * Rz ^ m) :
    Rs ≤ a ^ 2 * Rz := by
  apply le_of_pow_le_pow_left₀ hm.ne' (by positivity)
  calc
    Rs ^ m ≤ F * Hs := hlo
    _ ≤ F * Hz := mul_le_mul_of_nonneg_left hsel hF
    _ ≤ F * (F * Rz ^ m) := mul_le_mul_of_nonneg_left hup hF
    _ ≤ a ^ m * (a ^ m * Rz ^ m) := by gcongr
    _ = (a ^ 2 * Rz) ^ m := by rw [← mul_pow, ← mul_pow]; congr 1; ring

end NLA.KE03
