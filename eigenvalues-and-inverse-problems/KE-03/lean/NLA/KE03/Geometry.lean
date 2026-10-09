import NLA.KE03.MatrixBounds
import NLA.KE03.Search

/-! Finite complex geometry: a nearly maximal shifted spectral radius locates
an eigenvalue near the spectral circle. -/

noncomputable section
namespace NLA.KE03

private theorem scaled_circle_identity (w u : ℂ) (ρ r : ℝ)
    (hw : ‖w‖ = ρ) (hu : ‖u‖ = 1) :
    ρ * ‖w + (r : ℂ) * u‖ ^ 2 + r * ‖w - (ρ : ℂ) * u‖ ^ 2 =
      ρ * (ρ + r) ^ 2 := by
  have hw' : w.re ^ 2 + w.im ^ 2 = ρ ^ 2 := by
    rw [← hw, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hu' : u.re ^ 2 + u.im ^ 2 = 1 := by
    calc _ = ‖u‖ ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
         _ = 1 := by rw [hu]; norm_num
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  linear_combination (ρ + r) * hw' + (ρ * r * (ρ + r)) * hu'

private theorem shifted_circle_lower (w u : ℂ) {ρ r ε : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (_hε : 0 < ε) (hw : ‖w‖ = ρ) (hu : ‖u‖ = 1)
    (hnet : ‖w / (ρ : ℂ) - u‖ ≤ ε / 8) :
    (ρ + r) ^ 2 - ρ * r * ε ^ 2 / 64 ≤ ‖w + (r : ℂ) * u‖ ^ 2 := by
  have he : (ρ : ℂ) * (w / (ρ : ℂ) - u) = w - (ρ : ℂ) * u := by
    have hz : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    field_simp
  have hdist : ‖w - (ρ : ℂ) * u‖ ≤ ρ * ε / 8 := by
    rw [← he, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    nlinarith [mul_le_mul_of_nonneg_left hnet hρ.le]
  have hsq : ‖w - (ρ : ℂ) * u‖ ^ 2 ≤ (ρ * ε / 8) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hdist 2
  have hid := scaled_circle_identity w u ρ r hw hu
  apply (mul_le_mul_iff_right₀ hρ).mp
  nlinarith [mul_le_mul_of_nonneg_left hsq hr.le]

private theorem eta_geometry_bounds {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    0 ≤ eta ε ∧ eta ε ≤ 1 / 4 ∧
    (1 + eta ε) ^ 2 ≤ 1 + 3 * eta ε ∧ (1 + eta ε) ^ 2 ≤ 2 ∧
    (1 + eta ε) ^ 4 ≤ 1 + 15 * eta ε ∧
    9 * eta ε ^ 2 + 135 * eta ε + ε ^ 2 / 32 ≤ ε ^ 2 / 4 ∧
    3 * eta ε ≤ ε / 2 := by
  have ht : 0 ≤ eta ε := (eta_pos hε).le
  have ht4 : eta ε ≤ 1 / 4 := by dsimp [eta]; nlinarith
  have ht1 : eta ε ≤ 1 := by linarith
  have hsq : eta ε ^ 2 ≤ eta ε := by nlinarith
  have hcube : eta ε ^ 3 ≤ eta ε := by
    nlinarith [mul_le_mul_of_nonneg_right hsq ht]
  have hfour : eta ε ^ 4 ≤ eta ε := by
    nlinarith [mul_le_mul_of_nonneg_right hcube ht]
  refine ⟨ht, ht4, by nlinarith, by nlinarith, by nlinarith, ?_, ?_⟩
  · have he : ε ^ 2 = 1024 * eta ε := by dsimp [eta]; ring
    nlinarith
  · dsimp [eta]
    nlinarith

set_option maxHeartbeats 1000000 in
theorem location_from_shift_max {n : ℕ} (hn : 0 < n) (lam : Fin n → ℂ)
    {ρ r ε : ℝ} (hρ : ‖lam‖ = ρ) (hρpos : 0 < ρ) (hrpos : 0 < r)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) {u us : ℂ}
    (hunit : ‖u‖ = 1) (hsunit : ‖us‖ = 1) {iStar : Fin n}
    (hstar : ‖lam iStar‖ = ρ) (hnet : ‖lam iStar / (ρ : ℂ) - us‖ ≤ ε / 8)
    (hlo : ρ ≤ (1 + eta ε) ^ 2 * r) (hup : r ≤ (1 + eta ε) ^ 2 * ρ)
    (hshift : ‖fun i => lam i + (r : ℂ) * us‖ ≤
      (1 + eta ε) ^ 2 * ‖fun i => lam i + (r : ℂ) * u‖) :
    ∃ i, (1 - ε) * ρ ≤ ‖lam i‖ ∧ ‖(r : ℂ) * u - lam i‖ ≤ ε * ρ := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨ht, ht4, ha2, ha2two, ha4, herror, hsmall⟩ := eta_geometry_bounds hε hεhalf
  let z : ℂ := (r : ℂ) * u
  have hz : ‖z‖ = r := by simp [z, hunit, Real.norm_of_nonneg hrpos.le]
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm (fun i => lam i + z)).1
  change ‖lam i + z‖ = ‖fun i => lam i + z‖ at hi
  have hmu : ‖lam i‖ ≤ ρ := hρ ▸ norm_le_pi_norm lam i
  have hrupper : r ≤ 2 * ρ := by
    nlinarith [mul_le_mul_of_nonneg_right ha2two hρpos.le]
  have hradup : r - ρ ≤ 3 * eta ε * ρ := by
    nlinarith [mul_le_mul_of_nonneg_right ha2 hρpos.le]
  have hradlo : ρ - r ≤ 3 * eta ε * ρ := by
    by_cases hrρ : r ≤ ρ
    · nlinarith [mul_le_mul_of_nonneg_right ha2 hrpos.le,
        mul_le_mul_of_nonneg_left hrρ (by positivity : 0 ≤ 3 * eta ε)]
    · nlinarith [mul_nonneg ht hρpos.le]
  have hradsq : (ρ - r) ^ 2 ≤ 9 * eta ε ^ 2 * ρ ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 3 * eta ε * ρ - (ρ - r) by linarith)
      (show 0 ≤ 3 * eta ε * ρ + (ρ - r) by linarith)]
  have hsum : ‖lam i + z‖ ≤ ρ + r := (norm_add_le _ _).trans (by rw [hz]; linarith)
  have hsumSq : ‖lam i + z‖ ^ 2 ≤ (ρ + r) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hsum 2
  have hnetlower := shifted_circle_lower (lam iStar) us hρpos hrpos hε hstar hsunit hnet
  have hstarupper : ‖lam iStar + (r : ℂ) * us‖ ≤
      (1 + eta ε) ^ 2 * ‖lam i + z‖ := by
    rw [hi]
    exact (norm_le_pi_norm (fun i => lam i + (r : ℂ) * us) iStar).trans hshift
  have hstarSq := pow_le_pow_left₀ (norm_nonneg _) hstarupper 2
  have hdefect : (ρ + r) ^ 2 - ‖lam i + z‖ ^ 2 ≤
      15 * eta ε * (ρ + r) ^ 2 + ρ * r * ε ^ 2 / 64 := by
    have ha := mul_le_mul_of_nonneg_right ha4 (sq_nonneg ‖lam i + z‖)
    have hs := mul_le_mul_of_nonneg_left hsumSq (by positivity : 0 ≤ 15 * eta ε)
    nlinarith only [hnetlower, hstarSq, ha, hs]
  have hpar := parallelogram_law_with_norm ℂ (lam i) z
  have hmusq := pow_le_pow_left₀ (norm_nonneg _) hmu 2
  have hdistSq : ‖z - lam i‖ ^ 2 ≤ ε ^ 2 * ρ ^ 2 / 4 := by
    rw [norm_sub_rev]
    rw [hz] at hpar
    have hsum3 : (ρ + r) ^ 2 ≤ 9 * ρ ^ 2 := by
      have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ρ + r)
        (show ρ + r ≤ 3 * ρ by linarith) 2
      nlinarith only [hs]
    have hsumErr := mul_le_mul_of_nonneg_left hsum3 (by positivity : 0 ≤ 15 * eta ε)
    have hnetErr := mul_le_mul_of_nonneg_left hrupper
      (show 0 ≤ ρ * ε ^ 2 / 64 by positivity)
    have herr := mul_le_mul_of_nonneg_right herror (sq_nonneg ρ)
    nlinarith only [hpar, hmusq, hradsq, hdefect, hsumErr, hnetErr, herr]
  have hdist : ‖z - lam i‖ ≤ ε * ρ / 2 := by
    nlinarith only [hdistSq, norm_nonneg (z - lam i), mul_pos hε hρpos]
  have hrnear : (1 - ε / 2) * ρ ≤ r := by
    nlinarith only [hradlo, mul_le_mul_of_nonneg_right hsmall hρpos.le]
  refine ⟨i, ?_, ?_⟩
  · have htri := norm_sub_norm_le z (lam i)
    rw [hz] at htri
    nlinarith only [htri, hrnear, hdist]
  · change ‖z - lam i‖ ≤ ε * ρ
    nlinarith only [hdist, mul_pos hε hρpos]

end NLA.KE03
