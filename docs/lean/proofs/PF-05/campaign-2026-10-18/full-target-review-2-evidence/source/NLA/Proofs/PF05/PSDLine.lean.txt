import NLA.Proofs.PF05.ZeroPair

/-! Exact boundary algebra for feasible straight PSD segments in size two. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.PF05
open NLA.Statements.PF05

def determinantDirection (B F : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  B 0 0 * F 1 1 + B 1 1 * F 0 0 - 2 * B 0 1 * F 0 1

theorem det_add_smul_two (B F : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : Symmetric B) (hF : Symmetric F) (t : ℝ) :
    (B + t • F).det = B.det + t * determinantDirection B F + t^2 * F.det := by
  simp [Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply,
    determinantDirection, hB 1 0, hF 1 0, smul_eq_mul]
  ring

/-- The leading determinant coefficient cannot be negative on an actual
one-sided feasible PSD segment through a singular factor. -/
theorem determinantDirection_nonneg_of_segment
    (B F : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : Symmetric B) (hF : Symmetric F) (hdet : B.det = 0)
    (hseg : ∃ h : ℝ, 0 < h ∧ ∀ t, 0 ≤ t → t < h → PositiveSemidefinite (B + t • F)) :
    0 ≤ determinantDirection B F := by
  obtain ⟨h, hh, hseg⟩ := hseg
  by_contra! hn
  let q := determinantDirection B F
  let d := F.det
  let u := -q / (|d| + 1)
  have hden : 0 < |d| + 1 := by positivity
  have hu : 0 < u := div_pos (neg_pos.mpr hn) hden
  let t := min h u / 2
  have ht : 0 < t := half_pos (lt_min hh hu)
  have hth : t < h := (half_lt_self (lt_min hh hu)).trans_le (min_le_left h u)
  have htu : t < u := (half_lt_self (lt_min hh hu)).trans_le (min_le_right h u)
  have hbound : t * (|d| + 1) < -q := (lt_div_iff₀ hden).mp htu
  have htd : t * d ≤ t * |d| := mul_le_mul_of_nonneg_left (le_abs_self d) ht.le
  have hneg : q + t * d < 0 := by nlinarith
  have hnonneg := psd_det_nonneg _ (hseg t ht.le hth)
  rw [det_add_smul_two B F hB hF t, hdet] at hnonneg
  have hprod := mul_neg_of_pos_of_neg ht hneg
  change 0 ≤ 0 + t * q + t ^ 2 * d at hnonneg
  nlinarith

/-- In the flat case, the quadratic determinant coefficient is nonnegative. -/
theorem det_direction_nonneg_of_flat_segment
    (B F : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : Symmetric B) (hF : Symmetric F) (hdet : B.det = 0)
    (hflat : determinantDirection B F = 0)
    (hseg : ∃ h : ℝ, 0 < h ∧ ∀ t, 0 ≤ t → t < h → PositiveSemidefinite (B + t • F)) :
    0 ≤ F.det := by
  obtain ⟨h, hh, hseg⟩ := hseg
  have ht : 0 < h / 2 := half_pos hh
  have hp := psd_det_nonneg _ (hseg (h/2) ht.le (half_lt_self hh))
  rw [det_add_smul_two B F hB hF, hdet, hflat] at hp
  simp only [mul_zero, zero_add] at hp
  exact nonneg_of_mul_nonneg_right hp (sq_pos_of_pos ht)

private theorem flat_coordinates (a b c u v w : ℝ) (ha : 0 < a)
    (hB : a*c-b^2=0) (hq : a*w+c*u-2*b*v=0) (hF : 0 ≤ u*w-v^2) :
    ∃ d : ℝ, u=d*a ∧ v=d*b ∧ w=d*c := by
  have hidentity : a^2*(u*w-v^2)+(a*v-b*u)^2 = 0 := by
    linear_combination a*u*hq - u^2*hB
  have hprod : 0 ≤ a^2*(u*w-v^2) := mul_nonneg (sq_nonneg a) hF
  have hcross : a*v-b*u=0 := by
    nlinarith [sq_nonneg (a*v-b*u)]
  have hlast : a*(a*w-c*u)=0 := by
    linear_combination a*hq + 2*b*hcross - 2*u*hB
  have hlast' : a*w-c*u=0 := (mul_eq_zero.mp hlast).resolve_left (ne_of_gt ha)
  refine ⟨u/a, ?_, ?_, ?_⟩
  · field_simp [ne_of_gt ha]
  · field_simp [ne_of_gt ha]
    nlinarith [hcross]
  · field_simp [ne_of_gt ha]
    nlinarith [hlast']

/-- A nonzero singular PSD factor with flat determinant derivative has only a
proportional feasible straight direction. This includes the boundary case
where a generic second-order remainder would not establish PSD. -/
theorem flat_psd_segment_direction_scalar
    (B F : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : PositiveSemidefinite B) (hne : B ≠ 0)
    (hF : Symmetric F) (hdet : B.det = 0)
    (hflat : determinantDirection B F = 0)
    (hseg : ∃ h : ℝ, 0 < h ∧ ∀ t, 0 ≤ t → t < h → PositiveSemidefinite (B + t • F)) :
    ∃ d : ℝ, F = d • B := by
  have hFd := det_direction_nonneg_of_flat_segment B F hB.1 hF hdet hflat hseg
  have hBc : B 0 0 * B 1 1 - (B 0 1)^2=0 := by
    simpa [Matrix.det_fin_two, hB.1 1 0, pow_two] using hdet
  have hFc : 0 ≤ F 0 0 * F 1 1 - (F 0 1)^2 := by
    simpa [Matrix.det_fin_two, hF 1 0, pow_two] using hFd
  rcases nonzero_psd_two_positive_diagonal B hB hne with ha | hc
  · obtain ⟨d, hd0, hd1, hd2⟩ := flat_coordinates _ _ _ _ _ _ ha hBc hflat hFc
    refine ⟨d, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, smul_eq_mul, hF 1 0, hB.1 1 0, hd0, hd1, hd2]
  · have hBc' : B 1 1 * B 0 0 - (B 0 1)^2=0 := by nlinarith [hBc]
    have hFc' : 0 ≤ F 1 1 * F 0 0 - (F 0 1)^2 := by nlinarith [hFc]
    have hq' : B 1 1 * F 0 0 + B 0 0 * F 1 1 - 2 * B 0 1 * F 0 1=0 := by
      dsimp [determinantDirection] at hflat
      nlinarith [hflat]
    obtain ⟨d, hd0, hd1, hd2⟩ := flat_coordinates _ _ _ _ _ _ hc hBc' hq' hFc'
    refine ⟨d, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, smul_eq_mul, hF 1 0, hB.1 1 0, hd0, hd1, hd2]

/-- For a symmetric matrix of size two, positive trace and nonnegative
 determinant already suffice for PSD. -/
theorem psd_two_of_trace_pos_det_nonneg
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hs : Symmetric B)
    (htrace : 0 < B.trace) (hdet : 0 ≤ B.det) : PositiveSemidefinite B := by
  apply (psd_fin_two_iff B).mpr
  have ht : 0 < B 0 0 + B 1 1 := by simpa [Matrix.trace_fin_two] using htrace
  have hd : 0 ≤ B 0 0 * B 1 1 - (B 0 1)^2 := by
    simpa [Matrix.det_fin_two, hs 1 0, pow_two] using hdet
  refine ⟨hs, ?_, ?_, hdet⟩
  · by_contra! hn
    have hc : 0 < B 1 1 := by linarith
    nlinarith [mul_neg_of_neg_of_pos hn hc, sq_nonneg (B 0 1)]
  · by_contra! hn
    have ha : 0 < B 0 0 := by linarith
    nlinarith [mul_neg_of_pos_of_neg ha hn, sq_nonneg (B 0 1)]

#assert_trust kernel determinantDirection_nonneg_of_segment
#assert_trust kernel det_direction_nonneg_of_flat_segment
#assert_trust kernel flat_psd_segment_direction_scalar
#assert_trust kernel psd_two_of_trace_pos_det_nonneg
#print axioms flat_psd_segment_direction_scalar

end NLA.Proofs.PF05
