import NLA.Proofs.RA10.MatrixFunctionalCalculus
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! A two-dimensional comparison excludes a corner in a concave matrix-monotone
function. This proves differentiability without invoking Bendat--Sherman. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Matrix Filter Set Topology
open scoped BigOperators Matrix
open NLA.Statements.RA10

namespace NLA.Proofs.RA10

/-- The two matrices differ by a positive rank-one matrix. The test vector
(1,-1) is in its kernel, detecting unequal one-sided derivatives. -/
theorem operatorMonotone_corner_inequality {f : ℝ → ℝ}
    (hf : OperatorMonotoneOnPositive f) {c ε : ℝ} (hε : 0 < ε) (hc : 2 * ε < c) :
    0 ≤ f (c + ε) + f (c - ε) - (8 / 5) * f (c + ε / 2) - (2 / 5) * f (c - 2 * ε) := by
  let q := Real.sqrt (1 / 10 : ℝ)
  have hq : q ^ 2 = 1 / 10 := Real.sq_sqrt (by norm_num)
  let Q : Matrix (Fin 2) (Fin 2) ℝ := !![3 * q, q; -q, 3 * q]
  let a : Fin 2 → ℝ := ![c + ε / 2, c - 2 * ε]
  let b : Fin 2 → ℝ := ![c + ε, c - ε]
  let A := SpectralMatrix a Q
  let B := diagonal b
  have hQ : Q.transpose * Q = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [hq]
  have hu : IsUnit Q := isUnit_iff_exists_inv.mpr ⟨Q.transpose, mul_eq_one_comm.mp hQ⟩
  have hA : A.PosDef := by
    rw [show A = Q * diagonal a * Q.transpose from spectralMatrix_factor a Q]
    apply hu.posDef_star_right_conjugate_iff.mpr
    apply PosDef.diagonal
    intro i
    fin_cases i <;> dsimp [a] <;> linarith
  have hB : B.PosDef := by
    apply PosDef.diagonal
    intro i
    fin_cases i <;> dsimp [b] <;> linarith
  have heq : B - A = (3 * ε / 4) • !![(1 : ℝ), 1; 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, B, a, b, Q, SpectralMatrix, Fin.sum_univ_two] <;>
      ring_nf <;> rw [hq] <;> ring
  have hBA : (B - A).PosSemidef := by
    rw [heq]
    apply PosSemidef.smul _ (by positivity)
    apply PosSemidef.of_dotProduct_mulVec_nonneg (by
      apply Matrix.isHermitian_iff_isSymm.mpr
      ext i j
      fin_cases i <;> fin_cases j <;> rfl)
    intro v
    simp [dotProduct, mulVec, Fin.sum_univ_two]
    nlinarith [sq_nonneg (v 0 + v 1)]
  have h := (operatorMonotoneOnPositive_cfc hf hB hA hBA).dotProduct_mulVec_nonneg ![1, -1]
  rw [← functionMatrix_eq_cfc f hQ (show A = SpectralMatrix a Q from rfl),
    matrix_cfc_diagonal f b] at h
  simp [FunctionMatrix, SpectralMatrix, Q, a, b, dotProduct, mulVec, Fin.sum_univ_two] at h
  ring_nf at h
  rw [hq] at h
  ring_nf at h ⊢
  exact h

/-- Scalar concavity gives the one-sided derivatives; matrix monotonicity
forces them to coincide via the preceding rank-one comparison. -/
theorem operatorMonotone_differentiableAt_of_concave {f : ℝ → ℝ}
    (hf : OperatorMonotoneOnPositive f) (hconc : ConcaveOn ℝ (Ioi 0) f)
    {c : ℝ} (hc : 0 < c) : DifferentiableAt ℝ f c := by
  have hci : c ∈ interior (Ioi (0 : ℝ)) := by simpa using hc
  let L := -derivWithin (-f) (Iio c) c
  let R := -derivWithin (-f) (Ioi c) c
  have hL : HasDerivWithinAt f L (Iio c) c := by
    simpa only [neg_neg] using (hconc.neg.hasDerivWithinAt_leftDeriv_of_mem_interior hci).neg
  have hR : HasDerivWithinAt f R (Ioi c) c := by
    simpa only [neg_neg] using (hconc.neg.hasDerivWithinAt_rightDeriv_of_mem_interior hci).neg
  have hRL : R ≤ L := neg_le_neg (hconc.neg.leftDeriv_le_rightDeriv_of_mem_interior hci)
  have hLt : Tendsto (slope f c) (𝓝[<] c) (𝓝 L) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hL
  have hRt : Tendsto (slope f c) (𝓝[>] c) (𝓝 R) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hR
  let s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hs : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hspos (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hshift (r : ℝ) : Tendsto (fun n => c + r * s n) atTop (𝓝 c) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (hs.const_mul r)
  have hleft (r : ℝ) (hr : r < 0) :
      Tendsto (fun n => c + r * s n) atTop (𝓝[<] c) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hshift r, Eventually.of_forall fun n => ?_⟩
    exact add_lt_of_neg_right _ (mul_neg_of_neg_of_pos hr (hspos n))
  have hright (r : ℝ) (hr : 0 < r) :
      Tendsto (fun n => c + r * s n) atTop (𝓝[>] c) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hshift r, Eventually.of_forall fun n => ?_⟩
    exact lt_add_of_pos_right _ (mul_pos hr (hspos n))
  have hlim := (((hRt.comp (hright 1 (by norm_num))).sub
    (hLt.comp (hleft (-1) (by norm_num)))).sub
      ((hRt.comp (hright (1 / 2) (by norm_num))).const_mul (4 / 5))).add
        ((hLt.comp (hleft (-2) (by norm_num))).const_mul (4 / 5))
  have hnonneg : 0 ≤ R - L - (4 / 5) * R + (4 / 5) * L := by
    apply ge_of_tendsto hlim
    have hsmall := hs.eventually (gt_mem_nhds (show (0 : ℝ) < c / 2 by positivity))
    filter_upwards [hsmall] with n hn
    dsimp only [Function.comp_def]
    have hcorner := operatorMonotone_corner_inequality hf (hspos n)
      (show 2 * s n < c by linarith)
    have h₁ := sub_smul_slope f c (c + s n)
    have h₂ := sub_smul_slope f c (c - s n)
    have h₃ := sub_smul_slope f c (c + s n / 2)
    have h₄ := sub_smul_slope f c (c - 2 * s n)
    simp only [smul_eq_mul, vsub_eq_sub] at h₁ h₂ h₃ h₄
    have heq₁ : c + 1 * s n = c + s n := by ring
    have heq₂ : c + -1 * s n = c - s n := by ring
    have heq₃ : c + 1 / 2 * s n = c + s n / 2 := by ring
    have heq₄ : c + -2 * s n = c - 2 * s n := by ring
    rw [heq₁, heq₂, heq₃, heq₄]
    apply nonneg_of_mul_nonneg_left _ (hspos n)
    nlinarith [hcorner]
  have heq : L = R := by linarith
  exact (hasDerivAt_iff_tendsto_slope_left_right.mpr ⟨heq ▸ hLt, hRt⟩).differentiableAt

theorem normalizedProfile_differentiableAt {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) {c : ℝ} (hc : 0 < c) :
    DifferentiableAt ℝ (positiveProfileExtension g) c :=
  operatorMonotone_differentiableAt_of_concave
    (normalizedAdmissibleCompactClass_operatorMonotone hg)
    (normalizedAdmissibleCompactClass_concaveOn hg) hc

#assert_trust kernel operatorMonotone_corner_inequality
#assert_trust kernel operatorMonotone_differentiableAt_of_concave
#assert_trust kernel normalizedProfile_differentiableAt
#print axioms normalizedProfile_differentiableAt

end NLA.Proofs.RA10
