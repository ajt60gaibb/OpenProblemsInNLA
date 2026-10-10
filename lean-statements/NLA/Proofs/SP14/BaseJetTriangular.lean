import NLA.Proofs.SP14.JetVanishingMultiplicity

/-!
The explicit real triangular base-pencil jet map from the SP-14 source.
This constructs a right inverse for its finite linear system; identifying
it with the actual corrected Toeplitz jet remains a separate theorem.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- The source's normalized real half-binomial coefficient. -/
noncomputable def baseCoeffReal (k : ℕ) : ℝ := Ring.choose (1 / 2 : ℝ) k

/-- The first `h` rows and `h` correction columns of the exact base Jacobian. -/
noncomputable def baseJetMatrix (h : ℕ) : Matrix (Fin h) (Fin h) ℝ :=
  fun k d => if k ≤ d then
    -2 * (k.val + 1 : ℝ) * baseCoeffReal (d.val - k.val) else 0

theorem baseCoeffReal_zero : baseCoeffReal 0 = 1 := by
  simp [baseCoeffReal]

theorem baseCoeffReal_to_complex (k : ℕ) :
    ((baseCoeffReal k : ℝ) : ℂ) = baseCoeff k := by
  have h := Ring.map_choose (algebraMap ℝ ℂ) (1 / 2 : ℝ) k
  simpa [baseCoeffReal, baseCoeff] using h

theorem baseJetMatrix_upper (h : ℕ) : (baseJetMatrix h).IsUpperTriangular := by
  intro k d hdk
  change d < k at hdk
  simp [baseJetMatrix, not_le.mpr hdk]

theorem baseJetMatrix_diag (h : ℕ) (k : Fin h) :
    baseJetMatrix h k k = -2 * (k.val + 1 : ℝ) := by
  simp [baseJetMatrix, baseCoeffReal_zero]

theorem baseJetMatrix_det (h : ℕ) :
    (baseJetMatrix h).det = ∏ k : Fin h, (-2 * (k.val + 1 : ℝ)) := by
  rw [Matrix.det_of_isUpperTriangular (baseJetMatrix_upper h)]
  simp [baseJetMatrix_diag]

theorem baseJetMatrix_det_ne_zero (h : ℕ) : (baseJetMatrix h).det ≠ 0 := by
  rw [baseJetMatrix_det]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have : (k.val + 1 : ℝ) ≠ 0 := by positivity
  exact mul_ne_zero (by norm_num) this

/-- The explicit real solve via the nonsingular inverse of the displayed
source matrix. -/
noncomputable def baseJetSolve (h : ℕ) (y : Fin h → ℝ) : Fin h → ℝ :=
  (baseJetMatrix h)⁻¹.mulVec y

theorem baseJetSolve_spec (h : ℕ) (y : Fin h → ℝ) :
    (baseJetMatrix h).mulVec (baseJetSolve h y) = y := by
  have hunit : IsUnit (baseJetMatrix h).det :=
    isUnit_iff_ne_zero.mpr (baseJetMatrix_det_ne_zero h)
  simp [baseJetSolve, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit]

theorem baseJetSolve_unique (h : ℕ) (y : Fin h → ℝ) :
    ∃! x : Fin h → ℝ, (baseJetMatrix h).mulVec x = y := by
  refine ⟨baseJetSolve h y, baseJetSolve_spec h y, ?_⟩
  intro x hx
  have hunit : IsUnit (baseJetMatrix h).det :=
    isUnit_iff_ne_zero.mpr (baseJetMatrix_det_ne_zero h)
  calc
    x = (baseJetMatrix h)⁻¹.mulVec ((baseJetMatrix h).mulVec x) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
    _ = baseJetSolve h y := by rw [hx]; rfl

#assert_trust kernel baseJetMatrix_det_ne_zero
#assert_trust kernel baseCoeffReal_to_complex
#assert_trust kernel baseJetSolve_spec
#assert_trust kernel baseJetSolve_unique
#print axioms baseJetSolve_unique

end NLA.Proofs.SP14
