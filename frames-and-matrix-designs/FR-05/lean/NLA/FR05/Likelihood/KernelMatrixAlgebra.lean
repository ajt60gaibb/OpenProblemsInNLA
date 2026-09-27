import NLA.FR05.Likelihood.KernelMoments

set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Real Matrix WithLp
open scoped BigOperators

namespace NLA.FR05

theorem overlapOperatorNorm_mul (A B : SourceOverlapMatrix) :
    overlapOperatorNorm (A * B) ≤ overlapOperatorNorm A * overlapOperatorNorm B := by
  unfold overlapOperatorNorm
  rw [map_mul]
  exact norm_mul_le _ _

theorem overlapOperatorNorm_add (A B : SourceOverlapMatrix) :
    overlapOperatorNorm (A + B) ≤ overlapOperatorNorm A + overlapOperatorNorm B := by
  unfold overlapOperatorNorm
  rw [map_add]
  exact norm_add_le _ _

theorem overlapOperatorNorm_neg (A : SourceOverlapMatrix) :
    overlapOperatorNorm (-A) = overlapOperatorNorm A := by
  unfold overlapOperatorNorm
  rw [map_neg, norm_neg]

theorem overlapOperatorNorm_real_smul (x : ℝ) (A : SourceOverlapMatrix) :
    overlapOperatorNorm (x • A) = |x| * overlapOperatorNorm A := by
  unfold overlapOperatorNorm
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) ((x : ℂ) • A)‖ = _
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]

theorem overlapFrobeniusSq_le (K : SourceOverlapMatrix) :
    overlapFrobeniusSq K ≤ 2 * overlapOperatorNorm K ^ 2 := by
  have h0 := overlapColumnEnergy_le K 0
  have h1 := overlapColumnEnergy_le K 1
  have he : overlapFrobeniusSq K = overlapColumnEnergy K 0 + overlapColumnEnergy K 1 := by
    simp [overlapFrobeniusSq, overlapColumnEnergy, Fin.sum_univ_two]
    ring
  rw [he]
  linarith

def kernelTotalRadius (p : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : ℝ :=
  sourceRadiusSq p.1 + sourceRadiusSq p.2

def kernelEvenQuadratic (K : SourceOverlapMatrix)
    (p : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : ℝ :=
  sourceRadiusSq (Kᴴ *ᵥ p.1) + sourceRadiusSq (K *ᵥ p.2)

def kernelAdjugateResidual (K : SourceOverlapMatrix) : SourceOverlapMatrix :=
  ((1 - overlapFrobeniusSq K : ℝ) : ℂ) • (1 : SourceOverlapMatrix) + Kᴴ * K

theorem kernelAdjugateResidual_eq (K : SourceOverlapMatrix) :
    kernelAdjugateResidual K = (overlapResidualMatrix K).adjugate := by
  rw [overlapResidualMatrix_eq, Matrix.adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kernelAdjugateResidual, overlapColumnEnergy, overlapColumnCross,
      overlapFrobeniusSq, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.ext_iff, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring_nf <;> simp

def kernelEvenExponent (K : SourceOverlapMatrix)
    (p : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : ℝ :=
  (kernelEvenQuadratic K p - Complex.normSq K.det * kernelTotalRadius p) / overlapDeterminant K

def kernelOddExponent (K : SourceOverlapMatrix)
    (p : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : ℝ :=
  2 * (coneInner p.1 (K *ᵥ (kernelAdjugateResidual K *ᵥ p.2))).re / overlapDeterminant K

theorem overlapGaussianRatio_exponents {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) (z w : Fin 2 → ℂ) :
    overlapGaussianRatio K z w = (overlapDeterminant K)⁻¹ *
      Real.exp (-kernelEvenExponent K (z, w) + kernelOddExponent K (z, w)) := by
  have hΔ := (overlapDeterminant_pos hK).ne'
  unfold overlapGaussianRatio
  congr 2
  rw [overlapResidualMatrix_inverse, ← Complex.ofReal_inv]
  unfold kernelEvenExponent kernelOddExponent kernelEvenQuadratic kernelTotalRadius
  simp only [kernelAdjugateResidual_eq, overlapResidualMatrix_eq, Matrix.adjugate_fin_two_of,
    sourceRadiusSq, coneInner, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, Pi.sub_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im,
    mul_zero, zero_mul, add_zero, sub_zero, neg_neg]
  field_simp [hΔ]
  rw [overlapDeterminant_identity]
  simp [overlapFrobeniusSq, overlapColumnEnergy, overlapColumnCross,
    Matrix.det_fin_two, Fin.sum_univ_two, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

end NLA.FR05
