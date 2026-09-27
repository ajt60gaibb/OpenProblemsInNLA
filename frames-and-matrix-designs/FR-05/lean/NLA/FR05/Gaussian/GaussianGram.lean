import NLA.FR05.Gaussian.GaussianProjection
import NLA.FR05.Gaussian.GaussianFrameRows

/-!
# Gaussian projection laws determined by Gram matrices

Characteristic functions identify joint projection laws, with no rank or
nondegeneracy assumption. Orthonormal projections and unitary invariance are
consequences, used by both the density and likelihood arguments.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators

namespace NLA.FR05

/-- Joint adjoint projections of the conjugate row stored in the frame. -/
def gaussianMatrixProjection {n : ℕ} {ι : Type*}
    (B : Matrix (Fin n) ι ℂ) (x : Signal n) : EuclideanSpace ℂ ι :=
  toLp 2 (Bᴴ *ᵥ star x)

/-- The adjoint projection of a conjugated Gaussian row is continuous. -/
@[fun_prop]
theorem continuous_gaussianMatrixProjection {n : ℕ} {ι : Type*}
    (B : Matrix (Fin n) ι ℂ) : Continuous (gaussianMatrixProjection B) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  change Continuous (fun x : Signal n ↦ ∑ i, star (B i j) * star (x i))
  fun_prop

/-- Real scalar projections of the joint map are scalar complex dot products. -/
theorem gaussianMatrixProjection_real_inner {n : ℕ} {ι : Type*} [Fintype ι]
    (B : Matrix (Fin n) ι ℂ) (x : Signal n) (t : EuclideanSpace ℂ ι) :
    inner ℝ (gaussianMatrixProjection B x) t =
      (star x ⬝ᵥ star (B *ᵥ ofLp t)).re := by
  rw [real_inner_comm, PiLp.inner_apply]
  change (∑ j, ((Bᴴ *ᵥ star x) j * star (t j)).re) = _
  rw [← Complex.re_sum]
  change ((Bᴴ *ᵥ star x) ⬝ᵥ star (ofLp t)).re = _
  rw [dotProduct_comm, dotProduct_mulVec, vecMul_conjTranspose, star_star, dotProduct_comm]

/-- Conjugation preserves squared Euclidean energy. -/
theorem signalEnergy_star {n : ℕ} (x : Signal n) :
    signalEnergy (star x) = signalEnergy x := by
  simp [signalEnergy, squaredEuclideanNorm]

/-- Squared Euclidean energy is the real part of the Hermitian self-product. -/
theorem signalEnergy_eq_star_dotProduct {n : ℕ} (x : Signal n) :
    signalEnergy x = (star x ⬝ᵥ x).re := by
  simp [signalEnergy, squaredEuclideanNorm, dotProduct, Complex.mul_re,
    Complex.normSq_apply]

/-- The energy after a matrix map is the quadratic form of its Gram matrix. -/
theorem signalEnergy_mulVec_eq_gram {n : ℕ} {ι : Type*} [Fintype ι]
    (B : Matrix (Fin n) ι ℂ) (t : ι → ℂ) :
    signalEnergy (B *ᵥ t) = (star t ⬝ᵥ ((Bᴴ * B) *ᵥ t)).re := by
  rw [signalEnergy_eq_star_dotProduct, star_mulVec, ← dotProduct_mulVec,
    mulVec_mulVec]

/-- The joint characteristic function is fixed by the Gram matrix. -/
theorem charFun_gaussianMatrixProjection {n : ℕ} {ι : Type*} [Fintype ι]
    (B : Matrix (Fin n) ι ℂ) (t : EuclideanSpace ℂ ι) :
    charFun ((standardComplexGaussianTail n).map (gaussianMatrixProjection B)) t =
      charFun (gaussianReal 0 (signalEnergy (B *ᵥ ofLp t) / 2).toNNReal) 1 := by
  have hm := (continuous_gaussianMatrixProjection B).measurable
  have hz := measurable_real_star_dotProduct (star (B *ᵥ ofLp t))
  have hlaw := standardComplexGaussianTail_map_real_dotProduct (star (B *ᵥ ofLp t))
  rw [signalEnergy_star] at hlaw
  rw [← hlaw, charFun_apply, integral_map hm.aemeasurable (by fun_prop),
    charFun_apply_real, integral_map hz.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [gaussianMatrixProjection_real_inner, Complex.ofReal_one, one_mul]

/-- The joint characteristic function is the exponential of the Gram quadratic form. -/
theorem charFun_gaussianMatrixProjection_eq_exp {n : ℕ} {ι : Type*} [Fintype ι]
    (B : Matrix (Fin n) ι ℂ) (t : EuclideanSpace ℂ ι) :
    charFun ((standardComplexGaussianTail n).map (gaussianMatrixProjection B)) t =
      Complex.exp (-((signalEnergy (B *ᵥ ofLp t) / 4 : ℝ) : ℂ)) := by
  have h : 0 ≤ signalEnergy (B *ᵥ ofLp t) / 2 :=
    div_nonneg (Finset.sum_nonneg (fun _ _ ↦ Complex.normSq_nonneg _)) (by norm_num)
  rw [charFun_gaussianMatrixProjection, charFun_gaussianReal]
  congr 1
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_zero, zero_mul,
    zero_sub, one_pow, mul_one, Real.coe_toNNReal _ h, Complex.ofReal_div,
    Complex.ofReal_ofNat]
  ring

/-- Equal Gram matrices give equal projection laws, including singular cases. -/
theorem gaussianMatrixProjection_law_eq_of_gram
    {n m : ℕ} {ι : Type*} [Finite ι]
    (B : Matrix (Fin n) ι ℂ) (C : Matrix (Fin m) ι ℂ) (h : Bᴴ * B = Cᴴ * C) :
    (standardComplexGaussianTail n).map (gaussianMatrixProjection B) =
      (standardComplexGaussianTail m).map (gaussianMatrixProjection C) := by
  let : Fintype ι := Fintype.ofFinite ι
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_gaussianMatrixProjection, charFun_gaussianMatrixProjection,
    signalEnergy_mulVec_eq_gram, signalEnergy_mulVec_eq_gram, h]

/-- Orthonormal adjoint projections preserve the standard complex Gaussian law. -/
theorem standardComplexGaussianTail_map_orthonormal {n m : ℕ}
    (B : Matrix (Fin n) (Fin m) ℂ) (hB : Bᴴ * B = 1) :
    (standardComplexGaussianTail n).map (fun x ↦ Bᴴ *ᵥ star x) =
      standardComplexGaussianTail m := by
  have h := gaussianMatrixProjection_law_eq_of_gram B (1 : Matrix (Fin m) (Fin m) ℂ)
    (by simpa using hB)
  have hm := congrArg (Measure.map (ofLp : EuclideanSpace ℂ (Fin m) → Fin m → ℂ)) h
  rw [Measure.map_map (by fun_prop) (continuous_gaussianMatrixProjection _).measurable,
    Measure.map_map (by fun_prop) (continuous_gaussianMatrixProjection _).measurable] at hm
  simpa [Function.comp_def, gaussianMatrixProjection, standardComplexGaussianTail_map_star] using hm

/-- A unitary change of the conjugated row coordinates preserves the Gaussian law. -/
theorem standardComplexGaussianTail_map_unitary {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) :
    (standardComplexGaussianTail n).map (fun x ↦ star (Uᴴ *ᵥ star x)) =
      standardComplexGaussianTail n := by
  have h := gaussianMatrixProjection_law_eq_of_gram U (1 : Matrix (Fin n) (Fin n) ℂ)
    (by simpa using hU)
  have h' := congrArg (Measure.map (fun y : EuclideanSpace ℂ (Fin n) ↦ star (ofLp y))) h
  rw [Measure.map_map (by fun_prop) (continuous_gaussianMatrixProjection U).measurable,
    Measure.map_map (by fun_prop) (continuous_gaussianMatrixProjection 1).measurable] at h'
  simpa [Function.comp_def, gaussianMatrixProjection] using h'

/-- Unitary matrix multiplication preserves the standard complex Gaussian law. -/
theorem standardComplexGaussianTail_map_unitary_mulVec {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) :
    (standardComplexGaussianTail n).map (fun x ↦ U *ᵥ x) = standardComplexGaussianTail n := by
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have h := standardComplexGaussianTail_map_orthonormal Uᴴ (by simpa using hUU)
  rw [← standardComplexGaussianTail_map_star n,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simpa [Function.comp_def, standardComplexGaussianTail_map_star] using h

end NLA.FR05
