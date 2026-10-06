/-
Released under Apache 2.0; see LICENSE.
Centered Gaussian Frobenius concentration, proved directly from pinned Mathlib
and the kernel-checked scalar quadratic MGF. The independently approved exact
specification is in reviews/gaussian-frobenius-specification.md.
-/
import NLA.IE06.GaussianNull
import NLA.IE06.GaussianQuadratic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator RealInnerProductSpace
namespace NLA.IE06.GaussianFrobenius
open GaussianQuadratic

/-- Literal sum of squared entries, including empty matrices. -/
def frobeniusSq {r c : ℕ} (A : Matrix (Fin r) (Fin c) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- The genuine induced Euclidean norm; the domain is Euclidean column space. -/
def euclideanOpNorm {r c : ℕ} (A : Matrix (Fin r) (Fin c) ℝ) : ℝ :=
  ‖((Matrix.toEuclideanLin (𝕜 := ℝ)).trans LinearMap.toContinuousLinearMap) A‖

theorem euclideanOpNorm_eq_l2 {r c : ℕ} (A : Matrix (Fin r) (Fin c) ℝ) :
    euclideanOpNorm A = ‖A‖ := rfl

private def gram {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ) := M * Mᴴ
private theorem gram_hermitian {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ) :
    (gram M).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self M
private def weights {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ) :=
  (gram_hermitian M).eigenvalues
private def eigenbasis {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ) :=
  (gram_hermitian M).eigenvectorBasis

private theorem weights_bounds {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ) (i : Fin n) :
    0 ≤ weights M i ∧ weights M i ≤ euclideanOpNorm M ^ 2 := by
  have hnonneg : 0 ≤ weights M i :=
    Matrix.eigenvalues_self_mul_conjTranspose_nonneg M i
  refine ⟨hnonneg, ?_⟩
  let : Nonempty (Fin n) := ⟨i⟩
  have h := spectrum.norm_le_norm_of_mem ((gram_hermitian M).eigenvalues_mem_spectrum_real i)
  have hnorm : ‖gram M‖ = euclideanOpNorm M ^ 2 := by
    have hh := Matrix.l2_opNorm_conjTranspose_mul_self Mᴴ
    rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at hh
    simpa [gram, euclideanOpNorm_eq_l2, pow_two] using hh
  change ‖weights M i‖ ≤ ‖gram M‖ at h
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg, hnorm] using h

private theorem weights_sum {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ) :
    (∑ i, weights M i) = frobeniusSq M := by
  have h := Matrix.IsHermitian.trace_eq_sum_eigenvalues (gram_hermitian M)
  simpa [weights, gram, Matrix.trace, Matrix.diag, Matrix.mul_apply, frobeniusSq, pow_two] using h.symm

private def rowEnergy {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ j, (z ᵥ* M) j ^ 2

private theorem rowEnergy_gram {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ)
    (z : Fin n → ℝ) : rowEnergy M z = z ⬝ᵥ (gram M *ᵥ z) := by
  rw [gram, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  simp [rowEnergy, dotProduct, pow_two, Matrix.conjTranspose, Matrix.mulVec, Matrix.vecMul,
    mul_comm]

private def rotate {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (z : Fin n → ℝ) : Fin n → ℝ :=
  ofLp (∑ i, z i • b i)

private theorem rotate_continuous {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) : Continuous (rotate b) := by
  unfold rotate
  fun_prop

private theorem rowEnergy_rotate {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ)
    (z : Fin n → ℝ) : rowEnergy M (rotate (eigenbasis M) z) = weightedSquares (weights M) z := by
  let b := eigenbasis M
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (gram M)
  have hT (i : Fin n) : T (b i) = weights M i • b i := by
    apply (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).injective
    exact (gram_hermitian M).mulVec_eigenvectorBasis i
  rw [rowEnergy_gram]
  rw [← Matrix.inner_toEuclideanCLM (gram M) (toLp 2 (rotate (eigenbasis M) z))
    (toLp 2 (rotate (eigenbasis M) z))]
  change ⟪(∑ i, z i • b i), T (∑ i, z i • b i)⟫ = _
  simp_rw [map_sum, map_smul, hT, smul_smul, inner_sum, sum_inner,
    real_inner_smul_left, real_inner_smul_right, b.inner_eq_ite]
  simp [weightedSquares, pow_two, mul_assoc, mul_comm, mul_left_comm]

private theorem rotate_gaussian {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    (gaussianVector n).map (rotate b) = gaussianVector n := by
  have h := map_pi_eq_stdGaussian (ι := Fin n)
  rw [stdGaussian_eq_map_pi_orthonormalBasis b] at h
  have hh := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ.map ofLp) h
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at hh
  change (gaussianVector n).map (fun z => ofLp (∑ i, z i • b i)) = gaussianVector n
  simpa [Function.comp_def, gaussianVector] using hh.symm

private theorem rowEnergy_continuous {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ) :
    Continuous (rowEnergy M) := by
  unfold rowEnergy Matrix.vecMul dotProduct
  fun_prop

private theorem row_mgf_bound {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ)
    (hL : 0 < euclideanOpNorm M ^ 2) :
    Integrable (fun z => Real.exp ((1 / (4 * euclideanOpNorm M ^ 2)) * rowEnergy M z))
      (gaussianVector n) ∧
    (∫ z, Real.exp ((1 / (4 * euclideanOpNorm M ^ 2)) * rowEnergy M z)
        ∂gaussianVector n) ≤ Real.exp (frobeniusSq M / (2 * euclideanOpNorm M ^ 2)) := by
  let f := fun z => Real.exp ((1 / (4 * euclideanOpNorm M ^ 2)) * rowEnergy M z)
  have hf : Continuous f := by
    exact Real.continuous_exp.comp (continuous_const.mul (rowEnergy_continuous M))
  have hrot := (rotate_continuous (eigenbasis M)).measurable
  have hcomp : f ∘ rotate (eigenbasis M) =
      (fun z => Real.exp ((1 / (4 * euclideanOpNorm M ^ 2)) * weightedSquares (weights M) z)) := by
    funext z
    simp only [Function.comp_apply, f, rowEnergy_rotate]
  obtain ⟨hi, hb⟩ := weighted_mgf_bound (weights M) (euclideanOpNorm M ^ 2) hL
    (weights_bounds M)
  have him : Integrable f ((gaussianVector n).map (rotate (eigenbasis M))) := by
    apply (integrable_map_measure hf.aestronglyMeasurable hrot.aemeasurable).mpr
    simpa only [hcomp] using hi
  rw [rotate_gaussian] at him
  refine ⟨him, ?_⟩
  change (∫ z, f z ∂gaussianVector n) ≤ _
  rw [← rotate_gaussian (eigenbasis M), integral_map hrot.aemeasurable hf.aestronglyMeasurable]
  simpa only [← Function.comp_apply (f := f), hcomp, weights_sum] using hb

private theorem frobeniusSq_mul_rows {m n p : ℕ}
    (G : GaussianNull.RectMat m n) (M : Matrix (Fin n) (Fin p) ℝ) :
    frobeniusSq (Matrix.of G * M) = ∑ i, rowEnergy M (G i) := rfl

private theorem matrix_exp_product {m n p : ℕ}
    (G : GaussianNull.RectMat m n) (M : Matrix (Fin n) (Fin p) ℝ) (t : ℝ) :
    Real.exp (t * frobeniusSq (Matrix.of G * M)) = ∏ i, Real.exp (t * rowEnergy M (G i)) := by
  rw [frobeniusSq_mul_rows, Finset.mul_sum, Real.exp_sum]

private theorem matrix_mgf_bound {m n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ)
    (hL : 0 < euclideanOpNorm M ^ 2) :
    Integrable (fun G : GaussianNull.RectMat m n =>
      Real.exp ((1 / (4 * euclideanOpNorm M ^ 2)) * frobeniusSq (Matrix.of G * M)))
      (GaussianNull.gaussianRect m n) ∧
    (∫ G : GaussianNull.RectMat m n, Real.exp ((1 / (4 * euclideanOpNorm M ^ 2)) * frobeniusSq (Matrix.of G * M))
        ∂GaussianNull.gaussianRect m n) ≤
      Real.exp ((m : ℝ) * frobeniusSq M / (2 * euclideanOpNorm M ^ 2)) := by
  obtain ⟨hi, hb⟩ := row_mgf_bound M hL
  simp_rw [matrix_exp_product]
  constructor
  · exact Integrable.fintype_prod (fun _ : Fin m => hi)
  · change (∫ G : Fin m → Fin n → ℝ, ∏ i, Real.exp ((1 / (4 * euclideanOpNorm M ^ 2)) * rowEnergy M (G i))
      ∂Measure.pi (fun _ : Fin m => gaussianVector n)) ≤ _
    rw [integral_fintype_prod_eq_prod
      (fun _ : Fin m => fun z => Real.exp ((1 / (4 * euclideanOpNorm M ^ 2)) * rowEnergy M z))]
    calc
      _ ≤ ∏ _ : Fin m, Real.exp (frobeniusSq M / (2 * euclideanOpNorm M ^ 2)) := by
        apply Finset.prod_le_prod
        · intro i _
          exact integral_nonneg (fun _ => (Real.exp_pos _).le)
        · intro i _
          exact hb
      _ = _ := by
        rw [← Real.exp_sum]
        congr 1
        simp [mul_div_assoc]

theorem frobeniusSq_continuous {r c : ℕ} :
    Continuous (frobeniusSq : Matrix (Fin r) (Fin c) ℝ → ℝ) := by
  unfold frobeniusSq
  fun_prop

theorem frobenius_exceedance_measurable {m n p : ℕ}
    (M : Matrix (Fin n) (Fin p) ℝ) (a : ℝ) :
    MeasurableSet {G : GaussianNull.RectMat m n | a < frobeniusSq (Matrix.of G * M)} := by
  have hc : Continuous (fun G : GaussianNull.RectMat m n => frobeniusSq (Matrix.of G * M)) := by
    unfold frobeniusSq
    simp only [Matrix.mul_apply]
    fun_prop
  exact (isOpen_lt continuous_const hc).measurableSet

/-- Centered Gaussian Frobenius concentration with the exact Euclidean operator
norm and constants in manuscript Lemma4.1. All dimensions, including zero, are
allowed. The Gaussian law and all transformation facts are proved concretely. -/
theorem centered_gaussian_frobenius_tail {m n p : ℕ}
    (M : Matrix (Fin n) (Fin p) ℝ) (x : ℝ) (_hx : 0 < x) :
    GaussianNull.gaussianRect m n
      {G : GaussianNull.RectMat m n | 2 * (m : ℝ) * frobeniusSq M + 4 * x * euclideanOpNorm M ^ 2 <
        frobeniusSq (Matrix.of G * M)} ≤ ENNReal.ofReal (Real.exp (-x)) := by
  by_cases hM : M = 0
  · subst M
    simp [frobeniusSq, euclideanOpNorm, Matrix.mul_zero, Set.ofPred_false]
  have hn : euclideanOpNorm M ≠ 0 := by
    rw [euclideanOpNorm_eq_l2]
    exact norm_ne_zero_iff.mpr hM
  have hL : 0 < euclideanOpNorm M ^ 2 := sq_pos_of_ne_zero hn
  let : IsProbabilityMeasure (GaussianNull.gaussianRect m n) := by
    unfold GaussianNull.gaussianRect
    infer_instance
  obtain ⟨hi, hmgf⟩ := matrix_mgf_bound (m := m) M hL
  have ht : 0 ≤ (1 : ℝ) / (4 * euclideanOpNorm M ^ 2) := by positivity
  have hchernoff := measure_ge_le_exp_mul_mgf
    (μ := GaussianNull.gaussianRect m n) (X := fun G : GaussianNull.RectMat m n => frobeniusSq (Matrix.of G * M))
    (2 * (m : ℝ) * frobeniusSq M + 4 * x * euclideanOpNorm M ^ 2) ht hi
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr
  change (GaussianNull.gaussianRect m n).real _ ≤ _
  calc
    (GaussianNull.gaussianRect m n).real
        {G : GaussianNull.RectMat m n | 2 * (m : ℝ) * frobeniusSq M + 4 * x * euclideanOpNorm M ^ 2 <
          frobeniusSq (Matrix.of G * M)} ≤
      (GaussianNull.gaussianRect m n).real
        {G : GaussianNull.RectMat m n | 2 * (m : ℝ) * frobeniusSq M + 4 * x * euclideanOpNorm M ^ 2 ≤
          frobeniusSq (Matrix.of G * M)} := measureReal_mono (by
            intro G hG
            change 2 * (m : ℝ) * frobeniusSq M + 4 * x * euclideanOpNorm M ^ 2 ≤
              frobeniusSq (Matrix.of G * M)
            exact le_of_lt hG)
    _ ≤ Real.exp (-(1 / (4 * euclideanOpNorm M ^ 2)) *
          (2 * (m : ℝ) * frobeniusSq M + 4 * x * euclideanOpNorm M ^ 2)) *
        (∫ G : GaussianNull.RectMat m n, Real.exp ((1 / (4 * euclideanOpNorm M ^ 2)) * frobeniusSq (Matrix.of G * M))
          ∂GaussianNull.gaussianRect m n) := hchernoff
    _ ≤ Real.exp (-(1 / (4 * euclideanOpNorm M ^ 2)) *
          (2 * (m : ℝ) * frobeniusSq M + 4 * x * euclideanOpNorm M ^ 2)) *
        Real.exp ((m : ℝ) * frobeniusSq M / (2 * euclideanOpNorm M ^ 2)) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-x) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring

#assert_trust kernel frobeniusSq
#assert_trust kernel euclideanOpNorm
#assert_trust kernel euclideanOpNorm_eq_l2
#assert_trust kernel weights_bounds
#assert_trust kernel weights_sum
#assert_trust kernel rowEnergy_rotate
#assert_trust kernel rotate_gaussian
#assert_trust kernel row_mgf_bound
#assert_trust kernel matrix_mgf_bound
#assert_trust kernel frobenius_exceedance_measurable
#assert_trust kernel centered_gaussian_frobenius_tail
#print axioms centered_gaussian_frobenius_tail

end NLA.IE06.GaussianFrobenius
