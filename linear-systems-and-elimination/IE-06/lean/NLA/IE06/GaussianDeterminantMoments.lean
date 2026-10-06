/-
Exact negative Gaussian Gram determinant moments, derived from the proved
regression identity and actual Gaussian product law. The independently
approved contract is in reviews/gaussian-determinant-moments-specification.md.
No Bartlett independence or inverse-Wishart law is assumed.
-/
import NLA.IE06.GaussianRegression

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace
namespace NLA.IE06.GaussianDeterminantMoments
open GaussianNull GaussianQuadratic GaussianRegression
local instance gaussianRect_probability (m n : ℕ) : IsProbabilityMeasure (gaussianRect m n) := by
  unfold gaussianRect
  infer_instance

theorem inverse_gram_first_cofactor {s n : ℕ} (B : RectMat s n) (y : Fin n → ℝ) :
    (gram (Fin.cons y B))⁻¹ 0 0 = (gram (Fin.cons y B)).det⁻¹ * (gram B).det := by
  have hs : (gram (Fin.cons y B)).submatrix (Fin.succAbove (0 : Fin (s + 1)))
      (Fin.succAbove (0 : Fin (s + 1))) = gram B := by
    ext i j
    simp [GaussianRegression.gram, Matrix.mul_apply]
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_zero, zero_add, pow_zero, one_mul, hs, Ring.inverse_eq_inv, smul_eq_mul]

theorem inverse_det_cons_factor {s n : ℕ} (B : RectMat s n) (y : Fin n → ℝ)
    (hB : (gram B).det ≠ 0) (hG : (gram (Fin.cons y B)).det ≠ 0) (q : ℕ) :
    ((gram (Fin.cons y B)).det ^ q)⁻¹ =
      ((gram B).det ^ q)⁻¹ * (‖residual B y‖ ^ (2 * q))⁻¹ := by
  have he := inverse_gram_first_diagonal B y hG
  rw [inverse_gram_first_cofactor] at he
  have hi : (gram (Fin.cons y B)).det⁻¹ = (‖residual B y‖ ^ 2)⁻¹ / (gram B).det :=
    (eq_div_iff hB).mpr he
  calc
    _ = ((gram (Fin.cons y B)).det⁻¹) ^ q := (inv_pow _ _).symm
    _ = ((‖residual B y‖ ^ 2)⁻¹ / (gram B).det) ^ q := by rw [hi]
    _ = _ := by rw [div_pow, div_eq_mul_inv, inv_pow, ← pow_mul, mul_comm]

theorem inverse_det_measurable (m n q : ℕ) :
    Measurable (fun G : RectMat m n => ((gram G).det ^ q)⁻¹) := by
  exact (gram_continuous.matrix_det.measurable.pow_const q).inv

/-- Exact product of inverse chi-square moments, proved by repeated
conditioning with verified integrability, including m=0 and q=0. -/
theorem gaussian_inverse_gram_det_moment (m n q : ℕ) (hn : m + 2 * q ≤ n) :
    Integrable (fun G : RectMat m n => ((gram G).det ^ q)⁻¹) (gaussianRect m n) ∧
    (∫ G : RectMat m n, ((gram G).det ^ q)⁻¹ ∂gaussianRect m n) =
      ∏ a ∈ Finset.range m, ∏ b ∈ Finset.range q, (((n - a : ℕ) : ℝ) - 2 * (b + 1))⁻¹ := by
  induction m with
  | zero =>
    simp [Matrix.det_isEmpty]
  | succ s ih =>
    obtain ⟨hBi, hBe⟩ := ih (by omega)
    let C : ℝ := (∏ b ∈ Finset.range q, (((n - s : ℕ) : ℝ) - 2 * (b + 1)))⁻¹
    let f : RectMat (s + 1) n → ℝ := fun G => ((gram G).det ^ q)⁻¹
    let b : RectMat s n → ℝ := fun B => ((gram B).det ^ q)⁻¹
    let c : RectMat s n × (Fin n → ℝ) → RectMat (s + 1) n := fun z => Fin.cons z.2 z.1
    have hmp : MeasurePreserving c ((gaussianRect s n).prod (gaussianVector n))
        (gaussianRect (s + 1) n) :=
      (gaussian_cons_measurePreserving s n).comp (Measure.measurePreserving_swap)
    have hfm : Measurable f := inverse_det_measurable (s + 1) n q
    have hcAE : ∀ᵐ z ∂(gaussianRect s n).prod (gaussianVector n),
        (gram (c z)).det ≠ 0 :=
      hmp.quasiMeasurePreserving.ae (gram_det_ne_zero_ae (s + 1) n (by omega))
    have hcond : ∀ᵐ B ∂gaussianRect s n,
        Integrable (fun y => f (c (B, y))) (gaussianVector n) ∧
        (∫ y, f (c (B, y)) ∂gaussianVector n) = b B * C ∧
        (∫ y, ‖f (c (B, y))‖ ∂gaussianVector n) = b B * C := by
      filter_upwards [gram_posDef_ae s n (by omega), Measure.ae_ae_of_ae_prod hcAE] with B hB hdet
      obtain ⟨hri, hre⟩ := residual_inverse_norm_moment B hB q (by omega)
      have heq : (fun y => f (c (B, y))) =ᵐ[gaussianVector n]
          (fun y => b B * (‖residual B y‖ ^ (2 * q))⁻¹) := by
        filter_upwards [hdet] with y hy
        exact inverse_det_cons_factor B y (ne_of_gt hB.det_pos) hy q
      have hb : 0 ≤ b B := by dsimp [b]; exact inv_nonneg.mpr (pow_nonneg hB.det_pos.le q)
      have hnq : (fun y => ‖f (c (B, y))‖) =ᵐ[gaussianVector n]
          (fun y => b B * (‖residual B y‖ ^ (2 * q))⁻¹) := by
        filter_upwards [heq] with y hy
        rw [hy, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb (by positivity))]
      refine ⟨(hri.const_mul (b B)).congr heq.symm, ?_, ?_⟩
      · rw [integral_congr_ae heq, integral_const_mul, hre]
      · rw [integral_congr_ae hnq, integral_const_mul, hre]
    have hfi : Integrable (f ∘ c) ((gaussianRect s n).prod (gaussianVector n)) := by
      apply (integrable_prod_iff (hfm.comp hmp.measurable).aestronglyMeasurable).mpr
      refine ⟨hcond.mono fun B hB => hB.1, ?_⟩
      exact (hBi.mul_const C).congr (hcond.mono fun B hB => hB.2.2.symm)
    refine ⟨(hmp.integrable_comp hfm.aestronglyMeasurable).mp hfi, ?_⟩
    change (∫ G, f G ∂gaussianRect (s + 1) n) = _
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hfm.aestronglyMeasurable]
    change (∫ z, (f ∘ c) z ∂(gaussianRect s n).prod (gaussianVector n)) = _
    rw [integral_prod _ hfi]
    simp only [Function.comp_apply]
    rw [integral_congr_ae (hcond.mono fun B hB => hB.2.1), integral_mul_const]
    change (∫ B, ((gram B).det ^ q)⁻¹ ∂gaussianRect s n) * C = _
    rw [hBe, Finset.prod_range_succ]
    congr 1
    simp only [C, Finset.prod_inv_distrib]

#assert_trust kernel inverse_gram_first_cofactor
#assert_trust kernel inverse_det_cons_factor
#assert_trust kernel inverse_det_measurable
#assert_trust kernel gaussian_inverse_gram_det_moment
#print axioms gaussian_inverse_gram_det_moment
end NLA.IE06.GaussianDeterminantMoments
