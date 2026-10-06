import NLA.IE06.GaussianQuadratic
import NLA.IE06.SubGaussianQuadratic

/-! Exact Gaussian linear forms and finite row tails. Statements were reviewed
before implementation in `reviews/gaussian-linear-specification.md`. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
namespace NLA.IE06.GaussianLinear
open GaussianQuadratic

def dot {d : ℕ} (v z : Fin d → ℝ) : ℝ := ∑ i, v i * z i

def squareNorm {d : ℕ} (v : Fin d → ℝ) : ℝ := ∑ i, v i ^ 2

theorem squareNorm_nonneg {d : ℕ} (v : Fin d → ℝ) : 0 ≤ squareNorm v :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem linear_mgf {d : ℕ} (v : Fin d → ℝ) (t : ℝ) :
    Integrable (fun z => Real.exp (t * dot v z)) (gaussianVector d) ∧
    (∫ z, Real.exp (t * dot v z) ∂gaussianVector d) =
      Real.exp (t^2 * squareNorm v / 2) := by
  have he (z : Fin d → ℝ) : Real.exp (t * dot v z) =
      ∏ i, Real.exp ((t*v i)*z i) := by
    simp only [dot, Finset.mul_sum, Real.exp_sum, mul_assoc]
  simp_rw [he]
  constructor
  · exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (t*v i))
  · rw [gaussianVector, integral_fintype_prod_eq_prod
      (fun i z => Real.exp ((t*v i)*z))]
    have hm (i : Fin d) : (∫ z : ℝ, Real.exp ((t*v i)*z) ∂gaussianReal 0 1) =
        Real.exp ((t*v i)^2/2) := by
      simpa only [mgf, zero_mul, zero_add, NNReal.coe_one, one_mul] using
        congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) (t*v i)
    simp_rw [hm]
    rw [← Real.exp_sum]
    congr 1
    simp only [squareNorm, Finset.mul_sum, Finset.sum_div, mul_pow]

theorem linear_subGaussian {d : ℕ} (v : Fin d → ℝ) :
    HasSubgaussianMGF (dot v) ⟨squareNorm v, squareNorm_nonneg v⟩ (gaussianVector d) := by
  refine ⟨fun t => (linear_mgf v t).1, fun t => ?_⟩
  change (∫ z, Real.exp (t * dot v z) ∂gaussianVector d) ≤ _
  rw [(linear_mgf v t).2]
  simp only [mul_comm (t^2)]
  exact le_rfl

theorem gaussianVector_directional_subGaussian (d : ℕ) :
    SubGaussianQuadratic.DirectionalSubGaussian (gaussianVector d) id :=
  fun v => linear_subGaussian v

theorem dot_zero_of_squareNorm_zero {d : ℕ} (v : Fin d → ℝ)
    (hv : squareNorm v = 0) (z : Fin d → ℝ) : dot v z = 0 := by
  have hz (i : Fin d) : v i = 0 := by
    have hi : v i ^ 2 ≤ squareNorm v :=
      Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    rw [hv] at hi
    nlinarith [sq_nonneg (v i)]
  simp [dot, hz]

private theorem linear_upper_tail {d : ℕ} (v : Fin d → ℝ) (x : ℝ)
    (hx : 0 < x) (hv : 0 < squareNorm v) :
    gaussianVector d {z | Real.sqrt (2*x*squareNorm v) ≤ dot v z} ≤
      ENNReal.ofReal (Real.exp (-x)) := by
  have h := (linear_subGaussian v).measure_ge_le (Real.sqrt_nonneg (2*x*squareNorm v))
  have hs : -(Real.sqrt (2*x*squareNorm v))^2 / (2*squareNorm v) = -x := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  change (gaussianVector d).real _ ≤ Real.exp (-(Real.sqrt (2*x*squareNorm v))^2 / (2*squareNorm v)) at h
  rw [hs] at h
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr h

theorem linear_two_sided_tail {d : ℕ} (v : Fin d → ℝ) (x : ℝ) (hx : 0 < x) :
    gaussianVector d {z | Real.sqrt (2*x*squareNorm v) < |dot v z|} ≤
      2 * ENNReal.ofReal (Real.exp (-x)) := by
  by_cases hz : squareNorm v = 0
  · simp [hz, dot_zero_of_squareNorm_zero v hz, Set.ofPred_false]
  have hv := lt_of_le_of_ne (squareNorm_nonneg v) (Ne.symm hz)
  have hnv : squareNorm (-v) = squareNorm v := by simp [squareNorm]
  have hnd (z : Fin d → ℝ) : dot (-v) z = -dot v z := by simp [dot, Finset.sum_neg_distrib]
  calc
    gaussianVector d {z | Real.sqrt (2*x*squareNorm v) < |dot v z|} ≤
        gaussianVector d ({z | Real.sqrt (2*x*squareNorm v) ≤ dot v z} ∪
          {z | Real.sqrt (2*x*squareNorm v) ≤ dot (-v) z}) := by
      apply measure_mono
      intro z hz
      change Real.sqrt (2*x*squareNorm v) < |dot v z| at hz
      rcases (lt_abs.mp hz) with h | h
      · exact Or.inl h.le
      · exact Or.inr (by
          change Real.sqrt (2*x*squareNorm v) ≤ dot (-v) z
          rw [hnd]
          exact h.le)
    _ ≤ gaussianVector d {z | Real.sqrt (2*x*squareNorm v) ≤ dot v z} +
        gaussianVector d {z | Real.sqrt (2*x*squareNorm v) ≤ dot (-v) z} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-x)) + ENNReal.ofReal (Real.exp (-x)) :=
      add_le_add (linear_upper_tail v x hx hv)
        (by simpa only [hnv] using linear_upper_tail (-v) x hx (hnv.symm ▸ hv))
    _ = 2 * ENNReal.ofReal (Real.exp (-x)) := by rw [two_mul]

theorem rows_tail {m d : ℕ} (w : Fin m → Fin d → ℝ) (L x : ℝ)
    (_hL : 0 ≤ L) (hw : ∀ i, squareNorm (w i) ≤ L) (hx : 0 < x) :
    gaussianVector d {z | ∃ i, Real.sqrt (2*x*L) < |dot (w i) z|} ≤
      (2 * (m : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-x)) := by
  have hs : {z | ∃ i, Real.sqrt (2*x*L) < |dot (w i) z|} =
      ⋃ i : Fin m, {z | Real.sqrt (2*x*L) < |dot (w i) z|} := by ext z; simp
  rw [hs]
  calc
    _ ≤ ∑ i : Fin m, gaussianVector d {z | Real.sqrt (2*x*L) < |dot (w i) z|} :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ : Fin m, 2 * ENNReal.ofReal (Real.exp (-x)) := by
      apply Finset.sum_le_sum
      intro i _
      apply le_trans (measure_mono ?_) (linear_two_sided_tail (w i) x hx)
      intro z hz
      exact lt_of_le_of_lt (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hw i) (by positivity))) hz
    _ = (2 * (m : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-x)) := by
      simp [mul_assoc, mul_comm]

#assert_trust kernel linear_mgf
#assert_trust kernel linear_subGaussian
#assert_trust kernel gaussianVector_directional_subGaussian
#assert_trust kernel linear_two_sided_tail
#assert_trust kernel rows_tail
#print axioms linear_mgf
#print axioms gaussianVector_directional_subGaussian
#print axioms linear_two_sided_tail
#print axioms rows_tail
end NLA.IE06.GaussianLinear
