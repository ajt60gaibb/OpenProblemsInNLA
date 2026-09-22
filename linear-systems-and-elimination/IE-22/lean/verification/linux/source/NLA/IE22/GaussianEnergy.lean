import NLA.IE22.Definitions

/-! Exact Gaussian quadratic energy moments, including singular and zero matrices.
Original mathematical proof: Matthew J. Colbrook.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with AI-agent assistance. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE22
open NLA.IE21

lemma gaussian_inner_pow_integrable {d : ℕ} (b : Space d) (r : ℕ) :
    Integrable (fun g : Space d => (inner ℝ b g)^r) (stdGaussian (Space d)) := by
  apply ((gaussian_norm_pow_integrable d r).const_mul (‖b‖^r)).mono' (by fun_prop)
  filter_upwards with g
  rw [Real.norm_eq_abs,abs_pow]
  calc
    |inner ℝ b g|^r ≤ (‖b‖*‖g‖)^r := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm b g) r
    _ = ‖b‖^r*‖g‖^r := mul_pow _ _ _

lemma gaussian_inner_even_moment_general {d : ℕ} (b : Space d) (r : ℕ) :
    (∫ g : Space d, (inner ℝ b g)^(2*r) ∂stdGaussian (Space d)) =
      ‖b‖^(2*r) * ∏ j ∈ Finset.range r, (2*(j:ℝ)+1) := by
  by_cases hz : b = 0
  · subst b
    cases r <;> simp
  · let x : Space d := ‖b‖⁻¹ • b
    have hx : ‖x‖ = 1 := norm_smul_inv_norm hz
    have hb : b = ‖b‖ • x := by simp [x,smul_smul,norm_ne_zero_iff.mpr hz]
    have he (g : Space d) : (inner ℝ b g)^(2*r) =
        ‖b‖^(2*r)*(inner ℝ x g)^(2*r) := by
      conv_lhs => rw [hb,real_inner_smul_left,mul_pow]
    simp_rw [he]
    rw [integral_const_mul]
    congr 1
    simpa only [real_inner_comm] using gaussian_inner_even_moment x hx r

lemma gaussian_inner_sq_mean {d : ℕ} (b : Space d) :
    (∫ g : Space d, (inner ℝ b g)^2 ∂stdGaussian (Space d)) = ‖b‖^2 := by
  simpa using gaussian_inner_even_moment_general b 1

lemma gaussian_inner_fourth_mean {d : ℕ} (b : Space d) :
    (∫ g : Space d, (inner ℝ b g)^4 ∂stdGaussian (Space d)) = 3*‖b‖^4 := by
  have h := gaussian_inner_even_moment_general b 2
  norm_num [Finset.prod_range_succ] at h
  nlinarith [h]

lemma gaussian_inner_sq_mul_sq_integrable {d : ℕ} (b c : Space d) :
    Integrable (fun g : Space d => (inner ℝ b g)^2*(inner ℝ c g)^2)
      (stdGaussian (Space d)) := by
  apply ((gaussian_inner_pow_integrable b 4).add (gaussian_inner_pow_integrable c 4)).mono'
    (by fun_prop)
  filter_upwards with g
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  change (inner ℝ b g)^2*(inner ℝ c g)^2 ≤ (inner ℝ b g)^4+(inner ℝ c g)^4
  nlinarith [sq_nonneg ((inner ℝ b g)^2-(inner ℝ c g)^2)]

lemma gaussian_inner_cross_fourth {d : ℕ} (b c : Space d) :
    (∫ g : Space d, (inner ℝ b g)^2*(inner ℝ c g)^2 ∂stdGaussian (Space d)) =
      ‖b‖^2*‖c‖^2 + 2*(inner ℝ b c)^2 := by
  have hp (g : Space d) : 12*((inner ℝ b g)^2*(inner ℝ c g)^2) =
      (inner ℝ (b+c) g)^4+(inner ℝ (b-c) g)^4-
        2*(inner ℝ b g)^4-2*(inner ℝ c g)^4 := by
    simp only [inner_add_left,inner_sub_left]
    ring
  have he := congrArg (fun f : Space d → ℝ => ∫ g, f g ∂stdGaussian (Space d)) (funext hp)
  simp only [integral_const_mul] at he
  rw [integral_sub (f := fun g : Space d => (inner ℝ (b+c) g)^4+(inner ℝ (b-c) g)^4-2*(inner ℝ b g)^4) (g := fun g : Space d => 2*(inner ℝ c g)^4) (((gaussian_inner_pow_integrable (b+c) 4).add
      (gaussian_inner_pow_integrable (b-c) 4)).sub
      ((gaussian_inner_pow_integrable b 4).const_mul 2))
      ((gaussian_inner_pow_integrable c 4).const_mul 2),
    integral_sub (f := fun g : Space d => (inner ℝ (b+c) g)^4+(inner ℝ (b-c) g)^4) (g := fun g : Space d => 2*(inner ℝ b g)^4) ((gaussian_inner_pow_integrable (b+c) 4).add
      (gaussian_inner_pow_integrable (b-c) 4))
      ((gaussian_inner_pow_integrable b 4).const_mul 2),
    integral_add (f := fun g : Space d => (inner ℝ (b+c) g)^4) (g := fun g : Space d => (inner ℝ (b-c) g)^4) (gaussian_inner_pow_integrable (b+c) 4)
      (gaussian_inner_pow_integrable (b-c) 4)] at he
  simp only [integral_const_mul,gaussian_inner_fourth_mean] at he
  have hadd : ‖b+c‖^2 = ‖b‖^2+‖c‖^2+2*inner ℝ b c := by
    rw [norm_add_sq_real]
    ring
  have hsub : ‖b-c‖^2 = ‖b‖^2+‖c‖^2-2*inner ℝ b c := by
    rw [norm_sub_sq_real]
    ring
  have h4 (a : ℝ) : a^4 = (a^2)^2 := by ring
  simp only [h4,hadd,hsub] at he
  nlinarith [he]

lemma gram_trace_eq_row_sum {m d : ℕ} (B : Mat m d) :
    Matrix.trace (gramMatrix B) = ∑ i, ‖matrixRow B i‖^2 := by
  rw [gramMatrix,Matrix.trace_mul_comm]
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  simp [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply,matrixRow,sq]

lemma row_gram_eq_inner {m d : ℕ} (B : Mat m d) (i j : Fin m) :
    (B*B.transpose) i j = inner ℝ (matrixRow B i) (matrixRow B j) := by
  simp [Matrix.mul_apply,Matrix.transpose_apply,PiLp.inner_apply,matrixRow,mul_comm]

lemma gram_sq_trace_eq_row_inner_sum {m d : ℕ} (B : Mat m d) :
    Matrix.trace (gramMatrix B*gramMatrix B) =
      ∑ i, ∑ j, (inner ℝ (matrixRow B i) (matrixRow B j))^2 := by
  have he : Matrix.trace (gramMatrix B*gramMatrix B) =
      Matrix.trace ((B*B.transpose)*(B*B.transpose)) := by
    rw [gramMatrix,← Matrix.mul_assoc,
      Matrix.trace_mul_comm (B.transpose*B*B.transpose) B]
    simp only [Matrix.mul_assoc]
  rw [he]
  change (∑ i, ∑ j, (B*B.transpose) i j * (B*B.transpose) j i) = _
  simp_rw [row_gram_eq_inner]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (matrixRow B j),sq]

lemma projectedEnergy_eq_row_sum {m d : ℕ} (B : Mat m d) (g : Space d) :
    projectedEnergy B g = (∑ i, (inner ℝ (matrixRow B i) g)^2)/(m:ℝ) := by
  simp only [projectedEnergy,EuclideanSpace.real_norm_sq_eq,matrixMap_eq_inner_row]

lemma gaussian_projectedEnergy_memLp {m d : ℕ} (B : Mat m d) :
    MemLp (projectedEnergy B) 2 (stdGaussian (Space d)) := by
  have hi (i : Fin m) : MemLp (fun g : Space d => (inner ℝ (matrixRow B i) g)^2)
      2 (stdGaussian (Space d)) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    convert gaussian_inner_pow_integrable (matrixRow B i) 4 using 1
    ext g
    ring
  have hs := memLp_finsetSum (s := (Finset.univ : Finset (Fin m))) (fun i _ => hi i)
  convert hs.mul_const ((m:ℝ)⁻¹) using 1
  ext g
  exact (projectedEnergy_eq_row_sum B g).trans (div_eq_mul_inv _ _)

lemma gaussian_projectedEnergy_mean {m d : ℕ} (B : Mat m d) :
    (∫ g, projectedEnergy B g ∂stdGaussian (Space d)) = Matrix.trace (gramMatrix B)/m := by
  simp_rw [projectedEnergy_eq_row_sum]
  rw [integral_div,integral_finsetSum _ (fun i _ => gaussian_inner_pow_integrable (matrixRow B i) 2)]
  simp only [gaussian_inner_sq_mean,gram_trace_eq_row_sum]

lemma gaussian_projectedEnergy_second_moment {m d : ℕ} (B : Mat m d) :
    (∫ g, (projectedEnergy B g)^2 ∂stdGaussian (Space d)) =
      ((Matrix.trace (gramMatrix B))^2+2*Matrix.trace (gramMatrix B*gramMatrix B))/(m:ℝ)^2 := by
  have hp (g : Space d) : (projectedEnergy B g)^2 =
      (∑ i, ∑ j, ((inner ℝ (matrixRow B i) g)^2*(inner ℝ (matrixRow B j) g)^2))/(m:ℝ)^2 := by
    rw [projectedEnergy_eq_row_sum,div_pow,pow_two,Finset.sum_mul]
    simp only [Finset.mul_sum]
  simp_rw [hp]
  rw [integral_div,integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => gaussian_inner_sq_mul_sq_integrable (matrixRow B i) (matrixRow B j)))]
  simp_rw [integral_finsetSum _ (fun j _ =>
    gaussian_inner_sq_mul_sq_integrable _ (matrixRow B j)),gaussian_inner_cross_fourth]
  rw [gram_trace_eq_row_sum,gram_sq_trace_eq_row_inner_sum]
  congr 1
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,pow_two]

theorem gaussian_energy_moments (m d : ℕ) (_hm : 1 ≤ m) (_hd : 1 ≤ d) (B : Mat m d) :
    MemLp (projectedEnergy B) 2 (stdGaussian (Space d)) ∧
    (∫ g, projectedEnergy B g ∂stdGaussian (Space d)) = Matrix.trace (gramMatrix B)/m ∧
    Var[projectedEnergy B; stdGaussian (Space d)] =
      2*Matrix.trace (gramMatrix B*gramMatrix B)/(m:ℝ)^2 := by
  refine ⟨gaussian_projectedEnergy_memLp B,gaussian_projectedEnergy_mean B,?_⟩
  rw [variance_eq_sub (gaussian_projectedEnergy_memLp B)]
  change (∫ g, (projectedEnergy B g)^2 ∂stdGaussian (Space d)) -
    (∫ g, projectedEnergy B g ∂stdGaussian (Space d))^2 = _
  rw [gaussian_projectedEnergy_second_moment,gaussian_projectedEnergy_mean]
  rw [div_pow,add_div]
  ring

lemma gram_trace_nonneg {m d : ℕ} (B : Mat m d) : 0 ≤ Matrix.trace (gramMatrix B) := by
  rw [gram_trace_eq_row_sum]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

lemma gram_trace_le_rows {m d : ℕ} (B : Mat m d)
    (hrows : ∀ i, ‖matrixRow B i‖ ≤ 1) : Matrix.trace (gramMatrix B) ≤ m := by
  rw [gram_trace_eq_row_sum]
  calc
    _ ≤ ∑ _ : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [norm_nonneg (matrixRow B i),hrows i]
    _ = _ := by simp

lemma gaussian_projectedEnergy_mean_le_one {m d : ℕ} (hm : 1 ≤ m) (B : Mat m d)
    (hrows : ∀ i, ‖matrixRow B i‖ ≤ 1) :
    (∫ g, projectedEnergy B g ∂stdGaussian (Space d)) ≤ 1 := by
  rw [gaussian_projectedEnergy_mean]
  apply (div_le_iff₀ (by exact_mod_cast (show 0 < m by omega) : (0:ℝ)<m)).2
  simpa using gram_trace_le_rows B hrows

end NLA.IE22
