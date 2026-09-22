import NLA.IE22.Definitions

/-! The Gaussian threshold objective has the original trimmed-Gaussian upper mean.
The row coordinates may be correlated; only their individual laws are used.
Original mathematical proof: Matthew J. Colbrook.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with AI-agent assistance. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE22
open NLA.IE21

/-- Nonnegative quadratic hinges are bounded by their threshold. -/
lemma gaussian_inner_hinge_integrable {d : ℕ} (b : Space d) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun g : Space d => max (t - (inner ℝ b g)^2) 0)
      (stdGaussian (Space d)) := by
  apply (integrable_const t).mono' (by fun_prop)
  filter_upwards with g
  rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
  exact max_le (by nlinarith [sq_nonneg (inner ℝ b g)]) ht

/-- Contracting a unit Gaussian coordinate increases its lower-threshold hinge. -/
lemma gaussian_hinge_contraction {d : ℕ} (hd : 1 ≤ d) (b : Space d)
    (hb : ‖b‖ ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    (∫ z : ℝ, max (t-z^2) 0 ∂gaussianReal 0 1) ≤
      ∫ g : Space d, max (t-(inner ℝ b g)^2) 0 ∂stdGaussian (Space d) := by
  obtain ⟨x,hx,hb'⟩ : ∃ x : Space d, ‖x‖ = 1 ∧ b = ‖b‖ • x := by
    by_cases hz : b = 0
    · obtain ⟨x,hx⟩ := unit_sphere_nonempty d hd
      refine ⟨x,by simpa using hx,?_⟩
      simp [hz]
    · exact ⟨‖b‖⁻¹ • b,norm_smul_inv_norm hz,by simp [smul_smul,norm_ne_zero_iff.mpr hz]⟩
  have hpoint (g : Space d) : (inner ℝ b g)^2 ≤ (inner ℝ x g)^2 := by
    conv_lhs => rw [hb',real_inner_smul_left,mul_pow]
    have hsq : ‖b‖^2 ≤ 1 := by nlinarith [norm_nonneg b]
    simpa using mul_le_mul_of_nonneg_right hsq (sq_nonneg (inner ℝ x g))
  have hi := integral_mono (gaussian_inner_hinge_integrable x t ht)
    (gaussian_inner_hinge_integrable b t ht) (fun g => max_le_max_right 0 (by linarith [hpoint g]))
  have heq : (∫ g : Space d, max (t-(inner ℝ x g)^2) 0 ∂stdGaussian (Space d)) =
      ∫ z : ℝ, max (t-z^2) 0 ∂gaussianReal 0 1 := by
    rw [← gaussian_projection_law x hx,integral_map (by fun_prop) (by fun_prop)]
  rwa [heq] at hi

theorem gaussian_objective_mean (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (B : Mat m d)
    (hB : ∀ i, ‖matrixRow B i‖ ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (projectedObjective θ B t) (stdGaussian (Space d)) ∧
    (∫ g, projectedObjective θ B t g ∂stdGaussian (Space d)) ≤ gaussianTrim θ := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hi (i : Fin m) : Integrable (fun g : Space d => max (t-(matrixMap B g i)^2) 0)
      (stdGaussian (Space d)) := by
    simpa only [matrixMap_eq_inner_row] using gaussian_inner_hinge_integrable (matrixRow B i) t ht
  have hsum : Integrable (fun g : Space d => ∑ i, max (t-(matrixMap B g i)^2) 0)
      (stdGaussian (Space d)) := integrable_finsetSum _ (fun i _ => hi i)
  have hobj : Integrable (projectedObjective θ B t) (stdGaussian (Space d)) :=
    (integrable_const ((retainedRows θ m : ℝ)/m*t)).sub (hsum.const_mul (1/(m : ℝ)))
  refine ⟨hobj,?_⟩
  have heq : (∫ g, projectedObjective θ B t g ∂stdGaussian (Space d)) =
      (retainedRows θ m : ℝ)/m*t - (1/(m : ℝ))*
      ∑ i, ∫ g : Space d, max (t-(matrixMap B g i)^2) 0 ∂stdGaussian (Space d) := by
    unfold projectedObjective trimDual
    rw [integral_sub (integrable_const _) (hsum.const_mul _)]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi i)]
  have hbound : (m : ℝ) * (∫ z : ℝ, max (t-z^2) 0 ∂gaussianReal 0 1) ≤
      ∑ i, ∫ g : Space d, max (t-(matrixMap B g i)^2) 0 ∂stdGaussian (Space d) := by
    have hh (i : Fin m) := gaussian_hinge_contraction hd (matrixRow B i) (hB i) t ht
    simp only [← matrixMap_eq_inner_row] at hh
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => hh i)
  have hfrac : (retainedRows θ m : ℝ)/m ≤ θ := by
    apply (div_le_iff₀ hmpos).2
    nlinarith [(retainedRows_bounds θ hθ m).2.1]
  have hupper := trimming_objective_le_populationTrim hθ.2.le gaussian_square_integrable ht
  rw [populationTrim_gaussian θ hθ] at hupper
  rw [heq]
  have hscaled := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 1/(m : ℝ))
  have hc : (1/(m : ℝ))*((m : ℝ)*(∫ z : ℝ, max (t-z^2) 0 ∂gaussianReal 0 1)) =
      ∫ z : ℝ, max (t-z^2) 0 ∂gaussianReal 0 1 := by field_simp
  rw [hc] at hscaled
  have hf := mul_le_mul_of_nonneg_right hfrac ht
  linarith

end NLA.IE22
