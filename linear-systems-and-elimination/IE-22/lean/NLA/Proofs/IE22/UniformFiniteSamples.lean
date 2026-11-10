import NLA.Proofs.IE22.FiniteSamples
import NLA.Proofs.IE22.GaussianBasics

/-! Actual simultaneous finite samples for a uniformly Lipschitz bounded family
indexed by the genuine Euclidean unit sphere. The finite centers lie on that
sphere; an empty sphere or empty family needs no separate sampling oracle. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
namespace NLA.Proofs.IE22

/-- Uniform approximation on the compact unit sphere by one actual finite sample. -/
theorem exists_uniform_sphere_sample {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Euclid n → Ω → ℝ) (T : ℝ) (hT : 0 ≤ T) (L : ℝ≥0)
    (hF : ∀ x ∈ Metric.sphere (0 : Euclid n) 1, AEStronglyMeasurable (F x) μ)
    (hbound : ∀ x ∈ Metric.sphere (0 : Euclid n) 1, ∀ z, 0 ≤ F x z ∧ F x z ≤ T)
    (hLip : ∀ z, LipschitzOnWith L (fun x => F x z) (Metric.sphere (0 : Euclid n) 1))
    (ε : ℝ) (hε : 0 < ε) (M0 : ℕ) :
    ∃ m : ℕ, 0 < m ∧ M0 ≤ m ∧ ∃ ω : Fin m → Ω,
      ∀ x ∈ Metric.sphere (0 : Euclid n) 1,
        |(1 / (m : ℝ)) * (∑ i, F x (ω i)) - ∫ z, F x z ∂μ| < ε := by
  classical
  let S : Set (Euclid n) := Metric.sphere (0 : Euclid n) 1
  let η : ℝ := ε / (8 * ((L : ℝ) + 1))
  have hL : 0 ≤ (L : ℝ) := L.coe_nonneg
  have hden : 0 < 8 * ((L : ℝ) + 1) := by positivity
  have hη : 0 < η := div_pos hε hden
  obtain ⟨t, htS, htfin, htcover⟩ := (isCompact_sphere (0 : Euclid n) 1).finite_cover_balls hη
  let : Fintype t := htfin.fintype
  obtain ⟨m, hm0, hmM, ω, hω⟩ := exists_finite_sample μ
    (fun j : t => F j.1) T hT (fun j => hF j.1 (htS j.2))
    (fun j => hbound j.1 (htS j.2)) (ε / 2) (by positivity) M0
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  let avg : Euclid n → ℝ := fun x => (1 / (m : ℝ)) * ∑ i, F x (ω i)
  let mean : Euclid n → ℝ := fun x => ∫ z, F x z ∂μ
  have hint {x : Euclid n} (hx : x ∈ S) : Integrable (F x) μ :=
    (memLp_of_bounded (Filter.Eventually.of_forall (hbound x hx)) (hF x hx) 2).integrable
      (by norm_num)
  have hpoint {x y : Euclid n} (hx : x ∈ S) (hy : y ∈ S) (z : Ω) :
      |F x z - F y z| ≤ (L : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using (hLip z).dist_le_mul x hx y hy
  have hmean {x y : Euclid n} (hx : x ∈ S) (hy : y ∈ S) :
      |mean x - mean y| ≤ (L : ℝ) * dist x y := by
    dsimp [mean]
    rw [← integral_sub (hint hx) (hint hy)]
    have h := norm_integral_le_of_norm_le_const
      (μ := μ) (f := fun z => F x z - F y z)
      (Filter.Eventually.of_forall (fun z => by
        simpa only [Real.norm_eq_abs] using hpoint hx hy z))
    simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using h
  have havg {x y : Euclid n} (hx : x ∈ S) (hy : y ∈ S) :
      |avg x - avg y| ≤ (L : ℝ) * dist x y := by
    dsimp [avg]
    calc
      |1 / (m : ℝ) * ∑ i, F x (ω i) - 1 / (m : ℝ) * ∑ i, F y (ω i)| =
          (1 / (m : ℝ)) * |∑ i, (F x (ω i) - F y (ω i))| := by
        rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
          abs_of_nonneg (div_nonneg zero_le_one hmR.le)]
      _ ≤ (1 / (m : ℝ)) * ∑ i, |F x (ω i) - F y (ω i)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ (1 / (m : ℝ)) * ∑ _i : Fin m, (L : ℝ) * dist x y :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hpoint hx hy (ω i)))
          (by positivity)
      _ = (L : ℝ) * dist x y := by simp [hmne]
  have hηbound : 2 * (L : ℝ) * η < ε / 2 := by
    dsimp [η]
    rw [show 2 * (L : ℝ) * (ε / (8 * ((L : ℝ) + 1))) =
      (2 * (L : ℝ) * ε) / (8 * ((L : ℝ) + 1)) by ring]
    apply (div_lt_iff₀ hden).2
    nlinarith [mul_nonneg hL hε.le]
  refine ⟨m, hm0, hmM, ω, ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := mem_iUnion.mp (htcover hx)
  obtain ⟨hyt, hxy⟩ := mem_iUnion.mp hy
  have hyS : y ∈ S := htS hyt
  have hdist : dist x y ≤ η := (Metric.mem_ball.mp hxy).le
  have havgxy : |avg x - avg y| ≤ (L : ℝ) * η :=
    (havg hx hyS).trans (mul_le_mul_of_nonneg_left hdist hL)
  have hmeanxy : |mean y - mean x| ≤ (L : ℝ) * η := by
    have h := (hmean hyS hx).trans (mul_le_mul_of_nonneg_left
      (by simpa only [dist_comm] using hdist) hL)
    exact h
  have hnet : |avg y - mean y| < ε / 2 := hω ⟨y, hyt⟩
  change |avg x - mean x| < ε
  have htriangle : |avg x - mean x| ≤
      |avg x - avg y| + |avg y - mean y| + |mean y - mean x| := by
    calc
      _ ≤ |avg x - avg y| + |avg y - mean x| := abs_sub_le _ _ _
      _ ≤ |avg x - avg y| + (|avg y - mean y| + |mean y - mean x|) :=
        add_le_add le_rfl (abs_sub_le _ _ _)
      _ = _ := by ring
  linarith

#assert_trust kernel exists_uniform_sphere_sample
#print axioms exists_uniform_sphere_sample
end NLA.Proofs.IE22
