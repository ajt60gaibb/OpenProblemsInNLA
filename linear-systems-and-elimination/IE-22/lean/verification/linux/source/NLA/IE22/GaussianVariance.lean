import NLA.IE22.GaussianPoincareHinge
import NLA.IE22.VarianceTensorization
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Exact Gaussian variance of IE-22's correlated-row trimming objective.
Original proof: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace
namespace NLA.IE22
open NLA.IE21

/-- Actual row values retained by the derivative's active-set indicator. -/
def activeRowVector {m d : ℕ} (B : Mat m d) (t : ℝ) (g : Space d) : Space m :=
  WithLp.toLp 2 (fun i => if (matrixMap B g i) ^ 2 < t then matrixMap B g i else 0)

/-- An explicit measurable representative of every coordinate derivative. -/
def objectivePartial {m d : ℕ} (B : Mat m d) (t : ℝ) (j : Fin d) (g : Space d) : ℝ :=
  (2 / (m : ℝ)) * ∑ i, B i j * activeRowVector B t g i

theorem matrix_adjoint_coordinate {m d : ℕ} (B : Mat m d) (u : Space m) (j : Fin d) :
    ContinuousLinearMap.adjoint (matrixMap B) u j = ∑ i, B i j * u i := by
  calc
    _ = inner ℝ (EuclideanSpace.single j 1) (ContinuousLinearMap.adjoint (matrixMap B) u) := by
      simp [EuclideanSpace.inner_single_left]
    _ = inner ℝ (matrixMap B (EuclideanSpace.single j 1)) u :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = _ := by
      simp [PiLp.inner_apply, matrixMap_apply, RCLike.inner_apply, mul_comm]

theorem activeRowVector_norm_sq_le {m d : ℕ} (B : Mat m d) (t : ℝ) (ht : 0 ≤ t)
    (g : Space d) : ‖activeRowVector B t g‖ ^ 2 ≤ (m : ℝ) * t := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _ : Fin m, t := by
      apply Finset.sum_le_sum
      intro i _
      change (if (matrixMap B g i) ^ 2 < t then matrixMap B g i else 0) ^ 2 ≤ t
      split_ifs with h
      · exact h.le
      · simpa using ht
    _ = _ := by simp

/-- The exact adjoint estimate controls the sum of derivative squares without
any rowwise independence or Frobenius-norm substitution. -/
theorem objectivePartial_square_sum_le {m d : ℕ} (hm : 1 ≤ m) (B : Mat m d)
    (t : ℝ) (ht : 0 ≤ t) (g : Space d) :
    (∑ j, objectivePartial B t j g ^ 2) ≤ 4 * t * operatorNorm B ^ 2 / m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hnorm : ‖ContinuousLinearMap.adjoint (matrixMap B) (activeRowVector B t g)‖ ≤
      operatorNorm B * ‖activeRowVector B t g‖ := by
    simpa only [operatorNorm, LinearIsometryEquiv.norm_map] using
      (ContinuousLinearMap.adjoint (matrixMap B)).le_opNorm (activeRowVector B t g)
  have hsquare : ‖ContinuousLinearMap.adjoint (matrixMap B) (activeRowVector B t g)‖ ^ 2 ≤
      operatorNorm B ^ 2 * ‖activeRowVector B t g‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hrows := activeRowVector_norm_sq_le B t ht g
  calc
    _ = (2 / (m : ℝ)) ^ 2 *
        ‖ContinuousLinearMap.adjoint (matrixMap B) (activeRowVector B t g)‖ ^ 2 := by
      simp only [objectivePartial, mul_pow, ← Finset.mul_sum,
        EuclideanSpace.real_norm_sq_eq, matrix_adjoint_coordinate]
    _ ≤ (2 / (m : ℝ)) ^ 2 * (operatorNorm B ^ 2 * ‖activeRowVector B t g‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsquare (sq_nonneg _)
    _ ≤ (2 / (m : ℝ)) ^ 2 * (operatorNorm B ^ 2 * ((m : ℝ) * t)) := by
      gcongr
    _ = _ := by field_simp; ring

@[fun_prop]
theorem projectedObjective_continuous {m d : ℕ} (θ : ℝ) (B : Mat m d) (t : ℝ) :
    Continuous (projectedObjective θ B t) := by
  unfold projectedObjective trimDual
  fun_prop

theorem projectedObjective_norm_le {m d : ℕ} (θ : ℝ) (B : Mat m d)
    (t : ℝ) (ht : 0 ≤ t) (g : Space d) :
    ‖projectedObjective θ B t g‖ ≤
      |(retainedRows θ m : ℝ) / m * t| + |1 / (m : ℝ)| * ((m : ℝ) * t) := by
  have heq : projectedObjective θ B t g =
      affineHingeSum ((retainedRows θ m : ℝ) / m * t) (1 / (m : ℝ)) t
        (fun _ : Fin m => 0) (fun i => matrixMap B g i) 0 := by
    simp [projectedObjective, trimDual, affineHingeSum, affineHinge]
  rw [heq]
  exact affineHingeSum_norm_le _ _ t ht _ _ 0

theorem projectedObjective_memLp {m d : ℕ} (θ : ℝ) (B : Mat m d)
    (t : ℝ) (ht : 0 ≤ t) (μ : Measure (Space d)) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (projectedObjective θ B t) p μ :=
  MemLp.of_bound (projectedObjective_continuous θ B t).aestronglyMeasurable _
    (ae_of_all _ (projectedObjective_norm_le θ B t ht))

@[fun_prop]
theorem activeRowVector_measurable {m d : ℕ} (B : Mat m d) (t : ℝ) :
    Measurable (activeRowVector B t) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).measurable.comp
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

@[fun_prop]
theorem objectivePartial_measurable {m d : ℕ} (B : Mat m d) (t : ℝ) (j : Fin d) :
    Measurable (objectivePartial B t j) := by
  unfold objectivePartial
  have hrow (i : Fin m) : Measurable (fun g : Space d => activeRowVector B t g i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).measurable.comp
      (activeRowVector_measurable B t)
  exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => measurable_const.mul (hrow i)))

theorem activeRowVector_abs_le {m d : ℕ} (B : Mat m d) (t : ℝ) (g : Space d) (i : Fin m) :
    |activeRowVector B t g i| ≤ Real.sqrt t := by
  change |if (matrixMap B g i) ^ 2 < t then matrixMap B g i else 0| ≤ Real.sqrt t
  split_ifs with h
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h.le
  · simp

theorem objectivePartial_norm_le {m d : ℕ} (B : Mat m d) (t : ℝ) (j : Fin d)
    (g : Space d) :
    ‖objectivePartial B t j g‖ ≤ |2 / (m : ℝ)| * ∑ i, |B i j| * Real.sqrt t := by
  rw [objectivePartial, norm_mul, Real.norm_eq_abs]
  calc
    _ ≤ |2 / (m : ℝ)| * ∑ i, ‖B i j * activeRowVector B t g i‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ _ := by
      gcongr with i
      simp only [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (activeRowVector_abs_le B t g i) (abs_nonneg _)

/-- Fixed values of all coordinates other than the differentiated coordinate. -/
def rowOffset {m d : ℕ} (B : Mat m d) (x : Fin d → ℝ) (j : Fin d) (i : Fin m) : ℝ :=
  ∑ k ∈ Finset.univ \ {j}, B i k * x k

theorem matrixMap_update {m d : ℕ} (B : Mat m d) (x : Fin d → ℝ)
    (j : Fin d) (s : ℝ) (i : Fin m) :
    matrixMap B (WithLp.toLp 2 (Function.update x j s)) i =
      B i j * s + rowOffset B x j i := by
  change (∑ k, B i k * Function.update x j s k) = _
  simp_rw [Function.apply_update (fun k u => B i k * u)]
  exact Finset.sum_update_of_mem (Finset.mem_univ j) (fun k => B i k * x k) (B i j * s)

theorem objective_fiber_eq_hingeSum {m d : ℕ} (θ : ℝ) (B : Mat m d) (t : ℝ)
    (x : Fin d → ℝ) (j : Fin d) :
    (fun s => projectedObjective θ B t (WithLp.toLp 2 (Function.update x j s))) =
      affineHingeSum ((retainedRows θ m : ℝ) / m * t) (1 / (m : ℝ)) t
        (fun i => B i j) (rowOffset B x j) := by
  funext s
  simp only [projectedObjective, trimDual, affineHingeSum, affineHinge, matrixMap_update]

theorem objective_partial_fiber_eq {m d : ℕ} (B : Mat m d) (t : ℝ)
    (x : Fin d → ℝ) (j : Fin d) (s : ℝ) :
    objectivePartial B t j (WithLp.toLp 2 (Function.update x j s)) =
      affineHingeSumDerivative (1 / (m : ℝ)) t (fun i => B i j) (rowOffset B x j) s := by
  simp only [objectivePartial, activeRowVector, PiLp.toLp_apply,
    matrixMap_update, affineHingeSumDerivative, affineHingeDerivative,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

theorem objective_fiber_variance_le {m d : ℕ} (θ : ℝ) (B : Mat m d) (t : ℝ)
    (ht : 0 ≤ t) (x : Fin d → ℝ) (j : Fin d) :
    Var[fun s => projectedObjective θ B t (WithLp.toLp 2 (Function.update x j s)); gaussianReal 0 1] ≤
      ∫ s, objectivePartial B t j (WithLp.toLp 2 (Function.update x j s)) ^ 2 ∂gaussianReal 0 1 := by
  simp_rw [objective_fiber_eq_hingeSum, objective_partial_fiber_eq]
  exact affineHingeSum_gaussian_variance _ _ t ht _ _

theorem objectivePartial_square_norm_le {m d : ℕ} (B : Mat m d) (t : ℝ) (j : Fin d)
    (g : Space d) :
    ‖objectivePartial B t j g ^ 2‖ ≤
      (|2 / (m : ℝ)| * ∑ i, |B i j| * Real.sqrt t) ^ 2 := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (objectivePartial_norm_le B t j g) 2

/-- The frozen exact variance target, for the actual standard Gaussian and
arbitrarily correlated projected rows. -/
theorem gaussian_objective_variance (θ : ℝ) (m d : ℕ)
    (hm : 1 ≤ m) (_hd : 1 ≤ d) (B : Mat m d) (t : ℝ) (ht : 0 ≤ t) :
    MemLp (projectedObjective θ B t) 2 (stdGaussian (Space d)) ∧
    Var[projectedObjective θ B t; stdGaussian (Space d)] ≤
      4 * t * operatorNorm B ^ 2 / m := by
  refine ⟨projectedObjective_memLp θ B t ht _ 2, ?_⟩
  let μ := gaussianReal 0 1
  let π := Measure.pi (fun _ : Fin d => μ)
  let f : (Fin d → ℝ) → ℝ := fun x => projectedObjective θ B t (WithLp.toLp 2 x)
  let H : Fin d → (Fin d → ℝ) → ℝ := fun j x => objectivePartial B t j (WithLp.toLp 2 x) ^ 2
  have htoLp : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → Space d) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable
  have hf : Measurable f := (projectedObjective_continuous θ B t).measurable.comp htoLp
  have hfb : ∃ C : ℝ, ∀ x, |f x| ≤ C := by
    refine ⟨|(retainedRows θ m : ℝ) / m * t| + |1 / (m : ℝ)| * ((m : ℝ) * t), ?_⟩
    intro x
    exact projectedObjective_norm_le θ B t ht (WithLp.toLp 2 x)
  have hH (j : Fin d) : Measurable (H j) :=
    ((objectivePartial_measurable B t j).comp htoLp).pow_const 2
  have hHb (j : Fin d) : ∀ x, ‖H j x‖ ≤
      (|2 / (m : ℝ)| * ∑ i, |B i j| * Real.sqrt t) ^ 2 :=
    fun x => objectivePartial_square_norm_le B t j (WithLp.toLp 2 x)
  have hHi (j : Fin d) : Integrable (H j) π :=
    (MemLp.of_bound (p := 2) (hH j).aestronglyMeasurable _ (ae_of_all _ (hHb j))).integrable
      (by norm_num)
  have hcoordinate (j : Fin d) :
      (∫ x, Var[fun s => f (Function.update x j s); μ] ∂π) ≤ ∫ x, H j x ∂π := by
    have hpair : Measurable (fun p : (Fin d → ℝ) × ℝ => H j (Function.update p.1 j p.2)) :=
      (hH j).comp (by fun_prop)
    have hipair : Integrable (fun p : (Fin d → ℝ) × ℝ => H j (Function.update p.1 j p.2))
        (π.prod μ) :=
      (MemLp.of_bound (p := 2) hpair.aestronglyMeasurable _
        (ae_of_all _ (fun p => hHb j (Function.update p.1 j p.2)))).integrable (by norm_num)
    calc
      _ ≤ ∫ x, ∫ s, H j (Function.update x j s) ∂μ ∂π :=
        integral_mono (gaussian_coordinate_variance_integrable d f hf hfb j)
          hipair.integral_prod_left (fun x => objective_fiber_variance_le θ B t ht x j)
      _ = ∫ x, H j x ∂π := gaussian_integral_coordinate_resampling d (H j) (hH j)
        ⟨_, fun x => hHb j x⟩ j
  have hvar : Var[projectedObjective θ B t; stdGaussian (Space d)] = Var[f; π] := by
    rw [← map_pi_eq_stdGaussian, variance_map
      (projectedObjective_continuous θ B t).measurable.aemeasurable htoLp.aemeasurable]
    rfl
  rw [hvar]
  calc
    _ ≤ ∑ j, ∫ x, Var[fun s => f (Function.update x j s); μ] ∂π :=
      gaussian_variance_tensorization d f hf hfb
    _ ≤ ∑ j, ∫ x, H j x ∂π := Finset.sum_le_sum (fun j _ => hcoordinate j)
    _ = ∫ x, ∑ j, H j x ∂π := (integral_finsetSum _ (fun j _ => hHi j)).symm
    _ ≤ ∫ _x, 4 * t * operatorNorm B ^ 2 / m ∂π :=
      integral_mono (integrable_finsetSum _ (fun j _ => hHi j)) (integrable_const _)
        (fun x => objectivePartial_square_sum_le hm B t ht (WithLp.toLp 2 x))
    _ = _ := by simp [π, μ]

end NLA.IE22
