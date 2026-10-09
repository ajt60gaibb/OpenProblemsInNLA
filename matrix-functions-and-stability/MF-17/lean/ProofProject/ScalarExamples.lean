import ProofProject.Definitions

/-! Scalar exponentially decaying semigroups give the sharp lower value at the
contractive endpoint, and show that every envelope in the target is nonempty. -/

noncomputable section

namespace ProofProject

universe u

variable (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The scalar semigroup with generator `-a I`. -/
def scalarSemigroup (M a : ℝ) (hM : 1 ≤ M) (ha : 1 ≤ a) : StableSemigroup M H where
  op s := Real.exp (-a * s) • ContinuousLinearMap.id ℂ H
  at_zero := by simp
  add s t _ _ := by
    ext x
    simp only [smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, mul_add, Real.exp_add, mul_smul]
  strong_continuous x := by
    change ContinuousOn (fun s : ℝ => Real.exp (-a * s) • x) (Set.Ici 0)
    fun_prop
  bound s hs := by
    calc
      ‖Real.exp (-a * s) • ContinuousLinearMap.id ℂ H‖ ≤
          Real.exp (-a * s) * 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (Real.exp_pos _).le
      _ ≤ M * Real.exp (-s) := by
        have he : Real.exp (-a * s) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by nlinarith)
        nlinarith [Real.exp_pos (-s)]

/-- The bounded scalar inverse of `-a I`. -/
def scalarInverse (a : ℝ) : H →L[ℂ] H := (-a⁻¹ : ℝ) • ContinuousLinearMap.id ℂ H

theorem scalarSemigroup_hasDerivAt (M a : ℝ) (hM : 1 ≤ M) (ha : 1 ≤ a) (x : H) :
    HasDerivAt (fun s : ℝ => (scalarSemigroup H M a hM ha).op s x) ((-a : ℝ) • x) 0 := by
  change HasDerivAt (fun s : ℝ => Real.exp (-a * s) • x) ((-a : ℝ) • x) 0
  simpa using (((hasDerivAt_id (0 : ℝ)).const_mul (-a)).exp.smul_const x)

theorem scalarSemigroup_generatorGraph (M a : ℝ) (hM : 1 ≤ M) (ha : 1 ≤ a) (x y : H) :
    GeneratorGraph (scalarSemigroup H M a hM ha) x y ↔ y = (-a : ℝ) • x := by
  have hd := (scalarSemigroup_hasDerivAt H M a hM ha x).hasDerivWithinAt (s := Set.Ici 0)
  constructor
  · intro hy
    exact (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv (Set.Ici 0) hy hd
  · rintro rfl
    exact hd

theorem scalarSemigroup_isGeneratorInverse (M a : ℝ) (hM : 1 ≤ M) (ha : 1 ≤ a) :
    IsGeneratorInverse (scalarSemigroup H M a hM ha) (scalarInverse H a) := by
  have ha0 : a ≠ 0 := by linarith
  intro x y
  rw [scalarSemigroup_generatorGraph]
  change y = (-a : ℝ) • x ↔ (-a⁻¹ : ℝ) • y = x
  constructor
  · rintro rfl
    simp [smul_smul, ha0]
  · intro h
    rw [← h, smul_smul]
    simp [ha0]


theorem scalarInverse_evolution (a t : ℝ) :
    inverseEvolution (scalarInverse H a) t =
      Real.exp (-t / a) • ContinuousLinearMap.id ℂ H := by
  have hm := NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := H →L[ℂ] H) (-t / a)
  rw [← Real.exp_eq_exp_ℝ] at hm
  rw [inverseEvolution, scalarInverse]
  change NormedSpace.exp ((t : ℂ) • ((-a⁻¹ : ℝ) • (1 : H →L[ℂ] H))) = _
  simpa [Algebra.algebraMap_eq_smul_one, smul_smul, div_eq_mul_inv,
    mul_neg, neg_mul, ContinuousLinearMap.one_def] using hm.symm

theorem norm_scalarInverse_evolution [Nontrivial H] (a t : ℝ) :
    ‖inverseEvolution (scalarInverse H a) t‖ = Real.exp (-t / a) := by
  rw [scalarInverse_evolution, norm_smul, ContinuousLinearMap.norm_id, mul_one,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]


/-- Every admissible scalar decay rate supplies a value of the envelope. -/
theorem scalar_mem_attainableNorms (M a t : ℝ) (hM : 1 ≤ M) (ha : 1 ≤ a) :
    Real.exp (-t / a) ∈ attainableNorms.{u} M t := by
  let H := EuclideanSpace ℂ (ULift.{u} Unit)
  refine ⟨H, inferInstance, inferInstance, inferInstance,
    scalarSemigroup H M a hM ha, scalarInverse H a,
    scalarSemigroup_isGeneratorInverse H M a hM ha, ?_⟩
  exact (norm_scalarInverse_evolution H a t).symm

theorem attainableNorms_nonempty (M t : ℝ) (hM : 1 ≤ M) :
    (attainableNorms.{u} M t).Nonempty :=
  ⟨Real.exp (-t / 1), scalar_mem_attainableNorms M 1 t hM le_rfl⟩

/-- These scalar examples are already finite dimensional. -/
theorem scalar_finiteWitness (M a t : ℝ) (hM : 1 ≤ M) (ha : 1 ≤ a) :
    HasFiniteWitness.{u} M t (Real.exp (-t / a)) := by
  let H := EuclideanSpace ℂ (ULift.{u} Unit)
  refine ⟨H, inferInstance, inferInstance, inferInstance, inferInstance,
    scalarSemigroup H M a hM ha, scalarInverse H a,
    scalarSemigroup_isGeneratorInverse H M a hM ha, ?_⟩
  exact (norm_scalarInverse_evolution H a t).ge

open Filter in
/-- At each fixed time the scalar attainable values approach one. -/
theorem scalar_evolution_tendsto_one (t : ℝ) :
    Tendsto (fun a : ℝ => Real.exp (-t / a)) atTop (nhds 1) := by
  simpa [Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp
    (tendsto_const_nhds.div_atTop tendsto_id :
      Tendsto (fun a : ℝ => -t / a) atTop (nhds 0))


open Filter in
/-- The supremum is at least one once its boundedness has been proved. -/
theorem one_le_growthEnvelope (M t : ℝ) (hM : 1 ≤ M)
    (hbdd : BddAbove (attainableNorms.{u} M t)) :
    1 ≤ growthEnvelope.{u} M t := by
  apply le_of_tendsto (scalar_evolution_tendsto_one t)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
  exact le_csSup hbdd (scalar_mem_attainableNorms M a t hM ha)

end ProofProject
