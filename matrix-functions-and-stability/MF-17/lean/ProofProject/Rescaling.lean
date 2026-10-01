import ProofProject.Definitions

/-!
# Time rescaling

Accelerating a stable semigroup preserves its normalized exponential bound.
Its complete generator graph scales by the same positive factor, and its
bounded inverse scales by the reciprocal factor. This places each positive-time
attained norm at every later time.
-/

noncomputable section

namespace ProofProject

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- A right derivative under a nonnegative linear change of time. -/
lemma hasDerivWithinAt_mul_time {f : ℝ → H} {y : H} {c : ℝ} (hc : 0 ≤ c)
    (hf : HasDerivWithinAt f y (Set.Ici 0) 0) :
    HasDerivWithinAt (fun s : ℝ => f (c * s)) (c • y) (Set.Ici 0) 0 := by
  have hmul : HasDerivWithinAt (fun s : ℝ => c * s) c (Set.Ici 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul c).hasDerivWithinAt
  simpa [Function.comp_def] using hf.scomp_of_eq 0 hmul
    (fun s hs => mul_nonneg hc hs) (by simp)

/-- Accelerating time by at least one keeps the same normalized stability bound. -/
def StableSemigroup.rescale (T : StableSemigroup M H) (hM : 0 ≤ M)
    {c : ℝ} (hc : 1 ≤ c) : StableSemigroup M H where
  op s := T.op (c * s)
  at_zero := by simpa using T.at_zero
  add s t hs ht := by
    simpa only [mul_add] using
      T.add (c * s) (c * t) (mul_nonneg (by linarith) hs)
        (mul_nonneg (by linarith) ht)
  strong_continuous x :=
    (T.strong_continuous x).comp
      (show Continuous (fun s : ℝ => c * s) from continuous_const.mul continuous_id).continuousOn
      (fun s hs => mul_nonneg (show 0 ≤ c by linarith) hs)
  bound s hs := by
    calc
      ‖T.op (c * s)‖ ≤ M * Real.exp (-(c * s)) :=
        T.bound _ (mul_nonneg (by linarith) hs)
      _ ≤ M * Real.exp (-s) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hM

@[simp] lemma StableSemigroup.rescale_op (T : StableSemigroup M H) (hM : 0 ≤ M)
    {c : ℝ} (hc : 1 ≤ c) (s : ℝ) : (T.rescale hM hc).op s = T.op (c * s) := rfl

lemma GeneratorGraph.rescale {T : StableSemigroup M H} {x y : H} (hM : 0 ≤ M)
    {c : ℝ} (hc : 1 ≤ c) (hxy : GeneratorGraph T x y) :
    GeneratorGraph (T.rescale hM hc) x (c • y) :=
  hasDerivWithinAt_mul_time (c := c) (by linarith) hxy

/-- The rescaled graph is the entire original generator graph with its second
coordinate multiplied by the scale. In particular no domain restriction occurs. -/
lemma generatorGraph_rescale_iff (T : StableSemigroup M H) (hM : 0 ≤ M)
    {c : ℝ} (hc : 1 ≤ c) (x y : H) :
    GeneratorGraph (T.rescale hM hc) x y ↔ GeneratorGraph T x (c⁻¹ • y) := by
  have hc0 : c ≠ 0 := ne_of_gt (by linarith)
  constructor
  · intro hxy
    have h := hasDerivWithinAt_mul_time (c := c⁻¹) (inv_nonneg.mpr (by linarith)) hxy
    simpa [GeneratorGraph, mul_assoc, hc0] using h
  · intro hxy
    simpa [smul_smul, hc0] using hxy.rescale hM hc

lemma IsGeneratorInverse.rescale {T : StableSemigroup M H} {B : H →L[ℂ] H}
    (hB : IsGeneratorInverse T B) (hM : 0 ≤ M) {c : ℝ} (hc : 1 ≤ c) :
    IsGeneratorInverse (T.rescale hM hc) (c⁻¹ • B) := by
  intro x y
  rw [generatorGraph_rescale_iff T hM hc, hB]
  simp [ContinuousLinearMap.map_smul_of_tower]

/-- Reciprocal scaling of the inverse cancels scaling of the observation time. -/
lemma inverseEvolution_rescale (B : H →L[ℂ] H) {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    inverseEvolution (c⁻¹ • B) (c * t) = inverseEvolution B t := by
  unfold inverseEvolution
  congr 1
  rw [smul_comm, ← smul_assoc]
  congr 1
  simp [Complex.real_smul, Complex.ofReal_mul, hc]

/-- Every value attained at a positive time is attained at each later time. -/
lemma attainableNorms_mono_time {t₁ t₂ : ℝ} (hM : 0 ≤ M) (ht₁ : 0 < t₁)
    (htt : t₁ ≤ t₂) : attainableNorms.{u} M t₁ ⊆ attainableNorms.{u} M t₂ := by
  intro r hr
  obtain ⟨H, hH, hInner, hComplete, T, B, hB, hr⟩ := hr
  let := hH
  let := hInner
  let := hComplete
  have hc : 1 ≤ t₂ / t₁ := (le_div_iff₀ ht₁).mpr (by simpa using htt)
  have hc0 : t₂ / t₁ ≠ 0 := ne_of_gt (by linarith)
  refine ⟨H, hH, hInner, hComplete, T.rescale hM hc, (t₂ / t₁)⁻¹ • B,
    hB.rescale hM hc, ?_⟩
  have htime : (t₂ / t₁) * t₁ = t₂ := div_mul_cancel₀ _ ht₁.ne'
  have hevolution := inverseEvolution_rescale B hc0 t₁
  rw [htime] at hevolution
  rw [hevolution]
  exact hr

/-- Transport of finite-dimensional lower-bound witnesses uses the same space. -/
lemma HasFiniteWitness.mono_time {t₁ t₂ lower : ℝ}
    (hw : HasFiniteWitness.{u} M t₁ lower) (hM : 0 ≤ M) (ht₁ : 0 < t₁)
    (htt : t₁ ≤ t₂) : HasFiniteWitness.{u} M t₂ lower := by
  obtain ⟨H, hH, hInner, hComplete, hFinite, T, B, hB, hlower⟩ := hw
  let := hH
  let := hInner
  let := hComplete
  let := hFinite
  have hc : 1 ≤ t₂ / t₁ := (le_div_iff₀ ht₁).mpr (by simpa using htt)
  have hc0 : t₂ / t₁ ≠ 0 := ne_of_gt (by linarith)
  refine ⟨H, hH, hInner, hComplete, hFinite, T.rescale hM hc, (t₂ / t₁)⁻¹ • B,
    hB.rescale hM hc, ?_⟩
  have htime : (t₂ / t₁) * t₁ = t₂ := div_mul_cancel₀ _ ht₁.ne'
  have hevolution := inverseEvolution_rescale B hc0 t₁
  rw [htime] at hevolution
  rw [hevolution]
  exact hlower

end ProofProject
