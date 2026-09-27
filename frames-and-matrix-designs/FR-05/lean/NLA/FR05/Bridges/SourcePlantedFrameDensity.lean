/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Identification of the source's independent planted frame with its Gaussian
product-density law, including the conjugate-row convention.
-/
import NLA.FR05.Measure.Comparison
import NLA.FR05.Bridges.SourcePlantedDensityBridge
import NLA.FR05.Likelihood.SourceKernelMarginals

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace NLA.FR05


/-- The first two coordinates in the source's `n + 2` convention. -/
def sourceHead {n : ℕ} (x : Signal (n + 2)) : Signal 2 :=
  fun i ↦ x ⟨i.val, by lia⟩

def sourceHeadTailSplit {n : ℕ} (x : Signal (n + 2)) : Signal 2 × Signal n :=
  (sourceHead x, fun i ↦ x ⟨i.val + 2, by lia⟩)

@[fun_prop] theorem measurable_sourceHead {n : ℕ} :
    Measurable (sourceHead (n := n)) := by unfold sourceHead; fun_prop

@[fun_prop] theorem measurable_sourceHeadTailSplit {n : ℕ} :
    Measurable (sourceHeadTailSplit (n := n)) := by
  unfold sourceHeadTailSplit; fun_prop

theorem sourceHead_sourceHeadTailJoin {n : ℕ} (p : Signal 2 × Signal n) :
    sourceHead (sourceHeadTailJoin p) = p.1 := by
  ext i
  fin_cases i <;> simp [sourceHead, sourceHeadTailJoin, joinTwo]

theorem sourceHeadTailJoin_split {n : ℕ} (x : Signal (n + 2)) :
    sourceHeadTailJoin (sourceHeadTailSplit x) = x := by
  ext i
  by_cases h0 : i.val = 0
  · simp [sourceHeadTailJoin, sourceHeadTailSplit, sourceHead, joinTwo, h0]
    congr 1
    exact Fin.ext h0.symm
  by_cases h1 : i.val = 1
  · simp [sourceHeadTailJoin, sourceHeadTailSplit, sourceHead, joinTwo, h1]
    congr 1
    exact Fin.ext h1.symm
  · simp only [sourceHeadTailJoin, sourceHeadTailSplit, joinTwo, dif_neg h0, dif_neg h1]
    congr 1
    apply Fin.ext
    dsimp
    lia

theorem standardComplexGaussianTail_map_sourceHeadTailSplit (n : ℕ) :
    (standardComplexGaussianTail (n + 2)).map sourceHeadTailSplit =
      (standardComplexGaussianTail 2).prod (standardComplexGaussianTail n) := by
  simp only [standardComplexGaussianTail_eq_pi]
  let e : Fin (n + 2) ≃ Fin 2 ⊕ Fin n :=
    (finCongr (Nat.add_comm n 2)).trans finSumFinEquiv.symm
  have h1 := measurePreserving_piCongrLeft
    (fun _ : Fin 2 ⊕ Fin n ↦ scalarComplexGaussian) e
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin 2 ⊕ Fin n ↦ scalarComplexGaussian)
  convert (h2.comp h1).map_eq using 1
  congr 1
  funext x
  simp only [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft'_symm]
  apply Prod.ext
  · funext i
    change x ⟨i.val, _⟩ = x (e.symm (Sum.inl i))
    congr 1
  · funext i
    change x ⟨i.val + 2, _⟩ = x (e.symm (Sum.inr i))
    congr 1
    apply Fin.ext
    simp [e]

theorem standardComplexGaussianTail_prod_map_sourceHeadTailJoin (n : ℕ) :
    ((standardComplexGaussianTail 2).prod (standardComplexGaussianTail n)).map
      sourceHeadTailJoin = standardComplexGaussianTail (n + 2) := by
  rw [← standardComplexGaussianTail_map_sourceHeadTailSplit,
    Measure.map_map measurable_sourceHeadTailJoin measurable_sourceHeadTailSplit]
  have he : sourceHeadTailJoin ∘ sourceHeadTailSplit =
      (id : Signal (n + 2) → Signal (n + 2)) := funext sourceHeadTailJoin_split
  rw [he, Measure.map_id]

/-- The full sampled column has the two-coordinate planted density relative
to the standard Gaussian law in all coordinates. -/
theorem sourcePlantedColumnLaw_eq_withDensity {M n : ℕ} (hM : 1 ≤ M) :
    sourcePlantedColumnLaw sourceEta (sourceDelta M) (sourceEpsilon M) n =
      (standardComplexGaussianTail (n + 2)).withDensity
        (fun x ↦ ENNReal.ofReal (sourcePlantedDensity M (sourceHead x))) := by
  rw [sourcePlantedColumnLaw_eq_density_head_tail hM]
  change (((standardComplexGaussianTail 2).withDensity
    (fun z ↦ ENNReal.ofReal (sourcePlantedDensity M z))).prod
      (standardComplexGaussianTail n)).map sourceHeadTailJoin = _
  rw [prod_withDensity_left (measurable_sourcePlantedDensity M).ennreal_ofReal]
  have he : (fun p : Signal 2 × Signal n ↦ ENNReal.ofReal (sourcePlantedDensity M p.1)) =
      (fun x ↦ ENNReal.ofReal (sourcePlantedDensity M (sourceHead x))) ∘
        sourceHeadTailJoin := by
    funext p
    rw [Function.comp_apply, sourceHead_sourceHeadTailJoin]
  rw [he]
  change Measure.map sourceHeadTailJoin
    (((standardComplexGaussianTail 2).prod (standardComplexGaussianTail n)).withDensity
      (fun p ↦ ENNReal.ofReal (sourcePlantedDensity M (sourceHead (sourceHeadTailJoin p))))) = _
  rw [map_withDensity_comp _ _ measurable_sourceHeadTailJoin
    (fun x ↦ ENNReal.ofReal (sourcePlantedDensity M (sourceHead x)))
    (show Measurable (fun x : Signal (n + 2) ↦
      ENNReal.ofReal (sourcePlantedDensity M (sourceHead x))) from
      ((measurable_sourcePlantedDensity M).comp measurable_sourceHead).ennreal_ofReal),
    standardComplexGaussianTail_prod_map_sourceHeadTailJoin]

theorem standardComplexGaussianFrame_map_star (m d : ℕ) :
    (standardComplexGaussianFrame m d).map (fun A i ↦ star (A i)) =
      standardComplexGaussianFrame m d := by
  rw [standardComplexGaussianFrame_eq_pi]
  have h := Measure.pi_map_pi (μ := fun _ : Fin m ↦ standardComplexGaussianTail d)
    (f := fun _ : Fin m ↦ (star : Signal d → Signal d)) (fun _ ↦ by fun_prop)
  simp only [standardComplexGaussianTail_map_star] at h
  exact h

/-- Independent planted rows, with the manuscript's conjugate-row convention,
have the product of the planted head densities relative to the Gaussian frame. -/
theorem iidSourcePlantedFrameLaw_eq_withDensity {M m n : ℕ} (hM : 1 ≤ M) :
    iidSourcePlantedFrameLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n =
      (standardComplexGaussianFrame m (n + 2)).withDensity
        (fun A ↦ ENNReal.ofReal (∏ i, sourcePlantedDensity M (sourceHead (star (A i))))) := by
  let f : Signal (n + 2) → ℝ := fun x ↦ sourcePlantedDensity M (sourceHead x)
  have hf : Measurable f := (measurable_sourcePlantedDensity M).comp measurable_sourceHead
  have hf0 : ∀ x, 0 ≤ f x := fun x ↦ sourcePlantedDensity_nonneg M _
  have hfi : Integrable f (standardComplexGaussianTail (n + 2)) := by
    apply Integrable.of_bound hf.aestronglyMeasurable (Real.exp 1 * (M : ℝ) ^ 52)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    exact sourcePlantedDensity_le hM _
  have : IsProbabilityMeasure ((standardComplexGaussianTail (n + 2)).withDensity
      (fun x ↦ ENNReal.ofReal (f x))) := by
    rw [← sourcePlantedColumnLaw_eq_withDensity hM]
    exact isProbabilityMeasure_sourcePlantedColumnLaw sourceEta_pos.le sourceEta_lt_one
      (sourceEpsilon_pos M hM) n
  unfold iidSourcePlantedFrameLaw iidSourcePlantedColumnLaw
  simp_rw [sourcePlantedColumnLaw_eq_withDensity hM]
  rw [Measure.pi_withDensity_ofReal (ι := Fin m) _ f hf0 hfi,
    ← standardComplexGaussianFrame_eq_pi]
  have he : (fun A : Frame m (n + 2) ↦ ENNReal.ofReal (∏ i, f (A i))) =
      (fun A ↦ ENNReal.ofReal (∏ i, f (star (A i)))) ∘ frameFromPlantedColumns := by
    funext A
    change ENNReal.ofReal (∏ i, f (A i)) = ENNReal.ofReal (∏ i, f (star (star (A i))))
    simp only [star_star]
  change Measure.map frameFromPlantedColumns
    ((standardComplexGaussianFrame m (n + 2)).withDensity
      (fun A ↦ ENNReal.ofReal (∏ i, f (A i)))) = _
  rw [he]
  change Measure.map frameFromPlantedColumns
    ((standardComplexGaussianFrame m (n + 2)).withDensity
      (fun A ↦ ENNReal.ofReal (∏ i, f (star (frameFromPlantedColumns A i)))) ) = _
  have hh := map_withDensity_comp (standardComplexGaussianFrame m (n + 2))
    (fun A : Frame m (n + 2) ↦ fun i ↦ star (A i)) (by fun_prop)
    (fun A : Frame m (n + 2) ↦ ENNReal.ofReal (∏ i, f (star (A i)))) (by fun_prop)
  rw [standardComplexGaussianFrame_map_star] at hh
  exact hh

end NLA.FR05
