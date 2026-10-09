import ProofProject.Laplace

/-! The strong Laplace integral gives a right inverse of the generator. -/

noncomputable section

namespace ProofProject

open MeasureTheory Set Filter
open scoped Topology

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H]

namespace StableSemigroup

omit [CompleteSpace H] in
lemma integral_shift_orbit (T : StableSemigroup M H) (x : H) (t : ℝ) :
    (∫ s : ℝ in Ioi 0, T.op (t + s) x) = ∫ s : ℝ in Ioi t, T.op s x := by
  have hp : (fun s : ℝ => t + s) ⁻¹' Ioi t = Ioi 0 := by
    ext s
    simp
  simpa only [hp] using
    (measurePreserving_add_left volume t).setIntegral_preimage_emb
      (measurableEmbedding_addLeft t) (fun s => T.op s x) (Ioi t)

lemma laplaceInverse_orbit (T : StableSemigroup M H) (x : H) {t : ℝ} (ht : 0 ≤ t) :
    T.op t (T.laplaceInverse x) = -(∫ s : ℝ in Ioi t, T.op s x) := by
  rw [laplaceInverse_apply, map_neg, ← (T.op t).integral_comp_comm (T.integrable_orbit x)]
  congr 1
  calc
    (∫ s : ℝ in Ioi 0, T.op t (T.op s x)) =
        ∫ s : ℝ in Ioi 0, T.op (t + s) x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      change T.op t (T.op s x) = T.op (t + s) x
      rw [T.add t s ht hs.le, ContinuousLinearMap.comp_apply]
    _ = _ := T.integral_shift_orbit x t

lemma laplaceInverse_orbit_sub (T : StableSemigroup M H) (x : H) {t : ℝ} (ht : 0 ≤ t) :
    T.op t (T.laplaceInverse x) - T.laplaceInverse x = ∫ s : ℝ in 0..t, T.op s x := by
  rw [T.laplaceInverse_orbit x ht, laplaceInverse_apply, sub_neg_eq_add, neg_add_eq_sub]
  exact intervalIntegral.integral_Ioi_sub_Ioi (T.integrable_orbit x) ht

/-- The generator applied to the candidate inverse is the identity. -/
theorem laplaceInverse_graph (T : StableSemigroup M H) (x : H) :
    GeneratorGraph T (T.laplaceInverse x) x := by
  have hd : HasDerivWithinAt (fun t : ℝ => ∫ s : ℝ in 0..t, T.op s x)
      x (Ici 0) 0 := by
    have h := intervalIntegral.integral_hasDerivWithinAt_right
      (f := fun s : ℝ => T.op s x) (a := 0) (b := 0) (s := Ici 0) (t := Ioi 0)
      (by simp)
      (((T.strong_continuous x).mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi 0)
      ((T.strong_continuous x 0 (by simp)).mono Ioi_subset_Ici_self)
    simpa only [T.at_zero, ContinuousLinearMap.id_apply] using h
  have heq (t : ℝ) (ht : t ∈ Ici 0) :
      T.op t (T.laplaceInverse x) = (∫ s : ℝ in 0..t, T.op s x) + T.laplaceInverse x :=
    sub_eq_iff_eq_add.mp (T.laplaceInverse_orbit_sub x ht)
  exact (hd.add_const (T.laplaceInverse x)).congr_of_mem heq (by simp)

end StableSemigroup

end ProofProject
