import ProofProject.Generator

/-!
# The strong Laplace integral

Integration is performed after applying the semigroup to a vector. No operator
norm continuity or operator-valued Bochner measurability is assumed.
-/

noncomputable section

namespace ProofProject

open MeasureTheory Set Filter
open scoped Topology

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]

namespace StableSemigroup

lemma orbit_bound (T : StableSemigroup M H) (x : H) {s : ℝ} (hs : 0 ≤ s) :
    ‖T.op s x‖ ≤ (M * ‖x‖) * Real.exp (-s) := by
  calc
    ‖T.op s x‖ ≤ ‖T.op s‖ * ‖x‖ := (T.op s).le_opNorm x
    _ ≤ (M * Real.exp (-s)) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (T.bound s hs) (norm_nonneg x)
    _ = _ := by ring

lemma integrable_orbit (T : StableSemigroup M H) (x : H) :
    IntegrableOn (fun s : ℝ => T.op s x) (Ioi 0) := by
  apply ((integrableOn_exp_neg_Ioi 0).const_mul (M * ‖x‖)).mono'
    (((T.strong_continuous x).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  exact T.orbit_bound x hs.le

lemma norm_integral_orbit_le (T : StableSemigroup M H) (x : H) :
    ‖∫ s : ℝ in Ioi 0, T.op s x‖ ≤ M * ‖x‖ := by
  calc
    ‖∫ s : ℝ in Ioi 0, T.op s x‖ ≤
        ∫ s : ℝ in Ioi 0, (M * ‖x‖) * Real.exp (-s) := by
      apply norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi 0).const_mul (M * ‖x‖))
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      exact T.orbit_bound x hs.le
    _ = M * ‖x‖ := by rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

/-- The candidate inverse `-∫₀^∞ T(s) ds`, defined by strong integration. -/
def laplaceInverse (T : StableSemigroup M H) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => -(∫ s : ℝ in Ioi 0, T.op s x)
      map_add' := by
        intro x y
        simp only [map_add]
        rw [integral_add (T.integrable_orbit x) (T.integrable_orbit y), neg_add]
      map_smul' := by
        intro c x
        simp only [map_smul, integral_smul, smul_neg, RingHom.id_apply] }
    M (fun x => by
      change ‖-(∫ s : ℝ in Ioi 0, T.op s x)‖ ≤ M * ‖x‖
      simpa only [norm_neg] using T.norm_integral_orbit_le x)

@[simp] lemma laplaceInverse_apply (T : StableSemigroup M H) (x : H) :
    T.laplaceInverse x = -(∫ s : ℝ in Ioi 0, T.op s x) := rfl

lemma norm_laplaceInverse_le (T : StableSemigroup M H) (hM : 0 ≤ M) :
    ‖T.laplaceInverse‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro x
  simpa only [laplaceInverse_apply, norm_neg] using T.norm_integral_orbit_le x

end StableSemigroup

end ProofProject
