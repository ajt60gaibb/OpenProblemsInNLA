import ProofProject.BoundedSemigroup
import ProofProject.IntervalOperatorIntegral

/-!
# Strong scalar-kernel integrals for a bounded semigroup

Extend each orbit to negative times by its value at zero. This gives a bounded
continuous vector function, so every scalar `L¹` kernel defines a bounded
operator. For kernels vanishing at negative times the integral is precisely
the original semigroup integral. No operator-valued integral is used.
-/

noncomputable section

open MeasureTheory Set

namespace ProofProject.BoundedSemigroup

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def positiveOrbit (S : BoundedSemigroup M H) (x : H) (s : ℝ) : H :=
  S.op (max s 0) x

theorem positiveOrbit_continuous (S : BoundedSemigroup M H) (x : H) :
    Continuous (S.positiveOrbit x) := by
  exact (S.strong_continuous x).comp_continuous
    (continuous_id.max continuous_const) (fun s => le_max_right s 0)

theorem positiveOrbit_norm_le (S : BoundedSemigroup M H) (x : H) (s : ℝ) :
    ‖S.positiveOrbit x s‖ ≤ M * ‖x‖ :=
  ((S.op (max s 0)).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (S.bound _ (le_max_right _ _)) (norm_nonneg _))

theorem kernelOrbit_integrable (S : BoundedSemigroup M H)
    {k : ℝ → ℂ} (hk : Integrable k) (x : H) :
    Integrable (fun s => k s • S.positiveOrbit x s) := by
  apply Integrable.mono' (hk.norm.mul_const (M * ‖x‖))
    (hk.aestronglyMeasurable.smul (S.positiveOrbit_continuous x).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun s => by
    change ‖k s • S.positiveOrbit x s‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (S.positiveOrbit_norm_le x s) (norm_nonneg _)

theorem norm_kernelOrbit_integral_le (S : BoundedSemigroup M H)
    {k : ℝ → ℂ} (hk : Integrable k) (x : H) :
    ‖∫ s, k s • S.positiveOrbit x s‖ ≤ (M * ∫ s, ‖k s‖) * ‖x‖ := by
  calc
    _ ≤ ∫ s, ‖k s‖ * (M * ‖x‖) := norm_integral_le_of_norm_le
      (hk.norm.mul_const _) (Filter.Eventually.of_forall fun s => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (S.positiveOrbit_norm_le x s) (norm_nonneg _))
    _ = _ := by rw [integral_mul_const]; ring

/-- A scalar `L¹` kernel is integrated only after applying the orbit to a vector. -/
def kernelOperator (S : BoundedSemigroup M H) (k : ℝ → ℂ) (hk : Integrable k) :
    H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => ∫ s, k s • S.positiveOrbit x s
      map_add' := by
        intro x y
        simp only [positiveOrbit, map_add, smul_add]
        exact integral_add (S.kernelOrbit_integrable hk x) (S.kernelOrbit_integrable hk y)
      map_smul' := by
        intro c x
        simp only [positiveOrbit, map_smul, smul_comm (k _) c, integral_smul,
          RingHom.id_apply] }
    (M * ∫ s, ‖k s‖) (S.norm_kernelOrbit_integral_le hk)

@[simp]
theorem kernelOperator_apply (S : BoundedSemigroup M H)
    (k : ℝ → ℂ) (hk : Integrable k) (x : H) :
    S.kernelOperator k hk x = ∫ s, k s • S.positiveOrbit x s := rfl

theorem kernelOperator_norm_le (S : BoundedSemigroup M H)
    (k : ℝ → ℂ) (hk : Integrable k) :
    ‖S.kernelOperator k hk‖ ≤ M * ∫ s, ‖k s‖ :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg S.bound_nonneg (integral_nonneg fun _ => norm_nonneg _))
    (S.norm_kernelOrbit_integral_le hk)

theorem kernelOperator_apply_of_nonneg_support (S : BoundedSemigroup M H)
    (k : ℝ → ℂ) (hk : Integrable k) (hsupp : ∀ s < 0, k s = 0) (x : H) :
    S.kernelOperator k hk x = ∫ s, k s • S.op s x := by
  rw [kernelOperator_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    by_cases hs : 0 ≤ s
    · simp only [positiveOrbit, max_eq_left hs]
    · simp only [hsupp s (lt_of_not_ge hs), zero_smul]

theorem kernelOperator_inner (S : BoundedSemigroup M H)
    (k : ℝ → ℂ) (hk : Integrable k) (x y : H) :
    inner ℂ y (S.kernelOperator k hk x) =
      ∫ s, k s * inner ℂ y (S.positiveOrbit x s) := by
  rw [kernelOperator_apply]
  calc
    _ = ∫ s, inner ℂ y (k s • S.positiveOrbit x s) :=
      ((innerSL ℂ y).integral_comp_comm (S.kernelOrbit_integrable hk x)).symm
    _ = _ := by simp only [inner_smul_right]

theorem kernelOperator_inner_of_nonneg_support (S : BoundedSemigroup M H)
    (k : ℝ → ℂ) (hk : Integrable k) (hsupp : ∀ s < 0, k s = 0) (x y : H) :
    inner ℂ y (S.kernelOperator k hk x) = ∫ s, k s * inner ℂ y (S.op s x) := by
  rw [kernelOperator_inner]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    by_cases hs : 0 ≤ s
    · simp only [positiveOrbit, max_eq_left hs]
    · simp only [hsupp s (lt_of_not_ge hs), zero_mul]

/-- Every nonnegative semigroup time commutes with the kernel operator. -/
theorem kernelOperator_commutes (S : BoundedSemigroup M H)
    (k : ℝ → ℂ) (hk : Integrable k) {a : ℝ} (ha : 0 ≤ a) :
    (S.op a).comp (S.kernelOperator k hk) = (S.kernelOperator k hk).comp (S.op a) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, kernelOperator_apply]
  rw [← (S.op a).integral_comp_comm (S.kernelOrbit_integrable hk x)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    simp only [map_smul, positiveOrbit]
    congr 1
    have ht := S.add a (max s 0) ha (le_max_right _ _)
    have hs := S.add (max s 0) a (le_max_right _ _) ha
    rw [add_comm a] at ht
    exact congrArg (fun A : H →L[ℂ] H => A x) (ht.symm.trans hs)

end ProofProject.BoundedSemigroup
