import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

/-!
# Operators obtained by integrating continuous vector orbits on an interval

The integral is taken after application to a vector. Strong continuity of
the orbits and a uniform operator bound give a continuous linear operator,
without operator-valued measurability or operator-norm continuity. Continuity
of the adjoint orbits gives the corresponding vector integral for its adjoint.
The interval may be empty, and the Hilbert space need not be separable.
-/

noncomputable section

namespace ProofProject

open MeasureTheory Set Filter

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every weighted vector orbit is Bochner integrable on the compact interval. -/
theorem intervalOperatorIntegral_integrable
    (S : ℝ → H →L[ℂ] H) (k : ℝ → ℂ) (a b : ℝ)
    (hk : ContinuousOn k (Icc a b))
    (hS : ∀ x : H, ContinuousOn (fun s => S s x) (Icc a b)) (x : H) :
    IntegrableOn (fun s => k s • S s x) (Icc a b) :=
  (hk.smul (hS x)).integrableOn_compact isCompact_Icc

/-- The strong integral obeys the scalar `L¹` kernel bound. -/
theorem norm_intervalOperatorIntegral_apply_le
    (S : ℝ → H →L[ℂ] H) (k : ℝ → ℂ) (a b M : ℝ)
    (hk : ContinuousOn k (Icc a b))
    (hbound : ∀ s ∈ Icc a b, ‖S s‖ ≤ M) (x : H) :
    ‖∫ s in Icc a b, k s • S s x‖ ≤
      (M * ∫ s in Icc a b, ‖k s‖) * ‖x‖ := by
  have hkint : IntegrableOn (fun s => ‖k s‖) (Icc a b) :=
    hk.norm.integrableOn_compact isCompact_Icc
  calc
    _ ≤ ∫ s in Icc a b, (‖k s‖ * M) * ‖x‖ := by
      apply norm_integral_le_of_norm_le ((hkint.mul_const M).mul_const ‖x‖)
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
      rw [norm_smul]
      calc
        ‖k s‖ * ‖S s x‖ ≤ ‖k s‖ * (M * ‖x‖) :=
          mul_le_mul_of_nonneg_left
            (((S s).le_opNorm x).trans
              (mul_le_mul_of_nonneg_right (hbound s hs) (norm_nonneg _)))
            (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [integral_mul_const, integral_mul_const]; ring

/-- A bounded operator constructed exclusively from strong vector integrals. -/
def intervalOperatorIntegral
    (S : ℝ → H →L[ℂ] H) (k : ℝ → ℂ) (a b M : ℝ)
    (hk : ContinuousOn k (Icc a b))
    (hS : ∀ x : H, ContinuousOn (fun s => S s x) (Icc a b))
    (_hM : 0 ≤ M) (hbound : ∀ s ∈ Icc a b, ‖S s‖ ≤ M) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => ∫ s in Icc a b, k s • S s x
      map_add' := by
        intro x y
        simp only [map_add, smul_add]
        exact integral_add (intervalOperatorIntegral_integrable S k a b hk hS x)
          (intervalOperatorIntegral_integrable S k a b hk hS y)
      map_smul' := by
        intro c x
        simp only [map_smul, smul_comm (k _) c, integral_smul, RingHom.id_apply] }
    (M * ∫ s in Icc a b, ‖k s‖)
    (norm_intervalOperatorIntegral_apply_le S k a b M hk hbound)

@[simp]
theorem intervalOperatorIntegral_apply
    (S : ℝ → H →L[ℂ] H) (k : ℝ → ℂ) (a b M : ℝ)
    (hk : ContinuousOn k (Icc a b))
    (hS : ∀ x : H, ContinuousOn (fun s => S s x) (Icc a b))
    (hM : 0 ≤ M) (hbound : ∀ s ∈ Icc a b, ‖S s‖ ≤ M) (x : H) :
    intervalOperatorIntegral S k a b M hk hS hM hbound x =
      ∫ s in Icc a b, k s • S s x := rfl

theorem intervalOperatorIntegral_norm_le
    (S : ℝ → H →L[ℂ] H) (k : ℝ → ℂ) (a b M : ℝ)
    (hk : ContinuousOn k (Icc a b))
    (hS : ∀ x : H, ContinuousOn (fun s => S s x) (Icc a b))
    (hM : 0 ≤ M) (hbound : ∀ s ∈ Icc a b, ‖S s‖ ≤ M) :
    ‖intervalOperatorIntegral S k a b M hk hS hM hbound‖ ≤
      M * ∫ s in Icc a b, ‖k s‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hM (integral_nonneg fun _ => norm_nonneg _))
  exact norm_intervalOperatorIntegral_apply_le S k a b M hk hbound

/-- The adjoint is again computed by vector integration, with the scalar
kernel conjugated. Only adjoint-orbit continuity is added. -/
theorem intervalOperatorIntegral_adjoint_apply
    (S : ℝ → H →L[ℂ] H) (k : ℝ → ℂ) (a b M : ℝ)
    (hk : ContinuousOn k (Icc a b))
    (hS : ∀ x : H, ContinuousOn (fun s => S s x) (Icc a b))
    (hM : 0 ≤ M) (hbound : ∀ s ∈ Icc a b, ‖S s‖ ≤ M)
    (hSadj : ∀ y : H, ContinuousOn (fun s => star (S s) y) (Icc a b)) (y : H) :
    (intervalOperatorIntegral S k a b M hk hS hM hbound).adjoint y =
      ∫ s in Icc a b, star (k s) • star (S s) y := by
  have hiadj : IntegrableOn (fun s => star (k s) • star (S s) y) (Icc a b) :=
    intervalOperatorIntegral_integrable (fun s => star (S s)) (fun s => star (k s))
      a b hk.star hSadj y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, intervalOperatorIntegral_apply]
  calc
    inner ℂ (∫ s in Icc a b, k s • S s x) y =
        ∫ s in Icc a b, inner ℂ (k s • S s x) y := by
      exact (ContinuousLinearMap.integral_comp_commSL RCLike.conj_smul (innerSLFlip ℂ y)
        (intervalOperatorIntegral_integrable S k a b hk hS x)).symm
    _ = ∫ s in Icc a b, inner ℂ x (star (k s) • star (S s) y) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        simp only [inner_smul_left, inner_smul_right, starRingEnd_apply,
          ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℂ x (∫ s in Icc a b, star (k s) • star (S s) y) :=
      (innerSL ℂ x).integral_comp_comm hiadj

end ProofProject
