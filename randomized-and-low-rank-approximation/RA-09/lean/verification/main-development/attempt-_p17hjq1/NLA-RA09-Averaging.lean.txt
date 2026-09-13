/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Mathematical averaging argument: Matthew J. Colbrook, ordered transfer proof.
The positive-column conditions below will be derived from actual matrix order.
-/
import NLA.RA09.Scalar

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical
noncomputable section
namespace NLA.RA09

theorem weighted_harmonic_identity {n : ℕ} (a p : Fin n → ℝ) (b D : ℝ)
    (hsum : ∑ i, p i = 1) :
    (∑ i, p i * (D * (1 - b / a i))) =
      D * (1 - b * (∑ i, p i / a i)) := by
  calc
    _ = ∑ i, (D * p i - (D*b) * (p i / a i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
      ring

theorem weighted_scalar_identity {n : ℕ} (a p h v : Fin n → ℝ) (b c B : ℝ)
    (hsum : ∑ i, p i = 1) :
    (∑ i, p i * (h i + 2*B*v i - 2*c^2*b*a i - B^2 + c^2*b^2)) =
      (∑ i, p i*h i) + 2*B*(∑ i, p i*v i) -
        2*c^2*b*(∑ i, p i*a i) - B^2 + c^2*b^2 := by
  calc
    _ = ∑ i, (p i*h i + (2*B)*(p i*v i) -
        (2*c^2*b)*(p i*a i) - B^2*p i + (c^2*b^2)*p i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hsum, mul_one]

theorem positive_column_average {n : ℕ} (a p : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (f : ℝ → ℝ) (hf : AdmissibleFunction f) (τ b : ℝ)
    (hτ : 0 < τ) (hfτ : 0 < f τ) (hb : 0 < b)
    (hsupport : ∀ i, a i = 0 → p i = 0)
    (hharmonic : b * (∑ i, p i / a i) ≤ 1) :
    (f b)^2 - (transferScale f τ)^2*b^2 -
      2*f b*(∑ i, p i*f (a i)) +
        2*(transferScale f τ)^2*b*(∑ i, p i*a i) ≤
      ∑ i, p i * scalarAuxiliary f τ (a i) := by
  let c := transferScale f τ
  let D := f b * max (f b - c*b) 0
  have hD : 0 ≤ D := mul_nonneg (hf.2.2.2 b hb.le) (le_max_right _ _)
  have hsumineq :
      (∑ i, p i * (D * (1 - b / a i))) ≤
      ∑ i, p i * (scalarAuxiliary f τ (a i) + 2*f b*f (a i) -
        2*c^2*b*a i - (f b)^2 + c^2*b^2) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : a i = 0
    · simp only [hsupport i hi, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left
        (ordered_scalar_certificate_proved f hf τ (a i) b hτ hfτ
          (lt_of_le_of_ne (ha i) (Ne.symm hi)) hb) (hp i)
  have hnonneg : 0 ≤ ∑ i, p i * (D * (1-b/a i)) := by
    rw [weighted_harmonic_identity a p b D hsum]
    exact mul_nonneg hD (sub_nonneg.mpr hharmonic)
  have h := hnonneg.trans hsumineq
  rw [weighted_scalar_identity a p (fun i => scalarAuxiliary f τ (a i))
    (fun i => f (a i)) b c (f b) hsum] at h
  change (f b)^2 - c^2*b^2 - 2*f b*(∑ i, p i*f (a i)) +
    2*c^2*b*(∑ i, p i*a i) ≤ ∑ i, p i*scalarAuxiliary f τ (a i)
  linarith

#assert_trust kernel positive_column_average
#print axioms positive_column_average

end NLA.RA09
