/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Mathematical transfer theorem: Matthew J. Colbrook.
Exact finite tail identities at a positive actual discarded eigenvalue.
-/
import NLA.RA09.Spectral
import NLA.RA09.Scalar

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
noncomputable section
namespace NLA.RA09

theorem cutoff_square_comparisons {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) (hf : AdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hτ : 0 < d.eigenvalues ⟨k,hk⟩) :
    (∀ i : Fin n, i.val < k → (f (d.eigenvalues i))^2 ≤
      (transferScale f (d.eigenvalues ⟨k,hk⟩))^2 * (d.eigenvalues i)^2) ∧
    (∀ i : Fin n, k ≤ i.val →
      (transferScale f (d.eigenvalues ⟨k,hk⟩))^2 * (d.eigenvalues i)^2 ≤
        (f (d.eigenvalues i))^2) := by
  obtain ⟨_, hc, hlo, hhi, _, _⟩ :=
    admissible_scalar_consequences_proved f hf (d.eigenvalues ⟨k,hk⟩) hτ
  constructor
  · intro i hi
    have hb := hhi _ (d.decreasing (show i ≤ ⟨k,hk⟩ from Nat.le_of_lt hi))
    have hn := mul_nonneg (sub_nonneg.mpr hb)
      (add_nonneg (mul_nonneg hc (d.nonnegative i)) (hf.2.2.2 _ (d.nonnegative i)))
    nlinarith [hn]
  · intro i hi
    have hb := hlo _ (d.nonnegative i) (d.decreasing (show (⟨k,hk⟩ : Fin n) ≤ i from hi))
    have hn := mul_nonneg (sub_nonneg.mpr hb)
      (add_nonneg (hf.2.2.2 _ (d.nonnegative i)) (mul_nonneg hc (d.nonnegative i)))
    nlinarith [hn]

theorem spectral_auxiliary_sum {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) (hf : AdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hτ : 0 < d.eigenvalues ⟨k,hk⟩) :
    (∑ i, ((f (d.eigenvalues i))^2 -
      (transferScale f (d.eigenvalues ⟨k,hk⟩))^2 * (d.eigenvalues i)^2 +
        scalarAuxiliary f (d.eigenvalues ⟨k,hk⟩) (d.eigenvalues i))) =
      functionTail d f k -
        (transferScale f (d.eigenvalues ⟨k,hk⟩))^2 * spectralTail d k := by
  obtain ⟨hhead, htail⟩ := cutoff_square_comparisons d f hf k hk hτ
  unfold functionTail spectralTail
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < k
  · have hh := hhead i hi
    have hm := max_eq_left (sub_nonneg.mpr hh)
    simp only [scalarAuxiliary, hm, Nat.not_le.mpr hi, ↓reduceIte]
    ring
  · have ht := htail i (Nat.le_of_not_gt hi)
    have hm := max_eq_right (sub_nonpos.mpr ht)
    simp only [scalarAuxiliary, hm, Nat.le_of_not_gt hi, ↓reduceIte, add_zero]

theorem spectral_tail_scaling {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) (hf : AdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hτ : 0 < d.eigenvalues ⟨k,hk⟩) :
    (transferScale f (d.eigenvalues ⟨k,hk⟩))^2 * spectralTail d k ≤
      functionTail d f k := by
  have ht := (cutoff_square_comparisons d f hf k hk hτ).2
  unfold spectralTail functionTail
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => ht i (Finset.mem_filter.mp hi).2

#assert_trust kernel spectral_auxiliary_sum
#assert_trust kernel spectral_tail_scaling
#print axioms spectral_auxiliary_sum
#print axioms spectral_tail_scaling

end NLA.RA09
