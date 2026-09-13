/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Mathematical transfer theorem: Matthew J. Colbrook.

The zero-tail branch uses the original difference-of-squared-norms premise.
It retains arbitrary selected null-space bases and the full f(0) error.
-/
import NLA.RA09.Spectral
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
open Matrix
noncomputable section
namespace NLA.RA09

theorem functionTail_of_vanishing {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) (k : ℕ) (hk : k < n)
    (hzero : ∀ i : Fin n, k ≤ i.val → d.eigenvalues i = 0) :
    functionTail d f k = (n-k : ℕ) * (f 0)^2 := by
  have hset : Finset.univ.filter (fun i : Fin n => k ≤ i.val) =
      Finset.Ici (⟨k, hk⟩ : Fin n) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
    rfl
  unfold functionTail
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), (f 0)^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hzero i (Finset.mem_filter.mp hi).2]
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, hset, Fin.card_Ici]

theorem function_error_of_vanishing_tail {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) (k : ℕ) (hk : k < n)
    (hzero : ∀ i : Fin n, k ≤ i.val → d.eigenvalues i = 0) :
    frobeniusSquared (functionalCalculus f A - functionTruncation d f k) =
      (n-k : ℕ) * (f 0)^2 := by
  exact (truncation_semantics_proved d k hk.le f).2.2.2.1.trans
    (functionTail_of_vanishing d f k hk hzero)

theorem zero_tail_closure_proved {n : ℕ} {A Ahat : RealMatrix n}
    (dA : OrderedSpectralData A) (dHat : OrderedSpectralData Ahat)
    (horder : Ahat ≤ A) (f : ℝ → ℝ) (_hf : AdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hτ : dA.eigenvalues ⟨k, hk⟩ = 0)
    (ε : ℝ) (_hε : 0 ≤ ε)
    (hpremise : frobeniusSquared A - frobeniusSquared (truncation dHat k) ≤
      (1+ε) * frobeniusSquared (A-truncation dA k)) :
    A = truncation dHat k ∧ Ahat = A ∧
    frobeniusSquared (functionalCalculus f A - functionTruncation dHat f k) =
      (n-k : ℕ) * (f 0)^2 ∧
    frobeniusSquared (functionalCalculus f A - functionTruncation dA f k) =
      (n-k : ℕ) * (f 0)^2 := by
  have hzA : ∀ i : Fin n, k ≤ i.val → dA.eigenvalues i = 0 := by
    intro i hi
    apply le_antisymm ?_ (dA.nonnegative i)
    simpa only [hτ] using dA.decreasing (show (⟨k, hk⟩ : Fin n) ≤ i from hi)
  have htA := truncation_semantics_proved dA k hk.le f
  have htHat := truncation_semantics_proved dHat k hk.le f
  have heqA : truncation dA k = A := htA.2.2.2.2.mpr hzA
  have hzero : frobeniusSquared (0 : RealMatrix n) = 0 := by simp [frobeniusSquared]
  have hdef := trace_deficit_reduction_proved A (truncation dHat k)
    (orderedSpectral_semantics_proved dA).1 htHat.1 (htHat.2.1.trans horder)
  have hle : frobeniusSquared (A - truncation dHat k) ≤ 0 := by
    apply hdef.2.2.trans
    simpa only [heqA, sub_self, hzero, mul_zero] using hpremise
  have heq : A = truncation dHat k :=
    sub_eq_zero.mp ((frobeniusSquared_eq_zero _).mp
      (le_antisymm hle (frobeniusSquared_nonneg _)))
  have hHat : Ahat = A := le_antisymm horder (by rw [heq]; exact htHat.2.1)
  have hzHat : ∀ i : Fin n, k ≤ i.val → dHat.eigenvalues i = 0 :=
    htHat.2.2.2.2.mp (heq.symm.trans hHat.symm)
  refine ⟨heq, hHat, ?_, function_error_of_vanishing_tail dA f k hk hzA⟩
  rw [← hHat]
  exact function_error_of_vanishing_tail dHat f k hk hzHat

#assert_trust kernel functionTail_of_vanishing
#assert_trust kernel function_error_of_vanishing_tail
#assert_trust kernel zero_tail_closure_proved
#print axioms functionTail_of_vanishing
#print axioms function_error_of_vanishing_tail
#print axioms zero_tail_closure_proved

end NLA.RA09
