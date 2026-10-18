import NLA.Proofs.TR14.MomentRecurrenceReconstruction
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Data.Fintype.EquivFin

/-! Actual affine root enumeration and finite Vandermonde moment matching.
No root count, reconstruction coefficients or rank-one decomposition is assumed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.TR14

/-- The actual roots of a monic separable complex polynomial supply exactly
its degree many distinct affine nodes. Zero is an allowed node. -/
theorem exists_separable_root_family (P : Polynomial ℂ) (hm : P.Monic)
    (hs : P.Separable) :
    ∃ z : Fin P.natDegree → ℂ, Function.Injective z ∧ ∀ i, P.eval (z i) = 0 := by
  classical
  have hc : P.roots.toFinset.card = P.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs)]
    exact (IsAlgClosed.splits P).natDegree_eq_card_roots.symm
  let e : Fin P.natDegree ≃ P.roots.toFinset := (Finset.equivFinOfCardEq hc).symm
  refine ⟨fun i => (e i).val, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    exact Subtype.ext hij
  · intro i
    exact (Polynomial.mem_roots hm.ne_zero).mp (Multiset.mem_toFinset.mp (e i).property)

/-- Invertibility of the actual square Vandermonde matrix matches the first
v moments, with no hypothesis on those complex moment values. -/
theorem exists_vandermonde_weights {D v : ℕ} (h : Fin (D + 1) → ℂ)
    (hvD : v ≤ D + 1) (z : Fin v → ℂ) (hz : Function.Injective z) :
    ∃ c : Fin v → ℂ, ∀ j : Fin v,
      h ⟨j.val, by have hj := j.isLt; omega⟩ = ∑ i, c i * z i ^ j.val := by
  classical
  have hu : IsUnit (Matrix.vandermonde z) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hz))
  let initial : Fin v → ℂ := fun j => h ⟨j.val, by have hj := j.isLt; omega⟩
  obtain ⟨c, hc⟩ := (Matrix.vecMul_surjective_iff_isUnit.mpr hu) initial
  refine ⟨c, ?_⟩
  intro j
  simpa only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply, initial] using
    (congrFun hc j).symm

/-- A monic separable recurrence reconstructs every available moment as an
actual finite weighted power sum. The degree-D+1 case needs no recurrence step. -/
theorem exists_powerSum_of_monic_separable_recurrence {D : ℕ}
    (h : Fin (D + 1) → ℂ) (P : Polynomial ℂ) (hm : P.Monic)
    (hs : P.Separable) (hPD : P.natDegree ≤ D + 1)
    (hr : MonicMomentRecurrence h P) :
    ∃ z c : Fin P.natDegree → ℂ,
      ∀ j : Fin (D + 1), h j = ∑ i, c i * z i ^ j.val := by
  obtain ⟨z, hzi, hz⟩ := exists_separable_root_family P hm hs
  obtain ⟨c, hc⟩ := exists_vandermonde_weights h hPD z hzi
  let h' : Fin (D + 1) → ℂ := fun j => ∑ i, c i * z i ^ j.val
  have heq : h = h' := momentRecurrence_unique h h' P hr
    (powerSum_monicMomentRecurrence P hm z hz c) (by
      intro j hj
      exact hc ⟨j.val, hj⟩)
  exact ⟨z, c, fun j => congrFun heq j⟩

/-- Actual Vandermonde reconstruction gives the frozen same-vector symmetric
width, with every exceptional moment and zero affine root allowed. -/
theorem symmetricWidth_of_monic_separable_recurrence {m n : ℕ}
    (h : Fin (m * (n - 1) + 1) → ℂ) (P : Polynomial ℂ)
    (hm : P.Monic) (hs : P.Separable) (hPD : P.natDegree ≤ m * (n - 1) + 1)
    (hr : MonicMomentRecurrence h P) :
    NLA.Statements.TR14.SymmetricWidth (NLA.Statements.TR14.Hankel h) P.natDegree := by
  obtain ⟨z, c, hc⟩ := exists_powerSum_of_monic_separable_recurrence h P hm hs hPD hr
  refine ⟨c, (fun i j => z i ^ j.val), ?_⟩
  intro j
  change h (NLA.Statements.TR14.HankelIndex j) = _
  rw [hc]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun k => (j k).val) (z i)).symm

#assert_trust kernel exists_separable_root_family
#assert_trust kernel exists_vandermonde_weights
#assert_trust kernel exists_powerSum_of_monic_separable_recurrence
#assert_trust kernel symmetricWidth_of_monic_separable_recurrence
#print axioms symmetricWidth_of_monic_separable_recurrence

end NLA.Proofs.TR14
