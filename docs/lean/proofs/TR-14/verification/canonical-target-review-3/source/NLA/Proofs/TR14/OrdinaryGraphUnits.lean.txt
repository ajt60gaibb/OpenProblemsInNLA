import NLA.Proofs.TR14.OrdinaryGraph
import NLA.Proofs.TR14.UnitSpan
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.Group.Pi.Units

/-! Each actual ordinary graph mode contains an actual ambient unit.
Finite spectral avoidance handles the quotient factor, while finite dual
hyperplane avoidance handles every nonzero ordinary mode functional. The
constant polynomial is used only as a direction; no ordinary factor is
required to have a nonzero constant coordinate. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.TR14

/-- A nonconstant affine scalar equation has at most one solution; a
nonzero constant equation has none. -/
theorem finite_affine_zero_set (a b : ℂ) (ha : a ≠ 0) :
    {c : ℂ | a + c * b = 0}.Finite := by
  classical
  by_cases hb : b = 0
  · simp [hb, ha]
  · apply (Set.finite_singleton (-a / b)).subset
    intro c hc
    apply Set.mem_singleton_iff.mpr
    apply (eq_div_iff hb).mpr
    change a + c * b = 0 at hc
    linear_combination hc

variable {A : Type*} [CommRing A] [Algebra ℂ A] [FiniteDimensional ℂ A]

/-- Actual unit existence in every graph mode of an independent ordinary
decomposition. This works in the same normalized quotient chart. -/
theorem exists_unit_mem_ordinaryGraphSpace {m n r : ℕ}
    (φ : (Fin n → ℂ) →ₗ[ℂ] A) (hφ : ∃ p, φ p = 1)
    (u : Fin r → Fin m → Fin n → ℂ)
    (hind : LinearIndependent ℂ (ordinarySummand u)) (k : Fin m) :
    ∃ a : (A × (Fin r → ℂ))ˣ, (a : A × (Fin r → ℂ)) ∈ ordinaryGraphSpace φ u k := by
  classical
  obtain ⟨p1, hp1⟩ := hφ
  have hnonzero (j : Fin r) : ∃ p, ordinaryModeForm u j k p ≠ 0 := by
    by_contra! hz
    apply ordinaryModeForm_ne_zero u hind j k
    apply LinearMap.ext
    intro p
    exact hz p
  obtain ⟨p0, hp0⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun j : Fin r => ordinaryModeForm u j k) hnonzero
  have hbad : (⋃ j : Fin r, {c : ℂ |
      ordinaryModeForm u j k p0 + c * ordinaryModeForm u j k p1 = 0}).Finite :=
    Set.finite_iUnion fun j => finite_affine_zero_set _ _ (hp0 j)
  have hs := (algebra_finite_spectrum (K := ℂ) (-φ p0)).union hbad
  obtain ⟨c, hc⟩ := hs.exists_notMem
  let p := p0 + c • p1
  have hfirst : IsUnit (φ p) := by
    have hc' : c ∉ spectrum ℂ (-φ p0) := fun h => hc (Or.inl h)
    have hu := spectrum.notMem_iff.mp hc'
    simpa only [p, map_add, map_smul, RingHom.id_apply, hp1,
      Algebra.algebraMap_eq_smul_one, sub_neg_eq_add, add_comm] using hu
  have hscalar (j : Fin r) : ordinaryModeForm u j k p ≠ 0 := by
    intro hz
    apply hc
    right
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change ordinaryModeForm u j k p0 + c * ordinaryModeForm u j k p1 = 0
    simpa only [p, map_add, map_smul, RingHom.id_apply, smul_eq_mul] using hz
  have hunit : IsUnit (ordinaryGraphMap φ u k p) := by
    rw [ordinaryGraphMap_apply, Prod.isUnit_iff]
    exact ⟨hfirst, Pi.isUnit_iff.mpr fun j => isUnit_iff_ne_zero.mpr (hscalar j)⟩
  obtain ⟨a, ha⟩ := hunit
  refine ⟨a, ?_⟩
  rw [ha]
  exact ⟨p, rfl⟩

#assert_trust kernel exists_unit_mem_ordinaryGraphSpace
#print axioms exists_unit_mem_ordinaryGraphSpace

end NLA.Proofs.TR14
