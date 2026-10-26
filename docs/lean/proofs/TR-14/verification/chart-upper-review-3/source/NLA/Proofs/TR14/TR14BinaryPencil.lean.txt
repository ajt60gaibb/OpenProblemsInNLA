import NLA.Proofs.TR14.TR14BinaryInverse
import Mathlib.FieldTheory.Separable
import Mathlib.Data.Set.Finite.Basic

/-! A concrete separable affine pencil over the complex numbers. The finite
exceptional parameter set is derived from the actual Wronskian polynomial. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial
noncomputable section

/-- Coprimality prevents the Wronskian from vanishing identically when the
second polynomial has positive degree in characteristic zero. -/
theorem binary_wronskian_ne_zero (b A : ℂ[X])
    (hA : 0 < A.natDegree) (hcop : IsCoprime b A) :
    b.derivative * A - b * A.derivative ≠ 0 := by
  intro hz
  have heq : b.derivative * A = b * A.derivative := sub_eq_zero.mp hz
  have hdiv : A ∣ A.derivative := hcop.symm.dvd_of_dvd_mul_left (by
    rw [← heq]
    exact dvd_mul_left A b.derivative)
  have hderiv : A.derivative ≠ 0 := derivative_ne_zero.mpr (by omega)
  have hle := natDegree_le_of_dvd hdiv hderiv
  have hlt := natDegree_derivative_lt (p := A) (by omega)
  omega

/-- Some nonzero scalar gives a separable member of the actual pencil.
No abstract genericity or critical-value hypothesis is supplied. -/
theorem binary_pencil_separable (b A : ℂ[X])
    (hA : 0 < A.natDegree) (hcop : IsCoprime b A) :
    ∃ c : ℂ, c ≠ 0 ∧ (b + C c * A).Separable := by
  classical
  let W := b.derivative * A - b * A.derivative
  have hW : W ≠ 0 := binary_wronskian_ne_zero b A hA hcop
  let bad : Finset ℂ := W.roots.toFinset.image (fun α => -b.eval α / A.eval α)
  obtain ⟨c, hc⟩ := (insert 0 bad).exists_notMem
  have hc0 : c ≠ 0 := by
    intro heq
    exact hc (by simp [heq])
  have hcbad : c ∉ bad := fun h => hc (Finset.mem_insert_of_mem h)
  refine ⟨c, hc0, ?_⟩
  let p := b + C c * A
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ p p.derivative).mpr
  intro α
  by_cases hp : p.eval α ≠ 0
  · left
    simpa using hp
  · right
    have hp0 : p.eval α = 0 := not_ne_iff.mp hp
    have hAα : A.eval α ≠ 0 := by
      intro hz
      have hbα : b.eval α = 0 := by simpa [p, hz] using hp0
      have h := Polynomial.aeval_ne_zero_of_isCoprime hcop α
      simp [hbα, hz] at h
    have hderiv : p.derivative.eval α ≠ 0 := by
      intro hdp
      have hroot : b.eval α + c * A.eval α = 0 := by simpa [p] using hp0
      have hdroot : b.derivative.eval α + c * A.derivative.eval α = 0 := by
        simpa [p] using hdp
      have hWα : W.eval α = 0 := by
        simp only [W, eval_sub, eval_mul]
        linear_combination A.eval α * hdroot - A.derivative.eval α * hroot
      have hmem : α ∈ W.roots.toFinset := by
        rw [Multiset.mem_toFinset, mem_roots hW]
        exact hWα
      have hparam : -b.eval α / A.eval α = c := by
        apply (div_eq_iff hAα).mpr
        linear_combination -hroot
      exact hcbad (Finset.mem_image.mpr ⟨α, hmem, hparam⟩)
    simpa using hderiv

/-- A monic degree-d polynomial and a coprime lower-degree perturbation
have an actual monic separable member with the same degree. -/
theorem binary_monic_separable_pencil (b A : ℂ[X])
    (hA : A.Monic) (hApos : 0 < A.natDegree)
    (hb : b.natDegree < A.natDegree) (hcop : IsCoprime b A) :
    ∃ c : ℂ, c ≠ 0 ∧ (A + C c * b).Monic ∧
      (A + C c * b).natDegree = A.natDegree ∧ (A + C c * b).Separable := by
  obtain ⟨a, ha, hsep⟩ := binary_pencil_separable b A hApos hcop
  have hsmall : (C a⁻¹ * b).degree < A.degree := by
    exact degree_lt_degree ((natDegree_C_mul_le _ _).trans_lt hb)
  refine ⟨a⁻¹, inv_ne_zero ha, hA.add_of_left hsmall, ?_, ?_⟩
  · exact natDegree_add_eq_left_of_degree_lt hsmall
  · have heq : A + C a⁻¹ * b = C a⁻¹ * (b + C a * A) := by
      rw [mul_add, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul]
      exact add_comm _ _
    rw [heq]
    exact Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero ha))) hsep

#assert_trust kernel binary_wronskian_ne_zero
#assert_trust kernel binary_pencil_separable
#assert_trust kernel binary_monic_separable_pencil
#print axioms binary_monic_separable_pencil

end
end NLA.Proofs.TR14
