import NLA.Proofs.TR14.GL2MobiusEval

/-!
The finite nonzero-root coordinate correspondence for the audited TR-14 binary
chart. The two points at infinity and root multiplicities are separate gates.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial
noncomputable section

/-- At a nonzero transformed affine coordinate, the chart has a root exactly
when the original dehomogenization has a root at `z + t⁻¹`. -/
theorem chart_root_eval_zero_iff
    (z : ℂ) (d : ℕ) (g : Fin (d + 1) → ℂ)
    (t : ℂ) (ht : t ≠ 0) :
    (dehomogenize d (transportedApolarVector z d g)).eval t = 0 ↔
      (dehomogenize d g).eval (z + t⁻¹) = 0 := by
  rw [chart_dehomogenize_eval_nonzero z d g t ht]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hpow | hroot
    · exact False.elim ((pow_ne_zero d ht) hpow)
    · exact hroot
  · intro h
    rw [h, mul_zero]

/-- Exact finite-root bijection for the nonzero affine coordinates of the
audited chart. The forward coordinate is `(α-z)⁻¹`, and the inverse is
`z+t⁻¹`. -/
noncomputable def chart_nonzero_finite_roots_equiv
    (z : ℂ) (d : ℕ) (g : Fin (d + 1) → ℂ) :
    { α : ℂ // α ≠ z ∧ (dehomogenize d g).eval α = 0 } ≃
      { t : ℂ // t ≠ 0 ∧
        (dehomogenize d (transportedApolarVector z d g)).eval t = 0 } where
  toFun α := by
    have hsub : α.val - z ≠ 0 := sub_ne_zero.mpr α.property.1
    have ht : (α.val - z)⁻¹ ≠ 0 := inv_ne_zero hsub
    have hcoord : z + ((α.val - z)⁻¹)⁻¹ = α.val := by
      rw [inv_inv]
      ring
    exact ⟨(α.val - z)⁻¹, ht,
      (chart_root_eval_zero_iff z d g _ ht).mpr (by
        rw [hcoord]
        exact α.property.2)⟩
  invFun t := by
    have hα : z + t.val⁻¹ ≠ z := by
      intro heq
      have hinv : t.val⁻¹ = 0 := by
        calc
          t.val⁻¹ = (z + t.val⁻¹) - z := by ring
          _ = z - z := by rw [heq]
          _ = 0 := sub_self z
      exact (inv_ne_zero t.property.1) hinv
    exact ⟨z + t.val⁻¹, hα,
      (chart_root_eval_zero_iff z d g t.val t.property.1).mp t.property.2⟩
  left_inv α := by
    apply Subtype.ext
    change z + (((α.val - z)⁻¹)⁻¹) = α.val
    rw [inv_inv]
    ring
  right_inv t := by
    apply Subtype.ext
    change ((z + t.val⁻¹) - z)⁻¹ = t.val
    have hcoord : (z + t.val⁻¹) - z = t.val⁻¹ := by ring
    rw [hcoord, inv_inv]

theorem chart_nonzero_finite_roots_equiv_apply
    (z : ℂ) (d : ℕ) (g : Fin (d + 1) → ℂ)
    (α : { α : ℂ // α ≠ z ∧ (dehomogenize d g).eval α = 0 }) :
    (chart_nonzero_finite_roots_equiv z d g α).val = (α.val - z)⁻¹ := rfl

theorem chart_nonzero_finite_roots_equiv_symm_apply
    (z : ℂ) (d : ℕ) (g : Fin (d + 1) → ℂ)
    (t : { t : ℂ // t ≠ 0 ∧
      (dehomogenize d (transportedApolarVector z d g)).eval t = 0 }) :
    ((chart_nonzero_finite_roots_equiv z d g).symm t).val = z + t.val⁻¹ := rfl

#assert_trust kernel chart_root_eval_zero_iff
#assert_trust kernel chart_nonzero_finite_roots_equiv
#assert_trust kernel chart_nonzero_finite_roots_equiv_apply
#assert_trust kernel chart_nonzero_finite_roots_equiv_symm_apply
#print axioms chart_nonzero_finite_roots_equiv_symm_apply

end
end NLA.Proofs.TR14
