import NLA.Proofs.TR14.MomentQuotientModePairing
import Mathlib.Algebra.Algebra.Operations

/-! Actual quotient mode spaces and their product span. Every root power through
`c*q` is a product of `c` available mode monomials. Once these include the monic
quotient's power basis, the product subspace is the whole quotient algebra.
No ordinary decomposition or lower bound is assumed here. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open scoped BigOperators
noncomputable section

/-- The actual quotient-mode sum, bundled as a complex linear map. -/
def quotientModeLinear (g : Polynomial ℂ) (q : ℕ) :
    (Fin (q + 1) → ℂ) →ₗ[ℂ] AdjoinRoot g where
  toFun := quotientMode g q
  map_add' v w := by
    simp [quotientMode, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp [quotientMode, Pi.smul_apply, smul_smul, Finset.smul_sum]

@[simp] theorem quotientModeLinear_apply (g : Polynomial ℂ) (q : ℕ)
    (v : Fin (q + 1) → ℂ) : quotientModeLinear g q v = quotientMode g q v := rfl

/-- Each available monomial is an actual image of a coordinate mode vector. -/
theorem quotient_root_power_mem_mode_range (g : Polynomial ℂ) (q : ℕ)
    (i : Fin (q + 1)) :
    (AdjoinRoot.root g) ^ i.val ∈ LinearMap.range (quotientModeLinear g q) := by
  classical
  refine ⟨Pi.single i 1, ?_⟩
  change quotientMode g q (Pi.single i 1) = _
  simp [quotientMode, Pi.single_apply]

/-- Products of `c` mode spaces contain every root power through degree `c*q`,
including `c=0` and `q=0`. The submodule power zero is the scalar subspace. -/
theorem quotient_root_power_mem_mode_range_pow (g : Polynomial ℂ) (q c j : ℕ)
    (hj : j ≤ c * q) :
    (AdjoinRoot.root g) ^ j ∈ (LinearMap.range (quotientModeLinear g q)) ^ c := by
  induction c generalizing j with
  | zero =>
      have hj0 : j = 0 := by omega
      subst j
      rw [Submodule.pow_zero, pow_zero]
      exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  | succ c ih =>
      let a := min j q
      have ha : a < q + 1 := by dsimp [a]; omega
      have hrest : j - a ≤ c * q := by
        dsimp [a]
        simp only [Nat.succ_mul] at hj
        omega
      have hsum : j - a + a = j := by dsimp [a]; omega
      rw [Submodule.pow_succ]
      have hm := Submodule.mul_mem_mul (ih (j - a) hrest)
        (quotient_root_power_mem_mode_range g q ⟨a, ha⟩)
      simpa only [← pow_add, hsum] using hm

/-- The product of the actual quotient-mode ranges is the full algebra when
its monomials cover the monic quotient power basis. -/
theorem quotient_mode_range_pow_eq_top (g : Polynomial ℂ) (hg : g.Monic)
    (q c : ℕ) (hdegree : g.natDegree ≤ c * q + 1) :
    (LinearMap.range (quotientModeLinear g q)) ^ c = ⊤ := by
  apply top_unique
  rw [← (AdjoinRoot.powerBasis' hg).basis.span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  rw [(AdjoinRoot.powerBasis' hg).basis_eq_pow]
  apply quotient_root_power_mem_mode_range_pow
  have hi : i.val < g.natDegree := i.isLt
  omega

/-- The rank-minus-one convention used by the all-but-one mode product. -/
theorem quotient_mode_range_pow_eq_top_of_pred_le (g : Polynomial ℂ)
    (hg : g.Monic) (hr : 1 ≤ g.natDegree) (q c : ℕ)
    (hdegree : g.natDegree - 1 ≤ c * q) :
    (LinearMap.range (quotientModeLinear g q)) ^ c = ⊤ := by
  apply quotient_mode_range_pow_eq_top g hg q c
  omega

#assert_trust kernel quotientModeLinear
#assert_trust kernel quotientModeLinear_apply
#assert_trust kernel quotient_root_power_mem_mode_range
#assert_trust kernel quotient_root_power_mem_mode_range_pow
#assert_trust kernel quotient_mode_range_pow_eq_top
#assert_trust kernel quotient_mode_range_pow_eq_top_of_pred_le
#print axioms quotient_mode_range_pow_eq_top

end
end NLA.Proofs.TR14
