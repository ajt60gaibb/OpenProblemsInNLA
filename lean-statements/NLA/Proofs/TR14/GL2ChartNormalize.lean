import NLA.Proofs.TR14.GL2Dehomogenize
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
Normalize an arbitrary nonzero least homogeneous apolar form by an actual
invertible chart change. The output has a monic affine polynomial of exact
degree and retains all lower zero apolar kernels. No tensor-width or Target
claim is made.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

noncomputable section

/-- The selected least apolar form may have a root at infinity and need not
be unique. A finite chart makes its affine polynomial monic of exact degree,
while inverse-dual transport preserves the moment vector and every lower
zero apolar kernel. -/
theorem normalize_chosen_minimal_apolar {D r₀ : ℕ}
    (h : Fin (D + 1) → ℂ) (_hD : 1 ≤ D) (hh : h ≠ 0)
    (hrD : r₀ ≤ D) (hrLo : 1 ≤ r₀) (_hrHi : r₀ ≤ D / 2 + 1)
    (g : Fin (r₀ + 1) → ℂ) (hg : g ≠ 0)
    (hAp : IsApolar h r₀ hrD g)
    (hmin : ∀ k : ℕ, ∀ hk : k ≤ D, k < r₀ →
      ∀ c : Fin (k + 1) → ℂ, IsApolar h k hk c → c = 0) :
    ∃ z : ℂ, ∃ b : Fin (r₀ + 1) → ℂ, ∃ q : Polynomial ℂ,
      let h' := transformedMoments z h
      h' ≠ 0 ∧ b ≠ 0 ∧ IsApolar h' r₀ hrD b ∧
      b ⟨r₀, by omega⟩ = 1 ∧ q.Monic ∧ q.natDegree = r₀ ∧
      (∀ i : Fin (r₀ + 1), q.coeff i.val = b i) ∧
      (∀ k : ℕ, ∀ hk : k ≤ D, k < r₀ →
        ∀ c : Fin (k + 1) → ℂ, IsApolar h' k hk c → c = 0) := by
  obtain ⟨z, hz⟩ := exists_chart_last_nonzero r₀ g hg
  let gz := transportedApolarVector z r₀ g
  let a : ℂ := gz ⟨r₀, by omega⟩
  let b : Fin (r₀ + 1) → ℂ := fun i => a⁻¹ * gz i
  let q : Polynomial ℂ := dehomogenize r₀ b
  have ha : a ≠ 0 := hz
  have hbTop : b ⟨r₀, by omega⟩ = 1 := by
    change a⁻¹ * a = 1
    exact inv_mul_cancel₀ ha
  have hbNonzero : b ≠ 0 := by
    intro hbz
    have hv := congrFun hbz (⟨r₀, by omega⟩ : Fin (r₀ + 1))
    rw [hbTop] at hv
    exact one_ne_zero hv
  have hbEq : b = a⁻¹ • gz := by
    funext i
    rfl
  have hApGz : IsApolar (transformedMoments z h) r₀ hrD gz :=
    (apolar_iff_chart_apolar z hrD h g).mp hAp
  have hApB : IsApolar (transformedMoments z h) r₀ hrD b := by
    change apolarMap (transformedMoments z h) r₀ hrD b = 0
    rw [hbEq, map_smul]
    change apolarMap (transformedMoments z h) r₀ hrD gz = 0 at hApGz
    rw [hApGz, smul_zero]
  have hqCoeff (i : Fin (r₀ + 1)) : q.coeff i.val = b i :=
    dehomogenize_coeff r₀ b i
  have hqTop : q.coeff r₀ = 1 := by
    simpa only using (hqCoeff ⟨r₀, by omega⟩).trans hbTop
  have hqLe : q.natDegree ≤ r₀ := by
    have hlt : q.natDegree < r₀ + 1 :=
      Polynomial.ofFn_natDegree_lt (by omega) b
    omega
  have hqDegree : q.natDegree = r₀ :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hqLe (by
      rw [hqTop]
      exact one_ne_zero)
  have hqMonic : q.Monic :=
    Polynomial.monic_of_natDegree_le_of_coeff_eq_one r₀ hqLe hqTop
  have hhTrans : transformedMoments z h ≠ 0 := by
    intro hz0
    exact hh ((transformedMoments_eq_zero_iff z h).mp hz0)
  have hminTrans : ∀ k : ℕ, ∀ hk : k ≤ D, k < r₀ →
      ∀ c : Fin (k + 1) → ℂ,
        IsApolar (transformedMoments z h) k hk c → c = 0 := by
    intro k hk hlt c hc
    by_contra hc0
    obtain ⟨v, hv0, hvAp⟩ :=
      (chart_nonzero_apolar_degree_iff z hk h).mpr ⟨c, hc0, hc⟩
    exact hv0 (hmin k hk hlt v hvAp)
  exact ⟨z, b, q, hhTrans, hbNonzero, hApB, hbTop,
    hqMonic, hqDegree, hqCoeff, hminTrans⟩

#assert_trust kernel normalize_chosen_minimal_apolar
#print axioms normalize_chosen_minimal_apolar

end
end NLA.Proofs.TR14
