import NLA.Proofs.TR14.GraphNormalization
import NLA.Proofs.TR14.QuotientProductSpan

/-! Actual first-factor surjectivity for normalized quotient graph products.
The finite subset form includes every all-but-one mode product and keeps the
same monic quotient and actual ordinary factors. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.TR14
noncomputable section

/-- The actual quotient-mode map contains the constant-one polynomial. -/
theorem quotientModeLinear_one_mem_range (g : Polynomial ℂ) (q : ℕ) :
    ∃ p, quotientModeLinear g q p = 1 := by
  obtain ⟨p, hp⟩ := quotient_root_power_mem_mode_range g q ⟨0, Nat.zero_lt_succ q⟩
  exact ⟨p, by simpa only [pow_zero] using hp⟩

/-- On any actual subset of modes, the first projection of their graph
product is the corresponding power of the actual quotient-mode range. -/
theorem ordinaryGraph_subproduct_fst {m q r : ℕ} (g : Polynomial ℂ)
    (u : Fin r → Fin m → Fin (q + 1) → ℂ) (s : Finset (Fin m)) :
    (∏ k ∈ s, ordinaryGraphSpace (quotientModeLinear g q) u k).map
        (AlgHom.fst ℂ (AdjoinRoot g) (Fin r → ℂ)).toLinearMap =
      (LinearMap.range (quotientModeLinear g q)) ^ s.card := by
  let f := AlgHom.fst ℂ (AdjoinRoot g) (Fin r → ℂ)
  change (Submodule.mapHom f) (∏ k ∈ s, ordinaryGraphSpace (quotientModeLinear g q) u k) = _
  rw [map_prod]
  simp only [Submodule.mapHom_apply]
  dsimp only [f]
  simp only [ordinaryGraphSpace_fst, Finset.prod_const]

/-- Separate normalization preserves the required full projection whenever
these mode products cover the actual quotient power basis. -/
theorem normalizedGraph_subproduct_fst_top {m q r : ℕ}
    (g : Polynomial ℂ) (hg : g.Monic)
    (u : Fin r → Fin m → Fin (q + 1) → ℂ)
    (a : Fin m → (AdjoinRoot g × (Fin r → ℂ))ˣ)
    (s : Finset (Fin m)) (hdegree : g.natDegree ≤ s.card * q + 1) :
    (∏ k ∈ s, normalizedGraphSpace (quotientModeLinear g q) u a k).map
        (AlgHom.fst ℂ (AdjoinRoot g) (Fin r → ℂ)).toLinearMap = ⊤ := by
  simp only [normalizedGraphSpace]
  rw [unitScale_prod]
  apply unitScale_map_top
  rw [ordinaryGraph_subproduct_fst, quotient_mode_range_pow_eq_top g hg q s.card hdegree]

/-- The natural degree bound required for products omitting any single
mode follows from the least-apolar middle bound, without `degree≤n`. -/
theorem middle_degree_le_all_but_one {m q ρ : ℕ} (hm : 2 ≤ m)
    (hρ : ρ ≤ m * q / 2 + 1) : ρ ≤ (m - 1) * q + 1 := by
  have hq : q ≤ (m - 1) * q := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right q (show 1 ≤ m - 1 by omega)
  have heq : m * q = (m - 1) * q + q := by
    calc
      m * q = ((m - 1) + 1) * q := by congr 1; omega
      _ = (m - 1) * q + q := by rw [Nat.add_mul, Nat.one_mul]
  have hD : m * q ≤ 2 * ((m - 1) * q) := by omega
  have hhalf := Nat.div_le_div_right (c := 2) hD
  simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 2)] at hhalf
  omega

/-- The exact first-factor projection of every normalized all-but-one graph
product is the full quotient algebra, including arbitrary repeated roots. -/
theorem normalizedGraph_all_but_one_fst_top {m q r : ℕ}
    (g : Polynomial ℂ) (hg : g.Monic) (hm : 2 ≤ m)
    (hdegree : g.natDegree ≤ m * q / 2 + 1)
    (u : Fin r → Fin m → Fin (q + 1) → ℂ)
    (a : Fin m → (AdjoinRoot g × (Fin r → ℂ))ˣ) (i : Fin m) :
    (∏ k ∈ Finset.univ.erase i, normalizedGraphSpace (quotientModeLinear g q) u a k).map
        (AlgHom.fst ℂ (AdjoinRoot g) (Fin r → ℂ)).toLinearMap = ⊤ := by
  classical
  apply normalizedGraph_subproduct_fst_top g hg u a
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] using
    middle_degree_le_all_but_one hm hdegree

#assert_trust kernel normalizedGraph_subproduct_fst_top
#assert_trust kernel normalizedGraph_all_but_one_fst_top
#print axioms normalizedGraph_all_but_one_fst_top

end
end NLA.Proofs.TR14
