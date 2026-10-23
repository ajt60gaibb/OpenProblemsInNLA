import NLA.Proofs.TR14.GraphQuotientContext

/-! The exact take/drop first-factor context for the actual normalized
ordinary graph list. This connects finite quotient mode products to the
list-indexed contextual inequality without restricting mode dimension. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.TR14
noncomputable section

/-- Independently unit-scaled products, including lists with repeated labels. -/
theorem unitScale_list_prod {K B ι : Type*} [Field K] [CommRing B] [Algebra K B]
    (L : List ι) (u : ι → Bˣ) (U : ι → Submodule K B) :
    (L.map (fun i => unitScale (u i) (U i))).prod =
      unitScale (L.map u).prod (L.map U).prod := by
  induction L with
  | nil => simp
  | cons i L ih => simp only [List.map_cons, List.prod_cons, ih, unitScale_mul]

/-- The actual first projection for any list of unnormalized mode graphs. -/
theorem ordinaryGraph_listproduct_fst {m q r : ℕ} (g : Polynomial ℂ)
    (u : Fin r → Fin m → Fin (q + 1) → ℂ) (L : List (Fin m)) :
    (L.map (ordinaryGraphSpace (quotientModeLinear g q) u)).prod.map
        (AlgHom.fst ℂ (AdjoinRoot g) (Fin r → ℂ)).toLinearMap =
      (LinearMap.range (quotientModeLinear g q)) ^ L.length := by
  induction L with
  | nil => simp only [List.map_nil, List.prod_nil, List.length_nil, pow_zero, Submodule.map_one]
  | cons i L ih =>
    simp only [List.map_cons, List.prod_cons, Submodule.map_mul, ordinaryGraphSpace_fst,
      ih, List.length_cons, pow_succ]
    exact mul_comm _ _

/-- The normalized first projection is still the entire actual quotient
when the listed modes cover its power basis. -/
theorem normalizedGraph_listproduct_fst_top {m q r : ℕ}
    (g : Polynomial ℂ) (hg : g.Monic)
    (u : Fin r → Fin m → Fin (q + 1) → ℂ)
    (a : Fin m → (AdjoinRoot g × (Fin r → ℂ))ˣ)
    (L : List (Fin m)) (hdegree : g.natDegree ≤ L.length * q + 1) :
    (L.map (normalizedGraphSpace (quotientModeLinear g q) u a)).prod.map
        (AlgHom.fst ℂ (AdjoinRoot g) (Fin r → ℂ)).toLinearMap = ⊤ := by
  change (L.map (fun k => unitScale (a k)⁻¹
    (ordinaryGraphSpace (quotientModeLinear g q) u k))).prod.map
      (AlgHom.fst ℂ (AdjoinRoot g) (Fin r → ℂ)).toLinearMap = ⊤
  rw [unitScale_list_prod]
  apply unitScale_map_top
  rw [ordinaryGraph_listproduct_fst, quotient_mode_range_pow_eq_top g hg q L.length hdegree]

/-- Exact list take/drop premise used by `contextual_product_list_dimension_bound`.
All ordinary mode factors and the chosen quotient chart remain unrestricted. -/
theorem normalizedGraph_list_all_but_one_projection {m q r : ℕ}
    (g : Polynomial ℂ) (hg : g.Monic) (hm : 2 ≤ m)
    (hdegree : g.natDegree ≤ m * q / 2 + 1)
    (u : Fin r → Fin m → Fin (q + 1) → ℂ)
    (a : Fin m → (AdjoinRoot g × (Fin r → ℂ))ˣ)
    (i : ℕ) (hi : i < (List.ofFn (normalizedGraphSpace (quotientModeLinear g q) u a)).length)
    (b : AdjoinRoot g) :
    ∃ x ∈ ((List.ofFn (normalizedGraphSpace (quotientModeLinear g q) u a)).take i).prod *
        ((List.ofFn (normalizedGraphSpace (quotientModeLinear g q) u a)).drop (i + 1)).prod,
      x.1 = b := by
  let indices := (List.finRange m).take i ++ (List.finRange m).drop (i + 1)
  have him : i < m := by simpa only [List.length_ofFn] using hi
  have hlen : indices.length = m - 1 := by
    simp only [indices, List.length_append, List.length_take, List.length_finRange, List.length_drop]
    rw [Nat.min_eq_left (Nat.le_of_lt him)]
    omega
  have hd : g.natDegree ≤ indices.length * q + 1 := by
    rw [hlen]
    exact middle_degree_le_all_but_one hm hdegree
  have htop := normalizedGraph_listproduct_fst_top g hg u a indices hd
  have heq : ((List.ofFn (normalizedGraphSpace (quotientModeLinear g q) u a)).take i).prod *
        ((List.ofFn (normalizedGraphSpace (quotientModeLinear g q) u a)).drop (i + 1)).prod =
      (indices.map (normalizedGraphSpace (quotientModeLinear g q) u a)).prod := by
    simp only [indices, List.map_append, List.prod_append, List.ofFn_eq_map,
      List.map_take, List.map_drop]
  have hb : b ∈ (indices.map (normalizedGraphSpace (quotientModeLinear g q) u a)).prod.map
      (AlgHom.fst ℂ (AdjoinRoot g) (Fin r → ℂ)).toLinearMap := by rw [htop]; exact Submodule.mem_top
  obtain ⟨x, hx, hxb⟩ := hb
  exact ⟨x, heq.symm ▸ hx, hxb⟩

#assert_trust kernel normalizedGraph_list_all_but_one_projection
#print axioms normalizedGraph_list_all_but_one_projection

end
end NLA.Proofs.TR14
