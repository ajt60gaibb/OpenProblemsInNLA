import NLA.Statements.TR14

/-!
Elementary width semantics for the frozen TR-14 target. These lemmas do not
prove the hard ordinary-to-symmetric direction for nonzero Hankel tensors.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.TR14

open NLA.Statements.TR14

/-- Every symmetric rank-one summand is an ordinary rank-one summand, with
its scalar absorbed into a single mode. The proof covers empty width. -/
theorem symmetricWidth_to_ordinaryWidth {m n r : ℕ}
    (hm : 0 < m) {H : (Fin m → Fin n) → ℂ}
    (h : SymmetricWidth H r) : OrdinaryWidth H r := by
  rcases h with ⟨c, v, hv⟩
  let k0 : Fin m := ⟨0, hm⟩
  refine ⟨fun j k x => (if k = k0 then c j else 1) * v j x, ?_⟩
  intro i
  rw [hv i]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.prod_mul_distrib]
  have hscalar : (∏ k : Fin m, if k = k0 then c j else 1) = c j := by
    exact Fintype.prod_ite_eq' k0 (fun _ : Fin m => c j)
  rw [hscalar]

/-- At width zero, the frozen ordinary decomposition equation says exactly
that every coordinate of the tensor is zero. -/
theorem ordinaryWidth_zero_iff {m n : ℕ} (H : (Fin m → Fin n) → ℂ) :
    OrdinaryWidth H 0 ↔ ∀ i, H i = 0 := by
  constructor
  · rintro ⟨u, hu⟩ i
    simpa using hu i
  · intro h
    refine ⟨fun j => Fin.elim0 j, ?_⟩
    intro i
    simpa using h i

/-- The frozen symmetric width-zero equation has the same empty-sum meaning. -/
theorem symmetricWidth_zero_iff {m n : ℕ} (H : (Fin m → Fin n) → ℂ) :
    SymmetricWidth H 0 ↔ ∀ i, H i = 0 := by
  constructor
  · rintro ⟨c, v, hv⟩ i
    simpa using hv i
  · intro h
    refine ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, ?_⟩
    intro i
    simpa using h i

#assert_trust kernel symmetricWidth_to_ordinaryWidth
#assert_trust kernel ordinaryWidth_zero_iff
#assert_trust kernel symmetricWidth_zero_iff
#print axioms symmetricWidth_to_ordinaryWidth

end NLA.Proofs.TR14
