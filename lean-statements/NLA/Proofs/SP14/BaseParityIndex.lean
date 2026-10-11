import NLA.Statements.SP14

/-!
The all-order parity reindexing used for the actual odd Toeplitz sections
of the SP-14 base symbol. This is finite index algebra only.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- Even positions first, then odd positions, in an order `2m+1` section. -/
def baseParityMap (m : ℕ) : Fin (m + 1) ⊕ Fin m → Fin (2 * m + 1) :=
  Sum.elim
    (fun i => ⟨2 * i.val, by omega⟩)
    (fun j => ⟨2 * j.val + 1, by omega⟩)

private theorem baseParityMap_injective (m : ℕ) : Function.Injective (baseParityMap m) := by
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      have hv := congrArg Fin.val h
      have hij : i.val = j.val := by
        simp [baseParityMap] at hv
        omega
      exact congrArg Sum.inl (Fin.ext hij)
    | inr j =>
      have hv := congrArg Fin.val h
      simp [baseParityMap] at hv
      omega
  | inr i =>
    cases y with
    | inl j =>
      have hv := congrArg Fin.val h
      simp [baseParityMap] at hv
      omega
    | inr j =>
      have hv := congrArg Fin.val h
      have hij : i.val = j.val := by
        simp [baseParityMap] at hv
        omega
      exact congrArg Sum.inr (Fin.ext hij)

/-- A genuine equivalence, so reindexing preserves characteristic
polynomials and algebraic multiplicities. -/
noncomputable def baseParityEquiv (m : ℕ) : (Fin (m + 1) ⊕ Fin m) ≃ Fin (2 * m + 1) :=
  Equiv.ofBijective (baseParityMap m) <|
    (Fintype.bijective_iff_injective_and_card (baseParityMap m)).2
      ⟨baseParityMap_injective m, by simp [Fintype.card_sum]; omega⟩

@[simp] theorem baseParityEquiv_inl (m : ℕ) (i : Fin (m + 1)) :
    (baseParityEquiv m (Sum.inl i)).val = 2 * i.val := rfl

@[simp] theorem baseParityEquiv_inr (m : ℕ) (j : Fin m) :
    (baseParityEquiv m (Sum.inr j)).val = 2 * j.val + 1 := rfl

#assert_trust kernel baseParityEquiv
#print axioms baseParityEquiv

end NLA.Proofs.SP14
