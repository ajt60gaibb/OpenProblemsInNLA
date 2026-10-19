import NLA.Statements.TR14

/-! Zero padding of actual finite-coordinate TR-14 width witnesses. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open NLA.Statements.TR14
open scoped BigOperators

/-- Add one zero summand to an ordinary tensor decomposition. -/
theorem ordinaryWidth_succ {m n r : ℕ}
    {H : (Fin m → Fin n) → ℂ} (hm : 0 < m) (h : OrdinaryWidth H r) :
    OrdinaryWidth H (r + 1) := by
  rcases h with ⟨u, hu⟩
  refine ⟨Fin.snoc u (fun _ _ => 0), ?_⟩
  intro i
  rw [hu i, Fin.sum_univ_castSucc]
  have hzero : (∏ _k : Fin m, (0 : ℂ)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ (⟨0, hm⟩ : Fin m)) rfl
  simp [Fin.snoc_castSucc, Fin.snoc_last, hzero]

/-- Add one zero summand to a symmetric tensor decomposition. -/
theorem symmetricWidth_succ {m n r : ℕ}
    {H : (Fin m → Fin n) → ℂ} (h : SymmetricWidth H r) :
    SymmetricWidth H (r + 1) := by
  rcases h with ⟨c, v, hv⟩
  refine ⟨Fin.snoc c 0, Fin.snoc v (fun _ => 0), ?_⟩
  intro i
  rw [hv i, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Every larger ordinary width has a zero-padded witness. -/
theorem ordinaryWidth_mono {m n r s : ℕ}
    {H : (Fin m → Fin n) → ℂ} (hm : 0 < m) (hrs : r ≤ s)
    (h : OrdinaryWidth H r) : OrdinaryWidth H s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hrs
  clear hrs
  induction k with
  | zero => simpa using h
  | succ k ih => exact ordinaryWidth_succ hm ih

/-- Every larger symmetric width has a zero-padded witness. -/
theorem symmetricWidth_mono {m n r s : ℕ}
    {H : (Fin m → Fin n) → ℂ} (hrs : r ≤ s)
    (h : SymmetricWidth H r) : SymmetricWidth H s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hrs
  clear hrs
  induction k with
  | zero => simpa using h
  | succ k ih => exact symmetricWidth_succ ih

#assert_trust kernel ordinaryWidth_mono
#assert_trust kernel symmetricWidth_mono
#print axioms symmetricWidth_mono

end NLA.Proofs.TR14
