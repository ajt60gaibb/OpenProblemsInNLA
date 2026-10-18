import NLA.Proofs.PF05.ZeroRestrictionTransfer

/-! The actual positive nonzero core when no nonzero orthogonal pair exists. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
namespace ZeroRestriction
open NLA.Statements.PF05

/-- Ordinary rank three rules out a size-one PSD factorization. -/
theorem psdRankTwo_of_rank_three_factorization {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (hfact : Factorization M A B) (hrank : M.rank=3) : PSDRankTwo M := by
  refine ⟨⟨A,B,hfact⟩,?_⟩
  rintro ⟨A1,B1,h1⟩
  have heq : M=Matrix.vecMulVec (fun i => A1 i 0 0) (fun j => B1 j 0 0) := by
    ext i j
    rw [h1.2.2 i j]
    simp [Matrix.trace,Matrix.mul_apply,Matrix.vecMulVec_apply]
  have hle : M.rank≤1 := by
    rw [heq]
    exact Matrix.rank_vecMulVec_le _ _
  rw [hrank] at hle
  omega

/-- Once every actual zero factor is deleted, the absence of a nonzero zero
pair forces every remaining matrix entry to be strictly positive. -/
theorem reduced_positive_of_no_nonzero_zero_pair {p q r s : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (cA : Selection p r A) (cB : Selection q s B)
    (hM : ∀ i j, 0≤M i j)
    (hno : ¬∃ i j, A i≠0 ∧ B j≠0 ∧ M i j=0) :
    ∀ a b, 0<reducedMatrix M cA cB a b := by
  intro a b
  have hm := hM (cA.pick a) (cB.pick b)
  change 0<M (cA.pick a) (cB.pick b)
  by_contra! hn
  exact hno ⟨cA.pick a,cB.pick b,cA.nonzero a,cB.nonzero b,le_antisymm hn hm⟩

/-- Construct the actual smaller positive instance, preserving both full
frozen properties and all rank hypotheses, rather than assuming a positive
core or a transfer oracle. The original zero positions are restored by extend. -/
theorem exists_positive_core_of_no_nonzero_zero_pair {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (hM : ∀ i j, 0≤M i j) (hfact : Factorization M A B) (hrank : M.rank=3)
    (hno : ¬∃ i j, A i≠0 ∧ B j≠0 ∧ M i j=0) :
    ∃ r s : ℕ, ∃ cA : Selection p r A, ∃ cB : Selection q s B,
      Factorization (reducedMatrix M cA cB) (reduced cA) (reduced cB) ∧
      (reducedMatrix M cA cB).rank=3 ∧
      PSDRankTwo (reducedMatrix M cA cB) ∧
      (∀ a b, 0<reducedMatrix M cA cB a b) ∧
      (InfinitesimallyRigid A B ↔ InfinitesimallyRigid (reduced cA) (reduced cB)) ∧
      (UniqueUpToCongruence M A B ↔
        UniqueUpToCongruence (reducedMatrix M cA cB) (reduced cA) (reduced cB)) := by
  obtain ⟨r,⟨cA⟩⟩ := exists_selection A
  obtain ⟨s,⟨cB⟩⟩ := exists_selection B
  have hred := factorization_restrict M A B cA cB hfact
  have hr := reduced_rank_three M A B cA cB hfact hrank
  exact ⟨r,s,cA,cB,hred,hr,
    psdRankTwo_of_rank_three_factorization _ _ _ hred hr,
    reduced_positive_of_no_nonzero_zero_pair M A B cA cB hM hno,
    rigid_iff_reduced M A B cA cB hfact hrank,
    unique_iff_reduced M A B cA cB hfact hrank⟩

#assert_trust kernel psdRankTwo_of_rank_three_factorization
#assert_trust kernel reduced_positive_of_no_nonzero_zero_pair
#assert_trust kernel exists_positive_core_of_no_nonzero_zero_pair
#print axioms exists_positive_core_of_no_nonzero_zero_pair
end ZeroRestriction
end NLA.Proofs.PF05
