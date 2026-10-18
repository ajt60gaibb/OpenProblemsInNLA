import NLA.Proofs.PF05.PositiveUniqueness
import NLA.Proofs.PF05.ZeroPairRigidity
import NLA.Proofs.PF05.NonzeroCore
import NLA.Proofs.PF05.UniquenessRigidity

/-! The unchanged full PF-05 equivalence. Every zero pattern, zero factor,
repeated factor and singular factor is included. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
open NLA.Statements.PF05 CoordinateActions

/-- The complete forward implication: a nonzero orthogonal pair is handled
in original coordinates; otherwise actual zero-factor deletion gives the
proved positive case, and every original zero position is restored. -/
theorem rigid_implies_unique {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (hM : ∀ i j, 0≤M i j) (hf : Factorization M A B) (hrank : M.rank=3)
    (hRigid : InfinitesimallyRigid A B) : UniqueUpToCongruence M A B := by
  by_cases hpair : ∃ i j, A i≠0 ∧ B j≠0 ∧ M i j=0
  · obtain ⟨i,j,hi,hj,hij⟩ := hpair
    exact zero_pair_rigid_implies_unique M A B hf hrank i j hi hj hij hRigid
  · obtain ⟨r,s,cA,cB,hfr,hr,_,hpos,hRiff,hUiff⟩ :=
      ZeroRestriction.exists_positive_core_of_no_nonzero_zero_pair M A B hM hf hrank hpair
    apply hUiff.mpr
    exact positive_rigid_implies_unique _ _ _ hfr hr hpos (hRiff.mp hRigid)

/-- The literal full reviewed Target, with no conditional proof premise. -/
theorem target : NLA.Statements.PF05.Target := by
  intro p q M hM hrank _hPSD A B hf
  exact ⟨rigid_implies_unique M A B hM hf hrank,
    unique_implies_infinitesimallyRigid M A B hf hrank⟩

#assert_trust kernel rigid_implies_unique
#assert_trust kernel target
#print axioms target
end NLA.Proofs.PF05
