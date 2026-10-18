import NLA.Proofs.PF05.FeasibleIntegration
import NLA.Proofs.PF05.CongruenceLine

/-! Uniqueness implies the exact straight-line rigidity, with all zero patterns
and singular/repeated factors included. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Matrix
namespace NLA.Proofs.PF05
open NLA.Statements.PF05 CoordinateActions

theorem primal_scalar_operator (d : ℝ) (A : M2) (hs : Symmetric A) :
    primal (d • (1:M3)) A=d • A := by
  have hds : Symmetric (d • A) := by
    intro i j; simp [Matrix.smul_apply,hs i j]
  apply leftVector_injective_symmetric _ _ (primal_symmetric _ _) hds
  simp [Matrix.vecMul_smul]

theorem dual_scalar_operator (d : ℝ) (B : M2) (hs : Symmetric B) :
    dual (d • (1:M3)) B=d • B := by
  have hds : Symmetric (d • B) := by
    intro i j; simp [Matrix.smul_apply,hs i j]
  apply rightVector_injective_symmetric _ _ (dual_symmetric _ _) hds
  simp [Matrix.smul_mulVec]

/-- The unrestricted reverse implication of the frozen PF-05 equivalence.
There is no positive-entry, distinct-factor, nonzero-row or local-orbit premise. -/
theorem unique_implies_infinitesimallyRigid {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (hfact : Factorization M A B) (hrank : M.rank=3)
    (hunique : UniqueUpToCongruence M A B) : InfinitesimallyRigid A B := by
  intro E F hdir
  obtain ⟨T,h,hh,hE,hF,hpath⟩ := integrate_feasible_direction M A E B F hfact hrank hdir
  have hcong : ∀ t : ℝ, 0≤t → t<h →
      ∃ S : M2, S.det≠0 ∧ 1+t • T=congruenceOperator S := by
    intro t ht hth
    obtain ⟨S,hS,hA,_hB⟩ := hunique _ _ (hpath t ht hth).2
    refine ⟨S,hS,?_⟩
    apply operator_eq_congruence_of_factors M A B hfact hrank (1+t • T) S
    intro i
    rw [primal_one_add_smul T t (A i) (hfact.1 i).1,← hE i]
    exact hA i
  obtain ⟨d,hT⟩ := congruence_line_scalar T h hh hcong
  refine ⟨d,?_,?_⟩
  · intro i
    rw [hE i,hT,primal_scalar_operator d (A i) (hfact.1 i).1]
  · intro j
    rw [hF j,hT,dual_scalar_operator d (B j) (hfact.2.1 j).1]
    simp [neg_smul]

#assert_trust kernel primal_scalar_operator
#assert_trust kernel dual_scalar_operator
#assert_trust kernel unique_implies_infinitesimallyRigid
#print axioms unique_implies_infinitesimallyRigid
end NLA.Proofs.PF05
