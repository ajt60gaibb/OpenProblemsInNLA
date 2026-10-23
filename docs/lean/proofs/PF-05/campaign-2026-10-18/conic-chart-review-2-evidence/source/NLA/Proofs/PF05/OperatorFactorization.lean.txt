import NLA.Proofs.PF05.CoordinateActions

/-! Exact preservation of trace products by inverse coordinate actions. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Matrix
namespace NLA.Proofs.PF05
namespace CoordinateActions
open NLA.Statements.PF05

theorem trace_eq_coordinate_dot (A B : M2) (hA : Symmetric A) (hB : Symmetric B) :
    Matrix.trace (A*B)=leftVector A ⬝ᵥ rightVector B := by
  rw [trace_mul_symmetric_coordinates A B hA hB]
  simp [leftVector,rightVector,dotProduct,Fin.sum_univ_three]
  ring

/-- The weighted coordinate action preserves the original trace pairing when
its two actual operators multiply to the identity. -/
theorem trace_primal_dual (C D : M3) (hCD : C*D=1)
    (A B : M2) (hA : Symmetric A) (hB : Symmetric B) :
    Matrix.trace (primal C A * dual D B)=Matrix.trace (A*B) := by
  rw [trace_eq_coordinate_dot _ _ (primal_symmetric _ _) (dual_symmetric _ _),
    leftVector_primal,rightVector_dual,Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul,hCD,Matrix.vecMul_one,← trace_eq_coordinate_dot A B hA hB]

/-- The only PSD hypotheses are on the actual transformed factors. Arbitrary
coordinate operators are not asserted to preserve the entire PSD cone. -/
theorem factorization_primal_dual {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (hfact : Factorization M A B) (C D : M3) (hCD : C*D=1)
    (hA : ∀ i, PositiveSemidefinite (primal C (A i)))
    (hB : ∀ j, PositiveSemidefinite (dual D (B j))) :
    Factorization M (fun i => primal C (A i)) (fun j => dual D (B j)) := by
  refine ⟨hA,hB,?_⟩
  intro i j
  rw [trace_primal_dual C D hCD (A i) (B j) (hfact.1 i).1 (hfact.2.1 j).1]
  exact hfact.2.2 i j

#assert_trust kernel trace_primal_dual
#assert_trust kernel factorization_primal_dual
#print axioms factorization_primal_dual
end CoordinateActions
end NLA.Proofs.PF05
