import NLA.Proofs.TR04.MachineSVDMemory
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace SVDMemoryAuthorConsumer
open NLA.Computation.SVDMachine NLA.Proofs.TR04
theorem literal_output_readback {m l : ℕ} (old : ℕ → ℝ) (ub sb vb : ℕ)
    (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) (h : OutputBlocksDisjoint m l ub sb vb) :
    readMatrix (writeSVD old ub sb vb U sigma V) m m ub = U ∧
    (∀ k : Fin (min m l), writeSVD old ub sb vb U sigma V (sb + k.val) = sigma k) ∧
    readMatrix (writeSVD old ub sb vb U sigma V) l l vb = V ∧
    (∀ address : ℕ,
      ¬ (ub ≤ address ∧ address < ub + m * m) →
      ¬ (sb ≤ address ∧ address < sb + min m l) →
      ¬ (vb ≤ address ∧ address < vb + l * l) →
      writeSVD old ub sb vb U sigma V address = old address) := by
  exact ⟨readMatrix_writeSVD_u old ub sb vb U sigma V,
    writeSVD_sigma_entry old ub sb vb U sigma V h,
    readMatrix_writeSVD_v old ub sb vb U sigma V h,
    writeSVD_outside old ub sb vb U sigma V⟩
theorem literal_row_major {m l : ℕ} (A : Matrix (Fin m) (Fin l) ℝ)
    (i : Fin m) (j : Fin l) : matrixCell A (i.val * l + j.val) = A i j :=
  matrixCell_entry A i j
#assert_trust kernel literal_output_readback
#assert_trust kernel literal_row_major
#print axioms literal_output_readback
#print axioms literal_row_major
end SVDMemoryAuthorConsumer
#assert_trust kernel NLA.Proofs.TR04.matrix_offset_lt
#print axioms NLA.Proofs.TR04.matrix_offset_lt
#assert_trust kernel NLA.Proofs.TR04.matrixCell_entry
#print axioms NLA.Proofs.TR04.matrixCell_entry
#assert_trust kernel NLA.Proofs.TR04.disjointBlocks_not_mem_right
#print axioms NLA.Proofs.TR04.disjointBlocks_not_mem_right
#assert_trust kernel NLA.Proofs.TR04.disjointBlocks_not_mem_left
#print axioms NLA.Proofs.TR04.disjointBlocks_not_mem_left
#assert_trust kernel NLA.Proofs.TR04.writeSVD_u_entry
#print axioms NLA.Proofs.TR04.writeSVD_u_entry
#assert_trust kernel NLA.Proofs.TR04.readMatrix_writeSVD_u
#print axioms NLA.Proofs.TR04.readMatrix_writeSVD_u
#assert_trust kernel NLA.Proofs.TR04.writeSVD_sigma_entry
#print axioms NLA.Proofs.TR04.writeSVD_sigma_entry
#assert_trust kernel NLA.Proofs.TR04.writeSVD_v_entry
#print axioms NLA.Proofs.TR04.writeSVD_v_entry
#assert_trust kernel NLA.Proofs.TR04.readMatrix_writeSVD_v
#print axioms NLA.Proofs.TR04.readMatrix_writeSVD_v
#assert_trust kernel NLA.Proofs.TR04.writeSVD_outside
#print axioms NLA.Proofs.TR04.writeSVD_outside
