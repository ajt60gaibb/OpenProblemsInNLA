import NLA.PF03.CubicFiniteArithmetic

/-!
Exact rational cubic certificates for the literal seven-column seed. The Gram
calculation checks only28 upper-triangular entries, partitioned by row; symmetry
supplies the rest. This source contains no new real-number assumption.
Original mathematics and data: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Matrix
noncomputable section
namespace NLA.PF03

def seedCubicGram (r s : Fin 7) : Cubic :=
  ∑ i : Fin 7, cubicMul (RawData.orthogonalMatrix r i) (RawData.orthogonalMatrix s i)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem seed_cache_coordinates : ∀ r i : Fin 7, ∀ k : Fin 3,
    RawData.orthogonalMatrix r i k = RawData.coefficientMatrices k r i := by
  intro r i k
  fin_cases r <;> fin_cases i <;> fin_cases k <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem seed_cubic_gram_row0 : ∀ s : Fin 7, (0 : Fin 7) ≤ s → ∀ k : Fin 3,
    seedCubicGram 0 s k = (if (0 : Fin 7) = s then cubicOne else cubicZero) k := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem seed_cubic_gram_row1 : ∀ s : Fin 7, (1 : Fin 7) ≤ s → ∀ k : Fin 3,
    seedCubicGram 1 s k = (if (1 : Fin 7) = s then cubicOne else cubicZero) k := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem seed_cubic_gram_row2 : ∀ s : Fin 7, (2 : Fin 7) ≤ s → ∀ k : Fin 3,
    seedCubicGram 2 s k = (if (2 : Fin 7) = s then cubicOne else cubicZero) k := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem seed_cubic_gram_row3 : ∀ s : Fin 7, (3 : Fin 7) ≤ s → ∀ k : Fin 3,
    seedCubicGram 3 s k = (if (3 : Fin 7) = s then cubicOne else cubicZero) k := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem seed_cubic_gram_row4 : ∀ s : Fin 7, (4 : Fin 7) ≤ s → ∀ k : Fin 3,
    seedCubicGram 4 s k = (if (4 : Fin 7) = s then cubicOne else cubicZero) k := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem seed_cubic_gram_row5 : ∀ s : Fin 7, (5 : Fin 7) ≤ s → ∀ k : Fin 3,
    seedCubicGram 5 s k = (if (5 : Fin 7) = s then cubicOne else cubicZero) k := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem seed_cubic_gram_row6 : ∀ s : Fin 7, (6 : Fin 7) ≤ s → ∀ k : Fin 3,
    seedCubicGram 6 s k = (if (6 : Fin 7) = s then cubicOne else cubicZero) k := by
  decide +kernel

private theorem seed_cubic_gram_upper (r s : Fin 7) (hrs : r ≤ s) :
    seedCubicGram r s = if r = s then cubicOne else cubicZero := by
  funext k
  fin_cases r
  · exact seed_cubic_gram_row0 s hrs k
  · exact seed_cubic_gram_row1 s hrs k
  · exact seed_cubic_gram_row2 s hrs k
  · exact seed_cubic_gram_row3 s hrs k
  · exact seed_cubic_gram_row4 s hrs k
  · exact seed_cubic_gram_row5 s hrs k
  · exact seed_cubic_gram_row6 s hrs k

private theorem seed_cubic_gram_symm (r s : Fin 7) :
    seedCubicGram r s = seedCubicGram s r := by
  unfold seedCubicGram
  apply Finset.sum_congr rfl
  intro i _
  exact cubicMul_comm _ _

theorem seed_cubic_gram (r s : Fin 7) :
    seedCubicGram r s = if r = s then cubicOne else cubicZero := by
  rcases le_total r s with h | h
  · exact seed_cubic_gram_upper r s h
  · rw [seed_cubic_gram_symm, seed_cubic_gram_upper s r h]
    simp only [eq_comm]

#print axioms seed_cache_coordinates
#assert_trust kernel seed_cache_coordinates
#print axioms seed_cubic_gram
#assert_trust kernel seed_cubic_gram

end NLA.PF03
