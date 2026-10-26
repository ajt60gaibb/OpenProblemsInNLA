import NLA.Computation.SVDMachine
import LeanCert.Tactic.Verification

/-! Exact output-memory facts for the unchanged SVD instruction. Every matrix
entry is stored at its literal row-major address. Disjointness is precisely the
machine's finite half-open block condition; zero-dimensional outputs need no
extra assumptions. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

theorem matrix_offset_lt {m l : ℕ} (i : Fin m) (j : Fin l) :
    i.val * l + j.val < m * l := by
  calc
    i.val * l + j.val < i.val * l + l := Nat.add_lt_add_left j.isLt _
    _ = (i.val + 1) * l := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ m * l := Nat.mul_le_mul_right l i.isLt

theorem matrixCell_entry {m l : ℕ} (A : Matrix (Fin m) (Fin l) ℝ)
    (i : Fin m) (j : Fin l) : matrixCell A (i.val * l + j.val) = A i j := by
  have hl : 0 < l := Nat.zero_lt_of_lt j.isLt
  have hd : (i.val * l + j.val) / l = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hl, Nat.div_eq_of_lt j.isLt,
      Nat.zero_add]
  have hm : (i.val * l + j.val) % l = j.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  unfold matrixCell
  rw [dif_pos (matrix_offset_lt i j)]
  apply congrArg₂ A
  · exact Fin.ext hd
  · exact Fin.ext hm

theorem disjointBlocks_not_mem_right {a countA b countB address : ℕ}
    (h : DisjointBlocks a countA b countB)
    (ha : a ≤ address ∧ address < a + countA) :
    ¬ (b ≤ address ∧ address < b + countB) := by
  unfold DisjointBlocks at h
  rcases h with h | h | h | h <;> omega

theorem disjointBlocks_not_mem_left {a countA b countB address : ℕ}
    (h : DisjointBlocks a countA b countB)
    (hb : b ≤ address ∧ address < b + countB) :
    ¬ (a ≤ address ∧ address < a + countA) := by
  intro ha
  exact disjointBlocks_not_mem_right h ha hb

theorem writeSVD_u_entry {m l : ℕ} (memory : ℕ → ℝ)
    (uBase sigmaBase vBase : ℕ) (U : Matrix (Fin m) (Fin m) ℝ)
    (sigma : Fin (min m l) → ℝ) (V : Matrix (Fin l) (Fin l) ℝ)
    (i j : Fin m) :
    writeSVD memory uBase sigmaBase vBase U sigma V (uBase + i.val * m + j.val) =
      U i j := by
  have hi := matrix_offset_lt i j
  have hmem : uBase ≤ uBase + i.val * m + j.val ∧
      uBase + i.val * m + j.val < uBase + m * m := by omega
  have hsub : uBase + i.val * m + j.val - uBase = i.val * m + j.val := by omega
  simp only [writeSVD, if_pos hmem, hsub]
  exact matrixCell_entry U i j

theorem readMatrix_writeSVD_u {m l : ℕ} (memory : ℕ → ℝ)
    (uBase sigmaBase vBase : ℕ) (U : Matrix (Fin m) (Fin m) ℝ)
    (sigma : Fin (min m l) → ℝ) (V : Matrix (Fin l) (Fin l) ℝ) :
    readMatrix (writeSVD memory uBase sigmaBase vBase U sigma V) m m uBase = U := by
  funext i j
  exact writeSVD_u_entry memory uBase sigmaBase vBase U sigma V i j

theorem writeSVD_sigma_entry {m l : ℕ} (memory : ℕ → ℝ)
    (uBase sigmaBase vBase : ℕ) (U : Matrix (Fin m) (Fin m) ℝ)
    (sigma : Fin (min m l) → ℝ) (V : Matrix (Fin l) (Fin l) ℝ)
    (h : OutputBlocksDisjoint m l uBase sigmaBase vBase) (k : Fin (min m l)) :
    writeSVD memory uBase sigmaBase vBase U sigma V (sigmaBase + k.val) = sigma k := by
  have hs : sigmaBase ≤ sigmaBase + k.val ∧
      sigmaBase + k.val < sigmaBase + min m l := by omega
  have hu := disjointBlocks_not_mem_left h.1 hs
  simp only [writeSVD, if_neg hu, dif_pos hs]
  apply congrArg sigma
  apply Fin.ext
  change sigmaBase + k.val - sigmaBase = k.val
  omega

theorem writeSVD_v_entry {m l : ℕ} (memory : ℕ → ℝ)
    (uBase sigmaBase vBase : ℕ) (U : Matrix (Fin m) (Fin m) ℝ)
    (sigma : Fin (min m l) → ℝ) (V : Matrix (Fin l) (Fin l) ℝ)
    (h : OutputBlocksDisjoint m l uBase sigmaBase vBase) (i j : Fin l) :
    writeSVD memory uBase sigmaBase vBase U sigma V (vBase + i.val * l + j.val) =
      V i j := by
  have hi := matrix_offset_lt i j
  have hv : vBase ≤ vBase + i.val * l + j.val ∧
      vBase + i.val * l + j.val < vBase + l * l := by omega
  have hu := disjointBlocks_not_mem_left h.2.1 hv
  have hs := disjointBlocks_not_mem_left h.2.2 hv
  have hsub : vBase + i.val * l + j.val - vBase = i.val * l + j.val := by omega
  simp only [writeSVD, if_neg hu, dif_neg hs, if_pos hv, hsub]
  exact matrixCell_entry V i j

theorem readMatrix_writeSVD_v {m l : ℕ} (memory : ℕ → ℝ)
    (uBase sigmaBase vBase : ℕ) (U : Matrix (Fin m) (Fin m) ℝ)
    (sigma : Fin (min m l) → ℝ) (V : Matrix (Fin l) (Fin l) ℝ)
    (h : OutputBlocksDisjoint m l uBase sigmaBase vBase) :
    readMatrix (writeSVD memory uBase sigmaBase vBase U sigma V) l l vBase = V := by
  funext i j
  exact writeSVD_v_entry memory uBase sigmaBase vBase U sigma V h i j

theorem writeSVD_outside {m l : ℕ} (memory : ℕ → ℝ)
    (uBase sigmaBase vBase : ℕ) (U : Matrix (Fin m) (Fin m) ℝ)
    (sigma : Fin (min m l) → ℝ) (V : Matrix (Fin l) (Fin l) ℝ) (address : ℕ)
    (hu : ¬ (uBase ≤ address ∧ address < uBase + m * m))
    (hs : ¬ (sigmaBase ≤ address ∧ address < sigmaBase + min m l))
    (hv : ¬ (vBase ≤ address ∧ address < vBase + l * l)) :
    writeSVD memory uBase sigmaBase vBase U sigma V address = memory address := by
  simp only [writeSVD, if_neg hu, dif_neg hs, if_neg hv]

#assert_trust kernel matrixCell_entry
#assert_trust kernel readMatrix_writeSVD_u
#assert_trust kernel writeSVD_sigma_entry
#assert_trust kernel readMatrix_writeSVD_v
#assert_trust kernel writeSVD_outside
#print axioms matrixCell_entry
#print axioms readMatrix_writeSVD_u
#print axioms writeSVD_sigma_entry
#print axioms readMatrix_writeSVD_v
#print axioms writeSVD_outside

end NLA.Proofs.TR04
