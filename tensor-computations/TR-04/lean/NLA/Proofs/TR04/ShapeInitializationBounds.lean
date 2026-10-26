import NLA.Computation.TensorTrainApproximation
import LeanCert.Tactic.Verification

/-! Actual original-format header values and finite shape bounds. The original
order and lower mode-size assumptions are retained exactly. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04
open NLA.Computation.TensorTrainApproximation

def shapeHeaderValues (S : Shape) (j : ℕ) : ℕ :=
  if h : j < S.order then S.mode ⟨j, h⟩ else 0

theorem shapeHeaderValues_fin (S : Shape) (i : Fin S.order) :
    shapeHeaderValues S i.val = S.mode i := by
  simp [shapeHeaderValues, i.isLt]

theorem inputMemory_shapeHeader (S : Shape) (r : Ranks S) (A : Tensor S)
    (j : ℕ) (hj : j < S.order) :
    InputMemory S r A j = (shapeHeaderValues S j : ℝ) := by
  simp [InputMemory, shapeHeaderValues, hj]

theorem shapeHeaderValues_sum (S : Shape) :
    (∑ j ∈ Finset.range S.order, shapeHeaderValues S j) = ∑ i, S.mode i := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  exact shapeHeaderValues_fin S i

theorem shapeHeaderValues_product (S : Shape) :
    (∏ j ∈ Finset.range S.order, shapeHeaderValues S j) = DenseSize S := by
  rw [← Fin.prod_univ_eq_prod_range]
  unfold DenseSize
  apply Finset.prod_congr rfl
  intro i _
  exact shapeHeaderValues_fin S i

theorem fin_sum_le_prod_of_two_le_aux (d : ℕ) (n : Fin (d + 2) → ℕ)
    (hn : ∀ i, 2 ≤ n i) : (∑ i, n i) ≤ ∏ i, n i := by
  induction d with
  | zero =>
      simpa [Fin.sum_univ_succ, Fin.prod_univ_succ] using
        Nat.add_le_mul (hn (0 : Fin 2)) (hn (1 : Fin 2))
  | succ d ih =>
      rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
      have ht := ih (fun i : Fin (d + 2) => n i.succ) (fun i => hn i.succ)
      have hsum : 2 ≤ ∑ i : Fin (d + 2), n i.succ := by
        exact (hn (0 : Fin (d + 2)).succ).trans
          (Finset.single_le_sum (fun i _ => Nat.zero_le (n i.succ))
            (Finset.mem_univ (0 : Fin (d + 2))))
      exact (Nat.add_le_mul (hn 0) hsum).trans (Nat.mul_le_mul_left _ ht)

theorem fin_sum_le_prod_of_two_le {d : ℕ} (n : Fin d → ℕ)
    (hd : 2 ≤ d) (hn : ∀ i, 2 ≤ n i) : (∑ i, n i) ≤ ∏ i, n i := by
  cases d with
  | zero => omega
  | succ d =>
      cases d with
      | zero => omega
      | succ d => exact fin_sum_le_prod_of_two_le_aux d n hn

theorem shape_sum_modes_le_denseSize (S : Shape) :
    (∑ i, S.mode i) ≤ DenseSize S :=
  fin_sum_le_prod_of_two_le S.mode (by have := S.order_ge; omega) S.mode_ge

theorem shape_denseSize_pos (S : Shape) : 0 < DenseSize S := by
  apply Finset.prod_pos
  intro i _
  have := S.mode_ge i
  omega

theorem shape_order_le_denseSize (S : Shape) : S.order ≤ DenseSize S := by
  calc
    S.order = ∑ _i : Fin S.order, 1 := by simp
    _ ≤ ∑ i, S.mode i := by
      apply Finset.sum_le_sum
      intro i _
      have := S.mode_ge i
      omega
    _ ≤ DenseSize S := shape_sum_modes_le_denseSize S

theorem shape_mode_le_denseSize (S : Shape) (i : Fin S.order) :
    S.mode i ≤ DenseSize S := by
  apply Finset.single_le_prod' (fun j _ => ?_) (Finset.mem_univ i)
  have := S.mode_ge j
  omega

theorem shape_suffix_pos (S : Shape) (i : Fin S.order) : 0 < SuffixSize S i := by
  apply Finset.prod_pos
  intro j _
  have := S.mode_ge j
  omega

theorem shape_suffix_le_denseSize (S : Shape) (i : Fin S.order) :
    SuffixSize S i ≤ DenseSize S := by
  apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
  intro j _ _
  have := S.mode_ge j
  omega

theorem shape_denseSize_le_size (S : Shape) (r : Ranks S) : DenseSize S ≤ Size S r := by
  unfold Size
  omega

#assert_trust kernel inputMemory_shapeHeader
#assert_trust kernel shapeHeaderValues_product
#assert_trust kernel shape_sum_modes_le_denseSize
#assert_trust kernel shape_order_le_denseSize
#assert_trust kernel shape_mode_le_denseSize
#assert_trust kernel shape_suffix_le_denseSize
#print axioms shape_sum_modes_le_denseSize
#print axioms shape_order_le_denseSize
end NLA.Proofs.TR04
