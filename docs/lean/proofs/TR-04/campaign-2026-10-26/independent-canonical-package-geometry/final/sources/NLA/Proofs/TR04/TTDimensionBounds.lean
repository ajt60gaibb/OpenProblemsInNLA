import NLA.Proofs.TR04.TTCompletion

/-! Actual capped TT compression reduces the dense entry count. Positivity is
required only for the positive-rank execution branch; the nonincrease theorem
also covers zero dimensions and zero requested ranks. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.TR04.TensorFormat.Dimensions

def PositiveModes (ns : List ℕ) : Prop := ∀ n ∈ ns, 0 < n

def PositiveRanks (ns : List ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ j : ℕ, j + 1 < ns.length → 0 < r j

theorem positiveModes_cons {m : ℕ} {ns : List ℕ} :
    PositiveModes (m :: ns) ↔ 0 < m ∧ PositiveModes ns := by
  simp only [PositiveModes, List.mem_cons, forall_eq_or_imp]

theorem positiveModes_prod {ns : List ℕ} (h : PositiveModes ns) : 0 < ns.prod := by
  induction ns with
  | nil => simp
  | cons m ns ih =>
    obtain ⟨hm, ht⟩ := positiveModes_cons.mp h
    simpa only [List.prod_cons] using Nat.mul_pos hm (ih ht)

theorem suffixSize_eq_prod (ns : List ℕ) : suffixSize ns = ns.prod := card_index ns

theorem suffixSize_pos {ns : List ℕ} (h : PositiveModes ns) : 0 < suffixSize ns := by
  rw [suffixSize_eq_prod]
  exact positiveModes_prod h

theorem mode_le_prod {ns : List ℕ} (h : PositiveModes ns) (m : ℕ) (hm : m ∈ ns) :
    m ≤ ns.prod := by
  induction ns with
  | nil => simp at hm
  | cons n ns ih =>
    obtain ⟨hn, ht⟩ := positiveModes_cons.mp h
    have hp := positiveModes_prod ht
    rcases List.mem_cons.mp hm with he | hm
    · subst m
      simpa only [List.prod_cons, Nat.mul_one] using Nat.mul_le_mul_left n (show 1 ≤ ns.prod by omega)
    · have hi := ih ht hm
      have hm' := Nat.mul_le_mul_right ns.prod (show 1 ≤ n by omega)
      simp only [Nat.one_mul] at hm'
      exact hi.trans (by simpa only [List.prod_cons] using hm')

theorem stepRank_le_rows (m : ℕ) (ns : List ℕ) (r : ℕ → ℕ) : stepRank m ns r ≤ m :=
  (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)

theorem stepRank_le_cols (m : ℕ) (ns : List ℕ) (r : ℕ → ℕ) :
    stepRank m ns r ≤ suffixSize ns :=
  (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)

theorem stepRank_le_request (m : ℕ) (ns : List ℕ) (r : ℕ → ℕ) : stepRank m ns r ≤ r 0 :=
  Nat.min_le_left _ _

theorem stepRank_pos (m : ℕ) (ns : List ℕ) (r : ℕ → ℕ)
    (hm : 0 < m) (hns : PositiveModes ns) (hr : 0 < r 0) : 0 < stepRank m ns r := by
  exact lt_min hr (lt_min hm (suffixSize_pos hns))

theorem step_prod_le (m n : ℕ) (ns : List ℕ) (r : ℕ → ℕ) :
    ((stepRank m (n :: ns) r * n) :: ns).prod ≤ (m :: n :: ns).prod := by
  simp only [List.prod_cons, Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ (stepRank_le_rows m (n :: ns) r)

theorem step_compressed_dense_le (m : ℕ) (ns : List ℕ) (r : ℕ → ℕ) :
    stepRank m ns r * suffixSize ns ≤ (m :: ns).prod := by
  rw [List.prod_cons, suffixSize_eq_prod]
  exact Nat.mul_le_mul_right _ (stepRank_le_rows m ns r)

theorem step_length (m n : ℕ) (ns : List ℕ) (r : ℕ → ℕ) :
    ((stepRank m (n :: ns) r * n) :: ns).length + 1 = (m :: n :: ns).length := by simp

theorem step_positiveModes (m n : ℕ) (ns : List ℕ) (r : ℕ → ℕ)
    (h : PositiveModes (m :: n :: ns)) (hr : PositiveRanks (m :: n :: ns) r) :
    PositiveModes ((stepRank m (n :: ns) r * n) :: ns) := by
  obtain ⟨hm, ht⟩ := positiveModes_cons.mp h
  obtain ⟨hn, hns⟩ := positiveModes_cons.mp ht
  have hq := stepRank_pos m (n :: ns) r hm (positiveModes_cons.mpr ⟨hn, hns⟩)
    (hr 0 (by simp))
  exact positiveModes_cons.mpr ⟨Nat.mul_pos hq hn, hns⟩

theorem step_positiveRanks (m n : ℕ) (ns : List ℕ) (r : ℕ → ℕ)
    (hr : PositiveRanks (m :: n :: ns) r) :
    PositiveRanks ((stepRank m (n :: ns) r * n) :: ns) (fun j => r (j + 1)) := by
  intro j hj
  apply hr (j + 1)
  simp only [List.length_cons] at hj ⊢
  omega

structure StepBounds (m n : ℕ) (ns : List ℕ) (r : ℕ → ℕ) (bound : ℕ) : Prop where
  rows_pos : 0 < m
  cols_pos : 0 < suffixSize (n :: ns)
  rank_pos : 0 < stepRank m (n :: ns) r
  child_mode_pos : 0 < stepRank m (n :: ns) r * n
  tail_prod_pos : 0 < ns.prod
  rows_le : m ≤ bound
  cols_le : suffixSize (n :: ns) ≤ bound
  rank_le : stepRank m (n :: ns) r ≤ bound
  input_dense_le : m * suffixSize (n :: ns) ≤ bound
  contracted_dense_le : stepRank m (n :: ns) r * suffixSize (n :: ns) ≤ bound
  child_mode_le : stepRank m (n :: ns) r * n ≤ bound
  child_prod_le : ((stepRank m (n :: ns) r * n) :: ns).prod ≤ bound
  frame_square_le : m * m ≤ bound ^ 2
  frame_rectangle_le : m * stepRank m (n :: ns) r ≤ bound ^ 2
  right_square_le : suffixSize (n :: ns) * suffixSize (n :: ns) ≤ bound ^ 2

theorem step_bounds_of_product (m n : ℕ) (ns : List ℕ) (r : ℕ → ℕ) (bound : ℕ)
    (hpos : PositiveModes (m :: n :: ns)) (hr : PositiveRanks (m :: n :: ns) r)
    (hprod : (m :: n :: ns).prod ≤ bound) : StepBounds m n ns r bound := by
  have hm := (positiveModes_cons.mp hpos).1
  have ht := (positiveModes_cons.mp hpos).2
  have hl := suffixSize_pos ht
  have hq := stepRank_pos m (n :: ns) r hm ht (hr 0 (by simp))
  have hmle := (mode_le_prod hpos m (by simp)).trans hprod
  have hcol : suffixSize (n :: ns) ≤ bound := by
    have hh := Nat.mul_le_mul_right (n :: ns).prod (show 1 ≤ m by omega)
    simp only [Nat.one_mul] at hh
    rw [suffixSize_eq_prod]
    exact hh.trans hprod
  have hqle := (stepRank_le_rows m (n :: ns) r).trans hmle
  have hchild := (step_prod_le m n ns r).trans hprod
  have hchildpos := step_positiveModes m n ns r hpos hr
  exact {
    rows_pos := hm, cols_pos := hl, rank_pos := hq,
    child_mode_pos := (positiveModes_cons.mp hchildpos).1,
    tail_prod_pos := positiveModes_prod (positiveModes_cons.mp hchildpos).2,
    rows_le := hmle, cols_le := hcol, rank_le := hqle,
    input_dense_le := by
      calc
        m * suffixSize (n :: ns) = (m :: n :: ns).prod := by rw [suffixSize_eq_prod]; rfl
        _ ≤ bound := hprod,
    contracted_dense_le := (step_compressed_dense_le m (n :: ns) r).trans hprod,
    child_mode_le := (mode_le_prod hchildpos _ (by simp)).trans hchild,
    child_prod_le := hchild,
    frame_square_le := by simpa only [pow_two] using Nat.mul_le_mul hmle hmle,
    frame_rectangle_le := by simpa only [pow_two] using Nat.mul_le_mul hmle hqle,
    right_square_le := by simpa only [pow_two] using Nat.mul_le_mul hcol hcol }

#assert_trust kernel step_prod_le
#assert_trust kernel step_positiveModes
#assert_trust kernel step_positiveRanks
#assert_trust kernel step_bounds_of_product
#print axioms step_prod_le
#print axioms step_bounds_of_product
end NLA.Proofs.TR04.TensorFormat.Dimensions
