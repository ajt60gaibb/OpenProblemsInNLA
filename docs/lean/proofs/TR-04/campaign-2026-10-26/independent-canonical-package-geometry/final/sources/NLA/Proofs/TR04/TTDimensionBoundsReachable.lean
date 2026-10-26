import NLA.Proofs.TR04.TTDimensionBounds
import NLA.Proofs.TR04.TensorCompressionRadix
import NLA.Proofs.TR04.ShapeInitializationBounds

/-! Reachable recursive formats, with no assumed capacity invariant. Each step
is precisely the format of the frozen stepInput. All product/rank/positivity
bounds are derived by induction from the original literal shape and ranks. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation

inductive Reachable (initial : List ℕ) (r : ℕ → ℕ) : ℕ → List ℕ → Prop
  | start : Reachable initial r 0 initial
  | step {level m n : ℕ} {ns : List ℕ}
      (parent : Reachable initial r level (m :: n :: ns)) :
      Reachable initial r (level + 1)
        ((stepRank m (n :: ns) (fun j => r (level + j)) * n) :: ns)

 theorem Reachable.invariants {initial ns : List ℕ} {r : ℕ → ℕ} {level : ℕ}
    (h : Reachable initial r level ns) (hpos : PositiveModes initial)
    (hr : PositiveRanks initial r) :
    PositiveModes ns ∧ PositiveRanks ns (fun j => r (level + j)) ∧
      ns.prod ≤ initial.prod ∧ ns.length + level = initial.length := by
  induction h with
  | start =>
    refine ⟨hpos, ?_, le_rfl, by omega⟩
    simpa only [Nat.zero_add] using hr
  | @step level m n ns parent ih =>
    obtain ⟨hp, hpr, hprod, hlen⟩ := ih
    refine ⟨step_positiveModes m n ns _ hp hpr, ?_, (step_prod_le m n ns _).trans hprod, ?_⟩
    · have hc := step_positiveRanks m n ns (fun j => r (level + j)) hpr
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hc
    · simp only [List.length_cons] at hlen ⊢
      omega

 theorem Reachable.step_bounds {initial ns : List ℕ} {r : ℕ → ℕ} {level m n : ℕ}
    (h : Reachable initial r level (m :: n :: ns))
    (hpos : PositiveModes initial) (hr : PositiveRanks initial r) :
    StepBounds m n ns (fun j => r (level + j)) initial.prod := by
  obtain ⟨hp, hpr, hprod, _⟩ := h.invariants hpos hr
  exact step_bounds_of_product m n ns _ initial.prod hp hpr hprod

 theorem Reachable.nonempty {initial ns : List ℕ} {r : ℕ → ℕ} {level : ℕ}
    (h : Reachable initial r level ns) (hi : initial ≠ []) : ns ≠ [] := by
  induction h with
  | start => exact hi
  | step => simp

 theorem tail_drop (ns : List ℕ) (k : ℕ) : (ns.drop k).tail = ns.drop (k + 1) := by
  induction k generalizing ns with
  | zero => cases ns <;> rfl
  | succ k ih =>
    cases ns with
    | nil => simp
    | cons m ns => exact ih ns

 theorem Reachable.tail_eq_drop {initial ns : List ℕ} {r : ℕ → ℕ} {level : ℕ}
    (h : Reachable initial r level ns) : ns.tail = initial.drop (level + 1) := by
  induction h with
  | start => exact tail_drop initial 0
  | @step level m n ns parent ih =>
    have ht := congrArg List.tail ih
    rw [tail_drop] at ht
    simpa only [List.tail_cons, Nat.add_assoc] using ht

 theorem Reachable.level_lt {initial ns : List ℕ} {r : ℕ → ℕ} {level : ℕ}
    (h : Reachable initial r level ns) (hi : initial ≠ [])
    (hpos : PositiveModes initial) (hr : PositiveRanks initial r) : level < initial.length := by
  have hn := h.nonempty hi
  have hl := (h.invariants hpos hr).2.2.2
  have hp : 0 < ns.length := List.length_pos_iff.mpr hn
  omega

 theorem positiveModes_original (S : Shape) : PositiveModes (modeList S.mode) := by
  unfold PositiveModes
  rw [modeList_eq_ofFn, List.forall_mem_ofFn_iff]
  intro i
  have := S.mode_ge i
  omega

 theorem positiveRanks_original (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j) :
    PositiveRanks (modeList S.mode) (originalRanks S r) := by
  intro j hj
  rw [length_modeList] at hj
  have hj' : j < S.order - 1 := by omega
  have hh := hr ⟨j, hj'⟩
  change 0 < originalRanks S r j
  rw [originalRanks, dif_pos hj']
  omega

 theorem Reachable.original_invariants (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j)
    {level : ℕ} {ns : List ℕ}
    (h : Reachable (modeList S.mode) (originalRanks S r) level ns) :
    PositiveModes ns ∧ PositiveRanks ns (fun j => originalRanks S r (level + j)) ∧
      ns.prod ≤ DenseSize S ∧ ns.length + level = S.order := by
  have hh := h.invariants (positiveModes_original S) (positiveRanks_original S r hr)
  simpa only [prod_modeList, length_modeList, DenseSize] using hh

 theorem Reachable.original_step_bounds (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j)
    {level m n : ℕ} {ns : List ℕ}
    (h : Reachable (modeList S.mode) (originalRanks S r) level (m :: n :: ns)) :
    StepBounds m n ns (fun j => originalRanks S r (level + j)) (DenseSize S) := by
  have hh := h.step_bounds (positiveModes_original S) (positiveRanks_original S r hr)
  simpa only [prod_modeList, DenseSize] using hh

 theorem Reachable.original_level_lt (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j)
    {level : ℕ} {ns : List ℕ}
    (h : Reachable (modeList S.mode) (originalRanks S r) level ns) : level < S.order := by
  have hi : modeList S.mode ≠ [] := by
    intro he
    have hh := length_modeList S.mode
    rw [he] at hh
    have := S.order_ge
    simp only [List.length_nil] at hh
    omega
  simpa only [length_modeList] using
    h.level_lt hi (positiveModes_original S) (positiveRanks_original S r hr)

 theorem Reachable.original_suffix (S : Shape) (r : Ranks S)
    {level m n : ℕ} {ns : List ℕ}
    (h : Reachable (modeList S.mode) (originalRanks S r) level (m :: n :: ns)) :
    suffixSize (n :: ns) = ((modeList S.mode).drop (level + 1)).prod := by
  rw [suffixSize_eq_prod]
  exact congrArg List.prod h.tail_eq_drop

#assert_trust kernel Reachable.invariants
#assert_trust kernel Reachable.original_step_bounds
#assert_trust kernel Reachable.original_level_lt
#assert_trust kernel Reachable.original_suffix
#print axioms Reachable.invariants
#print axioms Reachable.original_step_bounds
end NLA.Proofs.TR04.TensorFormat.Dimensions
