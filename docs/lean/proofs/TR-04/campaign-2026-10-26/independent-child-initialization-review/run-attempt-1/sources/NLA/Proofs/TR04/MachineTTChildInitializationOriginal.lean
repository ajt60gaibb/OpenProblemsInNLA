import NLA.Proofs.TR04.MachineTTChildInitialization

/-! Child setup for the unchanged original tensor header. Reachability derives
all dense/frame capacities; the only protected-memory premise is the actual
published input header, and no approximation evaluator is assumed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
open TTMemoryLayout

/-- Child preparation retains every concrete allocation address and constant. -/
theorem ttChildPreserves_allocation {s t : State ttProgram} {L : Layout}
    (h : TTChildPreserves s t) (hs : TTAllocationRegisters L s) : TTAllocationRegisters L t := by
  constructor
  all_goals first
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.order
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.entries
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.square
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.input
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.firstU
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.firstSigma
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.firstV
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.childSigma
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.childV
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.frames
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.metadata
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.workA
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.workB
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.store
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.four
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.one
    | exact (h.2 _ (by unfold TTChildKept; decide)).trans hs.zero

theorem ttChild_mode_le_size (S : Shape) (r : Ranks S) (level : ℕ) (hl : level < S.order) :
    shapeHeaderValues S level ≤ Size S r := by
  have hm := shape_mode_le_denseSize S ⟨level,hl⟩
  rw [← shapeHeaderValues_fin S ⟨level,hl⟩] at hm
  exact hm.trans (shape_denseSize_le_size S r)

theorem ttChild_rank_le_size (S : Shape) (r : Ranks S) (level : ℕ) (hl : level < S.order-1) :
    r ⟨level,hl⟩ ≤ Size S r := by
  have hr : r ⟨level,hl⟩ ≤ ∑ j,r j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (r j)) (Finset.mem_univ (⟨level,hl⟩ : Cut S))
  unfold Size
  omega

/-- Literal original-header child dimensions agree with a reachable recursive
format. The consistency premise describes its head, not an assumed capacity. -/
theorem ttChild_initialize_original_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (S : Shape) (r : Ranks S) (A : Tensor S) (hr : ∀ j, 1 ≤ r j)
    (level m n : ℕ) (ns : List ℕ)
    (hreach : TensorFormat.Dimensions.Reachable (TensorFormat.modeList S.mode)
      (TensorFormat.originalRanks S r) level (m :: n :: ns))
    (hl : (trace.state offset).label = 208) (hs : (trace.state offset).status = .running)
    (ha : TTAllocationRegisters (ofShape S) (trace.state offset))
    (hlevel : (trace.state offset).natural 84 = level)
    (hrows : (trace.state offset).natural 100 * shapeHeaderValues S level = m)
    (hheader : ∀ a, a < (ofShape S).input →
      (trace.state offset).memory a = InputMemory S r A a) :
    ∃ elapsed : ℕ, elapsed ≤ 100 * (Size S r + 1) ∧
      TTChildInitialized (trace.state offset) (trace.state (offset + elapsed))
        (shapeHeaderValues S level) (TensorFormat.originalRanks S r level) (shapeHeaderValues S) ∧
      TTAllocationRegisters (ofShape S) (trace.state (offset + elapsed)) ∧
      (trace.state (offset + elapsed)).natural 85 = m ∧
      (trace.state (offset + elapsed)).natural 87 = TensorFormat.suffixSize (n :: ns) ∧
      (trace.state (offset + elapsed)).natural 86 =
        TensorFormat.stepRank m (n :: ns) (fun j => TensorFormat.originalRanks S r (level+j)) ∧
      (trace.state (offset + elapsed)).natural 94 = (ofShape S).frame level ∧
      TensorFormat.Dimensions.StepBounds m n ns
        (fun j => TensorFormat.originalRanks S r (level+j)) (DenseSize S) ∧
      CostThrough ttProgram trace (offset + elapsed) ≤ CostThrough ttProgram trace offset + 100 * (Size S r + 1) := by
  have hlen := (hreach.original_invariants S r hr).2.2.2
  simp only [List.length_cons] at hlen
  have hlt : level < S.order-1 := by omega
  have hlo : level < S.order := by omega
  have had : level+1 ≤ S.order := by omega
  have horder : (trace.state offset).natural 0 = S.order := ha.order
  have hmode : (trace.state offset).memory ((trace.state offset).natural 84) = (shapeHeaderValues S level : ℝ) := by
    rw [hlevel,hheader level (by change level < 2*S.order-1; omega)]
    exact inputMemory_shapeHeader S r A level hlo
  have hrank : (trace.state offset).memory ((trace.state offset).natural 0 + (trace.state offset).natural 84) =
      (TensorFormat.originalRanks S r level : ℝ) := by
    rw [horder,hlevel,hheader (S.order+level) (by change S.order+level < 2*S.order-1; omega),inputMemory_rankHeader S r A level hlt]
    rw [TensorFormat.originalRanks,dif_pos hlt]
  have hvalues : ∀ j, (trace.state offset).natural 84+1 ≤ j → j < (trace.state offset).natural 0 →
      (trace.state offset).memory j = (shapeHeaderValues S j : ℝ) := by
    intro j hj hk
    rw [horder] at hk
    rw [hheader j (by change j < 2*S.order-1; have := S.order_ge; omega)]
    exact inputMemory_shapeHeader S r A j hk
  obtain ⟨elapsed,he,hi,hc⟩ := ttChild_initialize_at ht offset (shapeHeaderValues S level)
    (TensorFormat.originalRanks S r level) (shapeHeaderValues S) hl hs
    (by rw [hlevel,horder]; exact had) hmode hrank hvalues
  have hcols : headerRangeProduct (shapeHeaderValues S) ((trace.state offset).natural 84+1)
      ((trace.state offset).natural 0) = TensorFormat.suffixSize (n :: ns) := by
    rw [hlevel,horder,headerRangeProduct_shape_drop S (level+1) had]
    exact (hreach.original_suffix S r).symm
  have hm := ttChild_mode_le_size S r level hlo
  have hrr : TensorFormat.originalRanks S r level ≤ Size S r := by
    rw [TensorFormat.originalRanks,dif_pos hlt]
    exact ttChild_rank_le_size S r level hlt
  have htime := headerRangeTime_shape_le_size S r (level+1)
  rw [hlevel,horder] at he hc
  have hbound : 3*shapeHeaderValues S level + 3*TensorFormat.originalRanks S r level +
      headerRangeTime (shapeHeaderValues S) (level+1) S.order + 78 ≤ 100*(Size S r+1) := by omega
  refine ⟨elapsed,he.trans hbound,hi,ttChildPreserves_allocation hi.preserves ha,
    hi.rows.trans hrows,hi.columns.trans hcols,?_,?_,hreach.original_step_bounds S r hr,by omega⟩
  · rw [hi.cap,hrows,hcols]
    rfl
  · rw [hi.frame,ha.frames,hlevel,ha.square]
    rfl

/-- The same endpoint with the current head expressed literally from its actual
previous-rank register and current mode header. No separate dimension or
capacity invariant is required. -/
theorem ttChild_initialize_reachable_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (S : Shape) (r : Ranks S) (A : Tensor S) (hr : ∀ j, 1 ≤ r j)
    (level n : ℕ) (ns : List ℕ)
    (hreach : TensorFormat.Dimensions.Reachable (TensorFormat.modeList S.mode)
      (TensorFormat.originalRanks S r) level
      (((trace.state offset).natural 100 * shapeHeaderValues S level) :: n :: ns))
    (hl : (trace.state offset).label = 208) (hs : (trace.state offset).status = .running)
    (ha : TTAllocationRegisters (ofShape S) (trace.state offset))
    (hlevel : (trace.state offset).natural 84 = level)
    (hheader : ∀ a, a < (ofShape S).input →
      (trace.state offset).memory a = InputMemory S r A a) :
    let m := (trace.state offset).natural 100 * shapeHeaderValues S level
    ∃ elapsed : ℕ, elapsed ≤ 100 * (Size S r + 1) ∧
      TTChildInitialized (trace.state offset) (trace.state (offset + elapsed))
        (shapeHeaderValues S level) (TensorFormat.originalRanks S r level) (shapeHeaderValues S) ∧
      TTAllocationRegisters (ofShape S) (trace.state (offset + elapsed)) ∧
      (trace.state (offset + elapsed)).natural 85 = m ∧
      (trace.state (offset + elapsed)).natural 87 = TensorFormat.suffixSize (n :: ns) ∧
      (trace.state (offset + elapsed)).natural 86 =
        TensorFormat.stepRank m (n :: ns) (fun j => TensorFormat.originalRanks S r (level+j)) ∧
      (trace.state (offset + elapsed)).natural 94 = (ofShape S).frame level ∧
      TensorFormat.Dimensions.StepBounds m n ns
        (fun j => TensorFormat.originalRanks S r (level+j)) (DenseSize S) ∧
      CostThrough ttProgram trace (offset + elapsed) ≤ CostThrough ttProgram trace offset + 100 * (Size S r + 1) :=
  ttChild_initialize_original_at ht offset S r A hr level
    ((trace.state offset).natural 100 * shapeHeaderValues S level) n ns hreach hl hs ha hlevel rfl hheader

#assert_trust kernel ttChildPreserves_allocation
#assert_trust kernel ttChild_mode_le_size
#assert_trust kernel ttChild_rank_le_size
#assert_trust kernel ttChild_initialize_original_at
#assert_trust kernel ttChild_initialize_reachable_at
#print axioms ttChild_initialize_original_at
#print axioms ttChild_initialize_reachable_at
end NLA.Proofs.TR04
