import NLA.Proofs.TR04.MachineTTChildInitializationOriginal
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
open NLA.Proofs.TR04 NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
open NLA.Proofs.TR04.TTMemoryLayout
namespace ChildInitializationExactConsumer
theorem literal_ttChild_initialize_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset mode rank : ℕ) (values : ℕ → ℕ)
    (hl : (trace.state offset).label = 208) (hs : (trace.state offset).status = .running)
    (had : (trace.state offset).natural 84 + 1 ≤ (trace.state offset).natural 0)
    (hmode : (trace.state offset).memory ((trace.state offset).natural 84) = (mode : ℝ))
    (hrank : (trace.state offset).memory ((trace.state offset).natural 0 + (trace.state offset).natural 84) = (rank : ℝ))
    (hvalues : ∀ j, (trace.state offset).natural 84 + 1 ≤ j → j < (trace.state offset).natural 0 →
      (trace.state offset).memory j = (values j : ℝ)) :
    ∃ elapsed : ℕ, elapsed ≤ 3 * mode + 3 * rank +
        headerRangeTime values ((trace.state offset).natural 84 + 1) ((trace.state offset).natural 0) + 78 ∧
      TTChildInitialized (trace.state offset) (trace.state (offset + elapsed)) mode rank values ∧
      CostThrough ttProgram trace (offset + elapsed) ≤ CostThrough ttProgram trace offset +
        (3 * mode + 3 * rank + headerRangeTime values ((trace.state offset).natural 84 + 1)
          ((trace.state offset).natural 0) + 78) := by
  exact ttChild_initialize_at ht offset mode rank values hl hs had hmode hrank hvalues
#assert_trust kernel literal_ttChild_initialize_at
#print axioms literal_ttChild_initialize_at

theorem literal_ttChild_initialize_original_at {start : State ttProgram} {trace : Trace ttProgram}
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
  exact ttChild_initialize_original_at ht offset S r A hr level m n ns hreach hl hs ha hlevel hrows hheader
#assert_trust kernel literal_ttChild_initialize_original_at
#print axioms literal_ttChild_initialize_original_at

theorem literal_ttChild_initialize_reachable_at {start : State ttProgram} {trace : Trace ttProgram}
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
      CostThrough ttProgram trace (offset + elapsed) ≤ CostThrough ttProgram trace offset + 100 * (Size S r + 1) := by
  exact ttChild_initialize_reachable_at ht offset S r A hr level n ns hreach hl hs ha hlevel hheader
#assert_trust kernel literal_ttChild_initialize_reachable_at
#print axioms literal_ttChild_initialize_reachable_at

theorem literal_child_svd_opcode : ttProgram.code 237 = .svd 85 87 89 94 103 104 238 := rfl
#assert_trust kernel literal_child_svd_opcode
#print axioms literal_child_svd_opcode

theorem literal_mode_read_opcode : ttProgram.code 208 = .read 0 84 209 := rfl
#assert_trust kernel literal_mode_read_opcode
#print axioms literal_mode_read_opcode

theorem literal_cap_end_empty (s : State ttProgram) (hr : s.natural 2=0) :
    (ttChildCapEnd s).natural 86=0 := by
  rw [(ttChild_cap_fields s).2.1,hr]
  exact Nat.zero_min _
#assert_trust kernel literal_cap_end_empty
#print axioms literal_cap_end_empty
end ChildInitializationExactConsumer

#assert_trust kernel NLA.Proofs.TR04.ttChildModeEntry
#print axioms NLA.Proofs.TR04.ttChildModeEntry

#assert_trust kernel NLA.Proofs.TR04.ttChildSuffixEntry
#print axioms NLA.Proofs.TR04.ttChildSuffixEntry

#assert_trust kernel NLA.Proofs.TR04.ttChildRankEntry
#print axioms NLA.Proofs.TR04.ttChildRankEntry

#assert_trust kernel NLA.Proofs.TR04.ttChildCapRowsEnd
#print axioms NLA.Proofs.TR04.ttChildCapRowsEnd

#assert_trust kernel NLA.Proofs.TR04.ttChildCapColsEnd
#print axioms NLA.Proofs.TR04.ttChildCapColsEnd

#assert_trust kernel NLA.Proofs.TR04.ttChildCapEnd
#print axioms NLA.Proofs.TR04.ttChildCapEnd

#assert_trust kernel NLA.Proofs.TR04.ttChild_mode_steps
#print axioms NLA.Proofs.TR04.ttChild_mode_steps

#assert_trust kernel NLA.Proofs.TR04.ttChild_suffix_steps
#print axioms NLA.Proofs.TR04.ttChild_suffix_steps

#assert_trust kernel NLA.Proofs.TR04.ttChild_rank_steps
#print axioms NLA.Proofs.TR04.ttChild_rank_steps

#assert_trust kernel NLA.Proofs.TR04.ttChild_cap_rows_steps
#print axioms NLA.Proofs.TR04.ttChild_cap_rows_steps

#assert_trust kernel NLA.Proofs.TR04.ttChild_cap_cols_steps
#print axioms NLA.Proofs.TR04.ttChild_cap_cols_steps

#assert_trust kernel NLA.Proofs.TR04.ttChild_cap_steps
#print axioms NLA.Proofs.TR04.ttChild_cap_steps

#assert_trust kernel NLA.Proofs.TR04.TTChildKept
#print axioms NLA.Proofs.TR04.TTChildKept

#assert_trust kernel NLA.Proofs.TR04.TTChildPreserves
#print axioms NLA.Proofs.TR04.TTChildPreserves

#assert_trust kernel NLA.Proofs.TR04.ttChildPreserves_trans
#print axioms NLA.Proofs.TR04.ttChildPreserves_trans

#assert_trust kernel NLA.Proofs.TR04.ttChild_mode_preserves
#print axioms NLA.Proofs.TR04.ttChild_mode_preserves

#assert_trust kernel NLA.Proofs.TR04.ttChild_suffix_preserves
#print axioms NLA.Proofs.TR04.ttChild_suffix_preserves

#assert_trust kernel NLA.Proofs.TR04.ttChild_rank_preserves
#print axioms NLA.Proofs.TR04.ttChild_rank_preserves

#assert_trust kernel NLA.Proofs.TR04.ttChild_cap_preserves
#print axioms NLA.Proofs.TR04.ttChild_cap_preserves

#assert_trust kernel NLA.Proofs.TR04.ttChild_dispatch_preserves
#print axioms NLA.Proofs.TR04.ttChild_dispatch_preserves

#assert_trust kernel NLA.Proofs.TR04.ttChild_header_preserves
#print axioms NLA.Proofs.TR04.ttChild_header_preserves

#assert_trust kernel NLA.Proofs.TR04.ttChildMode_relates
#print axioms NLA.Proofs.TR04.ttChildMode_relates

#assert_trust kernel NLA.Proofs.TR04.ttChildSuffix_relates
#print axioms NLA.Proofs.TR04.ttChildSuffix_relates

#assert_trust kernel NLA.Proofs.TR04.ttChildRank_relates
#print axioms NLA.Proofs.TR04.ttChildRank_relates

#assert_trust kernel NLA.Proofs.TR04.ttChild_cap_fields
#print axioms NLA.Proofs.TR04.ttChild_cap_fields

#assert_trust kernel NLA.Proofs.TR04.ttChild_cap_at
#print axioms NLA.Proofs.TR04.ttChild_cap_at

#assert_trust kernel NLA.Proofs.TR04.ttChild_mode_call_at
#print axioms NLA.Proofs.TR04.ttChild_mode_call_at

#assert_trust kernel NLA.Proofs.TR04.ttChild_suffix_call_at
#print axioms NLA.Proofs.TR04.ttChild_suffix_call_at

#assert_trust kernel NLA.Proofs.TR04.ttChild_rank_call_at
#print axioms NLA.Proofs.TR04.ttChild_rank_call_at

#assert_trust kernel NLA.Proofs.TR04.TTChildInitialized
#print axioms NLA.Proofs.TR04.TTChildInitialized

#assert_trust kernel NLA.Proofs.TR04.ttChild_initialize_at
#print axioms NLA.Proofs.TR04.ttChild_initialize_at

#assert_trust kernel NLA.Proofs.TR04.ttChildPreserves_allocation
#print axioms NLA.Proofs.TR04.ttChildPreserves_allocation

#assert_trust kernel NLA.Proofs.TR04.ttChild_mode_le_size
#print axioms NLA.Proofs.TR04.ttChild_mode_le_size

#assert_trust kernel NLA.Proofs.TR04.ttChild_rank_le_size
#print axioms NLA.Proofs.TR04.ttChild_rank_le_size

#assert_trust kernel NLA.Proofs.TR04.ttChild_initialize_original_at
#print axioms NLA.Proofs.TR04.ttChild_initialize_original_at

#assert_trust kernel NLA.Proofs.TR04.ttChild_initialize_reachable_at
#print axioms NLA.Proofs.TR04.ttChild_initialize_reachable_at
