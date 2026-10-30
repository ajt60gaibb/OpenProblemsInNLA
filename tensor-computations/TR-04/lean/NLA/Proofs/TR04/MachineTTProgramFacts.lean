import NLA.Proofs.TR04.MachineTTProgram
import NLA.Proofs.TR04.MachineHeaderProductOriginal
import NLA.Proofs.TR04.MachineHeaderProductCallable
import NLA.Proofs.TR04.MachineInstructionTrace

/-! Exact syntax and the first actual execution prefix of the fixed TT caller.
The full candidate loop, approximation endpoint and global polynomial charge
are separate obligations. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation

theorem ttProgram_code_first_svd : ttProgram.code 167 = .svd 81 82 92 72 73 74 168 := rfl
theorem ttProgram_code_child_svd : ttProgram.code 237 = .svd 85 87 89 94 103 104 238 := rfl
theorem ttProgram_code_header_exit : ttProgram.code 10 = .jump 372 := rfl
theorem ttProgram_code_matrix_exit : ttProgram.code 32 = .equalNat 97 127 274 394 := rfl
theorem ttProgram_code_copy_exit : ttProgram.code 39 = .jump 355 := rfl
theorem ttProgram_code_gather_exit : ttProgram.code 65 = .jump 198 := rfl
theorem ttProgram_code_threshold_exit : ttProgram.code 88 = .jump 179 := rfl
theorem ttProgram_code_best_exit : ttProgram.code 114 = .copyNat 83 55 371 := rfl

/-- All caller labels beyond the six bank intervals retain the literal static
controller code. This is code equality, with no evaluation of tensor data. -/
theorem ttProgram_code_caller (label : Fin 512) (hl : 119≤label.val) :
    ttProgram.code label=ttControllerProgram.code label := by
  have h0 := installCodeBank_outside bestCandidateProgram ttBankStage5 ttBestRegisters 89 (by decide) label (by
    change ¬(89≤label.val ∧ label.val<89+30)
    omega)
  have h1 := installCodeBank_outside thresholdScanProgram ttBankStage4 ttThresholdRegisters 66 (by decide) label (by
    change ¬(66≤label.val ∧ label.val<66+23)
    omega)
  have h2 := installCodeBank_outside frameGatherProgram ttBankStage3 ttGatherRegisters 40 (by decide) label (by
    change ¬(40≤label.val ∧ label.val<40+26)
    omega)
  have h3 := installCodeBank_outside copyProgram ttBankStage2 ttCopyRegisters 33 (by decide) label (by
    change ¬(33≤label.val ∧ label.val<33+7)
    omega)
  have h4 := installCodeBank_outside matrixMultiplyProgram ttBankStage1 ttMatrixRegisters 11 (by decide) label (by
    change ¬(11≤label.val ∧ label.val<11+22)
    omega)
  have h5 := installCodeBank_outside headerProductProgram ttControllerProgram ttHeaderRegisters 0 (by decide) label (by
    change ¬(0≤label.val ∧ label.val<0+11)
    omega)
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))

/-- The only SVD opcodes in the whole finite syntax are its first and child calls. -/
theorem ttProgram_svd_positions : ∀ label : Fin 512,
    instructionIsSVD (ttProgram.code label) = true ↔ label.val=167 ∨ label.val=237 := by
  decide

/-- Arbitrary input memory enters the actual header bank with literal initial
registers; its product and unread header values have not been supplied. -/
theorem ttHeader_initial_relates (memory : ℕ → ℝ) (d : ℕ) :
    ttHeaderEmbedding.Relates (initial headerProductProgram d memory) (initial ttProgram d memory) := by
  constructor
  · rfl
  · rfl
  · funext r
    change (if ttHeaderEmbedding.naturals r=0 then d else 0)=(if r=0 then d else 0)
    have hv : (ttHeaderEmbedding.naturals r).val=r.val := by
      change 0+r.val=r.val
      omega
    simp only [Fin.ext_iff,Fin.val_zero,hv]
  · rfl
  · rfl

/-- Actual full-model trace existence for the fixed finite program. -/
theorem ttProgram_trace_exists (S : Shape) (r : Ranks S) (A : Tensor S) :
    ∃ trace : Trace ttProgram,LegalTrace ttProgram (Start ttProgram S r A) trace :=
  exists_legalTrace _ _

/-- Every legal trace from the original Start computes N before caller startup,
preserves the whole input store, and has the original uniform linear charge. -/
theorem ttProgram_header_result (S : Shape) (r : Ranks S) (A : Tensor S)
    (trace : Trace ttProgram) (ht : LegalTrace ttProgram (Start ttProgram S r A) trace) :
    (trace.state (headerProductReturnTime (shapeHeaderValues S) S.order)).label=10 ∧
    (trace.state (headerProductReturnTime (shapeHeaderValues S) S.order)).status=.running ∧
    (trace.state (headerProductReturnTime (shapeHeaderValues S) S.order)).natural 2=DenseSize S ∧
    (trace.state (headerProductReturnTime (shapeHeaderValues S) S.order)).memory=InputMemory S r A ∧
    CostThrough ttProgram trace (headerProductReturnTime (shapeHeaderValues S) S.order)≤7*Size S r := by
  have hs : ttHeaderEmbedding.Relates (initial headerProductProgram S.order (InputMemory S r A))
      (trace.state 0) := by
    rw [ht.1]
    exact ttHeader_initial_relates _ _
  obtain ⟨counter,reals,hr,hc⟩ := ttHeaderEmbedding.headerProduct_run_at (InputMemory S r A)
    S.order (shapeHeaderValues S) (inputMemory_shapeHeader S r A) ht 0 hs
  simp only [costThrough_zero,zero_add] at hr hc
  refine ⟨hr.label,hr.status,?_,hr.memory,?_⟩
  · exact (hr.natural_apply 2).trans (headerPrefixProduct_shape S)
  · have htime : headerProductReturnTime (shapeHeaderValues S) S.order≤
        headerProductTime (shapeHeaderValues S) S.order := by
      unfold headerProductReturnTime headerProductTime
      omega
    exact hc.trans (htime.trans (headerProductTime_shape_le_size S r))

/-- All caller natural registers outside the four-register header frame retain
their literal initial zero through this actual prefix. -/
theorem ttProgram_header_natural_outside (S : Shape) (r : Ranks S) (A : Tensor S)
    (trace : Trace ttProgram) (ht : LegalTrace ttProgram (Start ttProgram S r A) trace)
    (j : Fin 128) (hj : 4≤j.val) :
    (trace.state (headerProductReturnTime (shapeHeaderValues S) S.order)).natural j=0 := by
  let values := shapeHeaderValues S
  let memory := InputMemory S r A
  have hs := ttHeader_initial_relates memory S.order
  have hn := ordinary_nohalt_prefix_of_running (initial headerProductProgram S.order memory)
    (headerProductReturnTime values S.order)
    (headerProduct_return_running memory S.order values (inputMemory_shapeHeader S r A))
  have hc : ∀ k<headerProductReturnTime values S.order,instructionIsSVD
      (headerProductProgram.code ((ordinaryStep headerProductProgram)^[k]
        (initial headerProductProgram S.order memory)).label)=false :=
    fun _ _ => headerProductProgram_scalar _
  have hframe : ∀ i,j≠ttHeaderEmbedding.naturals i := by
    intro i heq
    have heq' := congrArg Fin.val heq
    have hv : (ttHeaderEmbedding.naturals i).val=i.val := by
      change 0+i.val=i.val
      omega
    rw [hv] at heq'
    have hi : i.val<4 := i.isLt
    omega
  have hv := ttHeaderEmbedding.scalar_trace_natural_outside _ hs ht _ hn hc j hframe
  have hz : (initial ttProgram S.order memory).natural j=0 := by
    change (if j=0 then S.order else 0)=0
    split
    · next heq =>
        have hval := congrArg Fin.val heq
        change j.val=0 at hval
        omega
    · rfl
  exact hv.trans hz

#assert_trust kernel ttProgram_code_first_svd
#assert_trust kernel ttProgram_code_child_svd
#assert_trust kernel ttProgram_code_header_exit
#assert_trust kernel ttProgram_code_matrix_exit
#assert_trust kernel ttProgram_code_copy_exit
#assert_trust kernel ttProgram_code_gather_exit
#assert_trust kernel ttProgram_code_threshold_exit
#assert_trust kernel ttProgram_code_best_exit
#assert_trust kernel ttProgram_code_caller
#assert_trust kernel ttProgram_svd_positions
#assert_trust kernel ttHeader_initial_relates
#assert_trust kernel ttProgram_trace_exists
#assert_trust kernel ttProgram_header_result
#assert_trust kernel ttProgram_header_natural_outside
#print axioms ttProgram_header_result
#print axioms ttProgram_svd_positions
end NLA.Proofs.TR04
