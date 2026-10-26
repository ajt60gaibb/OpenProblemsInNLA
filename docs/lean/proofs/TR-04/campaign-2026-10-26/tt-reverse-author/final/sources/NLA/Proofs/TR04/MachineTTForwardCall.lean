import NLA.Proofs.TR04.MachineTTForwardReturn
import NLA.Proofs.TR04.MachineTensorMultiplyTrace

/-! The actual prepared forward caller state enters the frozen matrix bank.
Tensor inputs are literal stored entries, and separation is the machine's
actual block condition rather than an approximation or solver assumption. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat

structure TTForwardRegisters (s : State ttProgram)
    (m q cols stride frame input output tag : ℕ) : Prop where
  zero : s.natural 127=0
  one : s.natural 126=1
  rows : s.natural 85=m
  width : s.natural 86=q
  columns : s.natural 87=cols
  rowStride : s.natural 88=stride
  frameBase : s.natural 94=frame
  inputBase : s.natural 89=input
  outputBase : s.natural 90=output
  forwardTag : s.natural 108=tag

def ttForwardScratch (s : State ttProgram) : MatrixMultiplyScratch where
  a := 0
  bp := 0
  cp := 0
  real i := s.real (⟨2+i.val,by have := i.isLt;omega⟩ : Fin 16)

 theorem ttForwardSetup_relates (s : State ttProgram)
    (m q : ℕ) (ns : List ℕ) (stride frame input output tag : ℕ)
    (hr : TTForwardRegisters s m q (suffixSize ns) stride frame input output tag) :
    ttMatrixEmbedding.Relates (matrixMultiplyRowState
      (contractMultiplyData s.memory m q ns frame stride input output) 0 (ttForwardScratch s))
      (ttForwardSetupEnd s) := by
  rcases hr with ⟨hz,ho,hm,hq,hcols,hstride,hframe,hinput,houtput,htag⟩
  constructor
  · rfl
  · funext i
    rfl
  · funext i
    change ttForwardSetupNaturalPrefix s.natural 18 (⟨4+i.val,by have := i.isLt;change i.val<17 at this;omega⟩ : Fin 128) = _
    fin_cases i
    all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,ttForwardSetupNaturalPrefix,ttForwardSetupCells,List.foldl,
      matrixMultiplyRowState,matrixMultiplyState,contractMultiplyData,actMultiplyData,
      ttForwardScratch,hz,ho,hm,hq,hcols,hstride,hframe,hinput,houtput]
  · simp only [ttForwardSetupEnd,ttForwardSetupMiddle,matrixMultiplyRowState,matrixMultiplyState,
      MatrixMultiplyData.outputPrefix,Nat.zero_mul,prefixMemory_zero,contractMultiplyData,actMultiplyData]
  · rfl

 theorem ttMatrix_natural_outside (i : Fin 128) (hi : (i.val < 4) ∨ (21 ≤ i.val)) :
    ∀ j, i≠ttMatrixEmbedding.naturals j := by
  intro j heq
  have hv := congrArg Fin.val heq
  change i.val=4+j.val at hv
  have hj : j.val<17 := j.isLt
  omega

 theorem ttMatrix_real_outside (i : Fin 16) (hi : (i.val < 2) ∨ (5 ≤ i.val)) :
    ∀ j, i≠ttMatrixEmbedding.reals j := by
  intro j heq
  have hv := congrArg Fin.val heq
  change i.val=2+j.val at hv
  have hj : j.val<3 := j.isLt
  omega

 theorem ttNaturalFold_outside (cells : List (Fin 128 × ℕ)) (old : Fin 128 → ℕ) (i : Fin 128)
    (h : ∀ cell∈cells,i≠cell.1) :
    cells.foldl (fun regs cell => Function.update regs cell.1 cell.2) old i=old i := by
  induction cells generalizing old with
  | nil => rfl
  | cons cell cells ih =>
    rw [List.foldl_cons,ih _ (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    exact Function.update_of_ne (h cell (List.mem_cons_self ..)) _ _

 theorem ttForwardSetup_natural_outside (s : State ttProgram) (i : Fin 128)
    (hi : (i.val < 4) ∨ (21 ≤ i.val)) (hi97 : i≠97) :
    (ttForwardSetupEnd s).natural i=s.natural i := by
  apply ttNaturalFold_outside
  intro cell hc
  have hc' := List.mem_of_mem_take hc
  simp only [ttForwardSetupCells,List.mem_cons,List.not_mem_nil,or_false] at hc'
  have hne (j : Fin 128) (hj : 4≤j.val ∧ j.val≤20) : i≠j := by
    intro heq
    have he := congrArg Fin.val heq
    omega
  rcases hc' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact hi97 | exact hne _ (by dsimp only [Prod.fst]; decide)

 theorem ttForwardSetup_tag (s : State ttProgram) :
    (ttForwardSetupEnd s).natural 97=s.natural 108 := by
  simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,-Fin.val_eq_zero_iff,
    ttForwardSetupEnd,ttForwardSetupMiddle,ttForwardSetupNaturalPrefix,
    ttForwardSetupCells,List.foldl]

 theorem ttForward_contract_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (m q : ℕ) (ns : List ℕ) (stride frame input output tag : ℕ)
    (hl : (trace.state offset).label=255) (hs : (trace.state offset).status=.running)
    (hr : TTForwardRegisters (trace.state offset) m q (suffixSize ns) stride frame input output tag)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (A : Tensor (m::ns)) (hA : StoresTensor (trace.state offset).memory input (m::ns) A)
    (hQblock : DisjointBlocks frame (m*stride) output (q*suffixSize ns))
    (hAblock : DisjointBlocks input (m*suffixSize ns) output (q*suffixSize ns)) :
    let p := contractMultiplyData (trace.state offset).memory m q ns frame stride input output
    let time := offset+19+matrixMultiplyReturnTime p
    (trace.state time).label=32 ∧ (trace.state time).status=.running ∧
    StoresTensor (trace.state time).memory output (q::ns) (contract Q A) ∧
    StoresTensor (trace.state time).memory input (m::ns) A ∧
    StoresFrame (trace.state time).memory frame stride Q ∧
    (∀ a, ¬(output≤a ∧ a<output+q*suffixSize ns) →
      (trace.state time).memory a=(trace.state offset).memory a) ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+19+17*(q+m+suffixSize ns+1)^3 ∧
    (∀ i : Fin 16, (i.val < 2) ∨ (5 ≤ i.val) → (trace.state time).real i=(trace.state offset).real i) ∧
    (∀ i : Fin 128, ((i.val < 4) ∨ (21 ≤ i.val)) → i≠97 →
      (trace.state time).natural i=(trace.state offset).natural i) ∧
    (trace.state time).natural 97=tag := by
  let s := trace.state offset
  let p := contractMultiplyData s.memory m q ns frame stride input output
  obtain ⟨hsetup,hsetupCost⟩ := ttForwardSetup_run_at ht offset hl hs
  have hrel := ttForwardSetup_relates s m q ns stride frame input output tag hr
  have hc : ttMatrixEmbedding.Relates (matrixMultiplyRowState p 0 (ttForwardScratch s))
      (trace.state (offset+19)) := by rw [hsetup];exact hrel
  obtain ⟨hp,hstatus,hout,hin,hframe,hmem,hcost,hreal,hnatural⟩ :=
    ttMatrixEmbedding.contract_run_at s.memory frame stride input output hq Q hQ A hA
      hQblock hAblock (ttForwardScratch s) ht (offset+19) hc
  refine ⟨hp,hstatus,hout,hin,hframe,hmem,?_,?_,?_,?_⟩
  · exact hcost.trans (Nat.add_le_add_right hsetupCost _)
  · intro i hi
    rw [hreal i (ttMatrix_real_outside i hi),hsetup]
    rfl
  · intro i hi hi97
    rw [hnatural i (ttMatrix_natural_outside i hi),hsetup]
    exact ttForwardSetup_natural_outside s i hi hi97
  · rw [hnatural 97 (ttMatrix_natural_outside 97 (by decide)),hsetup,ttForwardSetup_tag]
    exact hr.forwardTag

#assert_trust kernel ttForwardSetup_relates
#assert_trust kernel ttForward_contract_at
#print axioms ttForwardSetup_relates
#print axioms ttForward_contract_at
end NLA.Proofs.TR04
