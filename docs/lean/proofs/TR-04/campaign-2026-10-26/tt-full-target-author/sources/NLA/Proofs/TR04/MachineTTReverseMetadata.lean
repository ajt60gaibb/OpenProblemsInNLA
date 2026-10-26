import NLA.Proofs.TR04.MachineTTReverseRead

/-! Four literal saved metadata cells are decoded by actual instructions. Their
memory is unchanged, and each result supplies the next caller register. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
private theorem ttReverseMetadata_naturals : ttProgram.extraNatRegisters=127 := rfl

structure TTReverseMetadata (memory : ℕ → ℝ) (base m q cols stride : ℕ) : Prop where
  rows : memory base=(m : ℝ)
  width : memory (base+1)=(q : ℝ)
  columns : memory (base+2)=(cols : ℝ)
  rowStride : memory (base+3)=(stride : ℝ)

 theorem ttReverseReadEnd_fields (s : State ttProgram) (k : Fin 4) (value : ℕ) :
    (ttReverseReadEnd s k value).label=ttReverseReadHandler k ∧
    (ttReverseReadEnd s k value).status=.running ∧
    (ttReverseReadEnd s k value).memory=s.memory ∧
    (ttReverseReadEnd s k value).natural 2=value ∧
    (ttReverseReadEnd s k value).natural 93=ttReverseReadAddress s k ∧
    (ttReverseReadEnd s k value).natural 125=s.natural 125 := by
  fin_cases k
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,ttReverseMetadata_naturals,ttReverseReadEnd,
    ttHeaderDispatchEnd,ttReverseHeaderEnd,ttReverseReadEntry,ttReverseReadNatural,
    ttReverseReadHandler,ttHeaderHandler]

def ttReverseMetadataEnd (s : State ttProgram) (m q cols stride : ℕ) : State ttProgram :=
  ttReverseReadEnd (ttReverseReadEnd (ttReverseReadEnd (ttReverseReadEnd s 0 m) 1 q) 2 cols) 3 stride

def ttReverseMetadataTime (m q cols stride : ℕ) : ℕ :=
  (8+(3*m+5)+(2*(7+0)+3))+(8+(3*q+5)+(2*(7+1)+3))+
  (8+(3*cols+5)+(2*(7+2)+3))+(8+(3*stride+5)+(2*(7+3)+3))

 theorem ttReverseMetadataTime_eq (m q cols stride : ℕ) :
    ttReverseMetadataTime m q cols stride=3*(m+q+cols+stride)+132 := by
  unfold ttReverseMetadataTime
  omega

 theorem ttReverseMetadata_run_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset m q cols stride : ℕ)
    (hl : (trace.state offset).label=287) (hs : (trace.state offset).status=.running)
    (hfour : (trace.state offset).natural 125=4)
    (hm : TTReverseMetadata (trace.state offset).memory
      ((trace.state offset).natural 68+4*(trace.state offset).natural 84) m q cols stride) :
    trace.state (offset+ttReverseMetadataTime m q cols stride)=
      ttReverseMetadataEnd (trace.state offset) m q cols stride ∧
    CostThrough ttProgram trace (offset+ttReverseMetadataTime m q cols stride)≤
      CostThrough ttProgram trace offset+ttReverseMetadataTime m q cols stride := by
  let s := trace.state offset
  let t0 := offset+8+(3*m+5)+(2*(7+0)+3)
  let t1 := t0+8+(3*q+5)+(2*(7+1)+3)
  let t2 := t1+8+(3*cols+5)+(2*(7+2)+3)
  let t3 := t2+8+(3*stride+5)+(2*(7+3)+3)
  have h0 : s.memory (ttReverseReadAddress s 0)=(m : ℝ) := hm.rows
  obtain ⟨he0,hc0⟩ := ttReverseRead_call_at ht offset 0 m hl hs hfour h0
  change trace.state t0=ttReverseReadEnd s 0 m at he0
  have hfields0 := ttReverseReadEnd_fields s 0 m
  have hl1 : (trace.state t0).label=ttReverseReadLabel 1 := by rw [he0];exact hfields0.1
  have hs1 : (trace.state t0).status=.running := by rw [he0];exact hfields0.2.1
  have hf1 : (trace.state t0).natural 125=4 := by rw [he0,hfields0.2.2.2.2.2];exact hfour
  have hm1 : (trace.state t0).memory (ttReverseReadAddress (trace.state t0) 1)=(q : ℝ) := by
    rw [he0]
    simpa (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,ttReverseMetadata_naturals,ttReverseReadEnd,
      ttHeaderDispatchEnd,ttReverseHeaderEnd,ttReverseReadEntry,ttReverseReadNatural,
      ttReverseReadAddress] using hm.width
  obtain ⟨he1,hc1⟩ := ttReverseRead_call_at ht t0 1 q hl1 hs1 hf1 hm1
  change trace.state t1=ttReverseReadEnd (trace.state t0) 1 q at he1
  have hfields1 := ttReverseReadEnd_fields (trace.state t0) 1 q
  have hl2 : (trace.state t1).label=ttReverseReadLabel 2 := by rw [he1];exact hfields1.1
  have hs2 : (trace.state t1).status=.running := by rw [he1];exact hfields1.2.1
  have hf2 : (trace.state t1).natural 125=4 := by rw [he1,hfields1.2.2.2.2.2];exact hf1
  have hm2 : (trace.state t1).memory (ttReverseReadAddress (trace.state t1) 2)=(cols : ℝ) := by
    rw [he1,he0]
    simpa (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,ttReverseMetadata_naturals,ttReverseReadEnd,
      ttHeaderDispatchEnd,ttReverseHeaderEnd,ttReverseReadEntry,ttReverseReadNatural,
      ttReverseReadAddress,Nat.add_assoc] using hm.columns
  obtain ⟨he2,hc2⟩ := ttReverseRead_call_at ht t1 2 cols hl2 hs2 hf2 hm2
  change trace.state t2=ttReverseReadEnd (trace.state t1) 2 cols at he2
  have hfields2 := ttReverseReadEnd_fields (trace.state t1) 2 cols
  have hl3 : (trace.state t2).label=ttReverseReadLabel 3 := by rw [he2];exact hfields2.1
  have hs3 : (trace.state t2).status=.running := by rw [he2];exact hfields2.2.1
  have hf3 : (trace.state t2).natural 125=4 := by rw [he2,hfields2.2.2.2.2.2];exact hf2
  have hm3 : (trace.state t2).memory (ttReverseReadAddress (trace.state t2) 3)=(stride : ℝ) := by
    rw [he2,he1,he0]
    simpa (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,ttReverseMetadata_naturals,ttReverseReadEnd,
      ttHeaderDispatchEnd,ttReverseHeaderEnd,ttReverseReadEntry,ttReverseReadNatural,
      ttReverseReadAddress,Nat.add_assoc] using hm.rowStride
  obtain ⟨he3,hc3⟩ := ttReverseRead_call_at ht t2 3 stride hl3 hs3 hf3 hm3
  change trace.state t3=ttReverseReadEnd (trace.state t2) 3 stride at he3
  have htime : offset+ttReverseMetadataTime m q cols stride=t3 := by
    dsimp [ttReverseMetadataTime,t0,t1,t2,t3]
    omega
  rw [htime]
  refine ⟨?_,?_⟩
  · have he3' : trace.state t3=ttReverseReadEnd (trace.state t2) 3 stride := he3
    have he2' : trace.state t2=ttReverseReadEnd (trace.state t1) 2 cols := he2
    have he1' : trace.state t1=ttReverseReadEnd (trace.state t0) 1 q := he1
    rw [he3',he2',he1',he0]
    rfl
  · dsimp [t0,t1,t2,t3,ttReverseMetadataTime] at *
    omega

def TTReverseMetadataStable (i : Fin 128) : Prop :=
  i≠1 ∧ i≠2 ∧ i≠3 ∧ i≠85 ∧ i≠86 ∧ i≠87 ∧ i≠93 ∧ i≠97 ∧ i≠123

 theorem ttReverseMetadataEnd_natural (s : State ttProgram) (m q cols stride : ℕ)
    (i : Fin 128) (hi : TTReverseMetadataStable i) :
    (ttReverseMetadataEnd s m q cols stride).natural i=s.natural i := by
  rcases hi with ⟨h1,h2,h3,h85,h86,h87,h93,h97,h123⟩
  simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,ttReverseMetadataEnd,ttReverseReadEnd,
    ttHeaderDispatchEnd,ttReverseHeaderEnd,ttReverseReadEntry,ttReverseReadNatural,
    ttReverseMetadata_naturals,h1,h2,h3,h85,h86,h87,h93,h97,h123]

 theorem ttReverseMetadataEnd_real (s : State ttProgram) (m q cols stride : ℕ)
    (i : Fin 16) (hi : 2 ≤ i.val) :
    (ttReverseMetadataEnd s m q cols stride).real i=s.real i := by
  have h0 : i≠(0 : Fin 16) := by intro h;have := congrArg Fin.val h;change i.val=0 at this;omega
  have h1 : i≠(1 : Fin 16) := by intro h;have := congrArg Fin.val h;change i.val=1 at this;omega
  simp only [ttReverseMetadataEnd,ttReverseReadEnd,ttHeaderDispatchEnd,ttReverseHeaderEnd,
    ttReverseReadEntry,Function.update_of_ne h0,Function.update_of_ne h1]

 theorem ttReverseMetadataEnd_fields (s : State ttProgram) (m q cols stride : ℕ) :
    (ttReverseMetadataEnd s m q cols stride).label=319 ∧
    (ttReverseMetadataEnd s m q cols stride).status=.running ∧
    (ttReverseMetadataEnd s m q cols stride).memory=s.memory ∧
    (ttReverseMetadataEnd s m q cols stride).natural 85=m ∧
    (ttReverseMetadataEnd s m q cols stride).natural 86=q ∧
    (ttReverseMetadataEnd s m q cols stride).natural 87=cols ∧
    (ttReverseMetadataEnd s m q cols stride).natural 2=stride ∧
    (ttReverseMetadataEnd s m q cols stride).natural 93=s.natural 68+4*s.natural 84+3 := by
  simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,ttReverseMetadataEnd,ttReverseReadEnd,
    ttHeaderDispatchEnd,ttReverseHeaderEnd,ttReverseReadEntry,ttReverseReadNatural,
    ttReverseReadAddress,ttReverseMetadata_naturals,ttHeaderHandler,Nat.add_assoc]

def ttReverseStartState (s : State ttProgram) : State ttProgram :=
  { s with
    label := 287
    natural := Function.update s.natural (84 : Fin 128) (s.natural 84-1)
    status := .running }

 theorem ttReverseStart_step (s : State ttProgram) (hl : s.label=286) (hs : s.status=.running) :
    ordinaryStep ttProgram s=ttReverseStartState s := by
  simp only [ordinaryStep,hl,hs,ttProgram_code_reverse_286,ttReverseStartState]
  rfl

 theorem ttReverse_start_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=286) (hs : (trace.state offset).status=.running) :
    trace.state (offset+1)=ttReverseStartState (trace.state offset) ∧
    CostThrough ttProgram trace (offset+1)≤CostThrough ttProgram trace offset+1 := by
  apply ttScalar_finish_at ht offset 1 _ _ rfl
  exact ttReverseStart_step _ hl hs

#assert_trust kernel ttReverseStart_step
#assert_trust kernel ttReverse_start_at

#assert_trust kernel ttReverseMetadataEnd_natural
#assert_trust kernel ttReverseMetadataEnd_real
#assert_trust kernel ttReverseMetadataEnd_fields

#assert_trust kernel ttReverseReadEnd_fields
#assert_trust kernel ttReverseMetadataTime_eq
#assert_trust kernel ttReverseMetadata_run_at
#print axioms ttReverseMetadata_run_at
end NLA.Proofs.TR04
