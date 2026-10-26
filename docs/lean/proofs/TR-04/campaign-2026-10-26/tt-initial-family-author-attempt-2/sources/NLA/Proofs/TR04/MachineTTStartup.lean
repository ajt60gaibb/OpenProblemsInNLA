import NLA.Proofs.TR04.MachineTTProgramFacts
import NLA.Proofs.TR04.MachineHeaderProductSingle
import NLA.Proofs.TR04.TTMemoryLayoutBounds

/-! Actual finite startup block: pointer allocation uses natural arithmetic,
then the first mode header is really read before entering the shared decoder.
No unread shape value is supplied as a register or executable constant. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout

instance ttStartup_nonzero_realRegisters : NeZero ttProgram.realRegisters := ⟨by decide⟩
private theorem ttStartup_labels : ttProgram.extraLabels=511 := rfl
private theorem ttStartup_naturals : ttProgram.extraNatRegisters=127 := rfl
private theorem ttStartup_reals : ttProgram.realRegisters=16 := rfl

private theorem ttStartup_code119 : ttProgram.code 119=.copyNat 64 2 120 := rfl
private theorem ttStartup_code120 : ttProgram.code 120=.mulNat 66 64 64 121 := rfl
private theorem ttStartup_code121 : ttProgram.code 121=.natural 126 1 122 := rfl
private theorem ttStartup_code122 : ttProgram.code 122=.natural 125 4 123 := rfl
private theorem ttStartup_code123 : ttProgram.code 123=.addNat 92 0 0 124 := rfl
private theorem ttStartup_code124 : ttProgram.code 124=.decrement 92 125 := rfl
private theorem ttStartup_code125 : ttProgram.code 125=.addNat 72 92 64 126 := rfl
private theorem ttStartup_code126 : ttProgram.code 126=.addNat 73 72 66 127 := rfl
private theorem ttStartup_code127 : ttProgram.code 127=.addNat 74 73 64 128 := rfl
private theorem ttStartup_code128 : ttProgram.code 128=.addNat 103 74 66 129 := rfl
private theorem ttStartup_code129 : ttProgram.code 129=.addNat 104 103 64 130 := rfl
private theorem ttStartup_code130 : ttProgram.code 130=.addNat 67 104 66 131 := rfl
private theorem ttStartup_code131 : ttProgram.code 131=.mulNat 123 0 66 132 := rfl
private theorem ttStartup_code132 : ttProgram.code 132=.addNat 68 67 123 133 := rfl
private theorem ttStartup_code133 : ttProgram.code 133=.mulNat 123 125 0 134 := rfl
private theorem ttStartup_code134 : ttProgram.code 134=.addNat 69 68 123 135 := rfl
private theorem ttStartup_code135 : ttProgram.code 135=.addNat 70 69 64 136 := rfl
private theorem ttStartup_code136 : ttProgram.code 136=.addNat 71 70 64 137 := rfl
private theorem ttStartup_code137 : ttProgram.code 137=.natural 76 0 138 := rfl
private theorem ttStartup_code138 : ttProgram.code 138=.read 0 127 139 := rfl
private theorem ttStartup_code139 : ttProgram.code 139=.copyNat 1 0 140 := rfl
private theorem ttStartup_code140 : ttProgram.code 140=.natural 2 1 141 := rfl
private theorem ttStartup_code141 : ttProgram.code 141=.natural 3 0 142 := rfl
private theorem ttStartup_code142 : ttProgram.code 142=.natural 97 1 143 := rfl
private theorem ttStartup_code143 : ttProgram.code 143=.jump 5 := rfl

theorem ordinary_nosvd_prefix_of_running {P : Program} (s : State P) (n : ℕ)
    (hn : ((ordinaryStep P)^[n] s).status=.running) (k : ℕ) (hk : k<n) :
    instructionIsSVD (P.code ((ordinaryStep P)^[k] s).label)=false := by
  have hs := ordinary_running_prefix s n hn k hk.le
  have hsnext := ordinary_running_prefix s n hn (k+1) (by omega)
  rw [Function.iterate_succ_apply'] at hsnext
  cases hi : P.code ((ordinaryStep P)^[k] s).label <;>
    simp only [instructionIsSVD]
  simp [ordinaryStep,hs,hi] at hsnext


def ttStartupNatural (old : Fin 128 → ℕ) (L : Layout) : Fin 128 → ℕ :=
  ([(64,L.entries),(66,L.entries^2),(126,1),(125,4),
    (92,L.input),(72,L.firstU),(73,L.firstSigma),(74,L.firstV),
    (103,L.childSigma),(104,L.childV),(67,L.frames),(123,L.order*L.entries^2),
    (68,L.metadata),(123,4*L.order),(69,L.workA),(70,L.workB),(71,L.store),
    (76,0),(1,L.order),(2,1),(3,0),(97,1)] : List (Fin 128 × ℕ)).foldl
      (fun registers cell => Function.update registers cell.1 cell.2) old

def ttStartupEnd (s : State ttProgram) (L : Layout) : State ttProgram where
  label := 5
  real := Function.update s.real 0 (s.memory 0)
  natural := ttStartupNatural s.natural L
  memory := s.memory
  status := .running

def ttStartupNaturalPrefix (old : Fin 128 → ℕ) (L : Layout) (count : ℕ) : Fin 128 → ℕ :=
  (([(64,L.entries),(66,L.entries^2),(126,1),(125,4),
    (92,L.input),(72,L.firstU),(73,L.firstSigma),(74,L.firstV),
    (103,L.childSigma),(104,L.childV),(67,L.frames),(123,L.order*L.entries^2),
    (68,L.metadata),(123,4*L.order),(69,L.workA),(70,L.workB),(71,L.store),
    (76,0),(1,L.order),(2,1),(3,0),(97,1)] : List (Fin 128 × ℕ)).take count).foldl
      (fun registers cell => Function.update registers cell.1 cell.2) old

def ttStartupMiddle (s : State ttProgram) (L : Layout) (count label : ℕ)
    (hlabel : label<512) : State ttProgram where
  label := ⟨label,hlabel⟩
  real := s.real
  natural := ttStartupNaturalPrefix s.natural L count
  memory := s.memory
  status := .running

theorem ttStartup_first (s : State ttProgram) (L : Layout)
    (hl : s.label=119) (hs : s.status=.running)
    (hd : s.natural 0=L.order) (hn : s.natural 2=L.entries) :
    (ordinaryStep ttProgram)^[6] s=ttStartupMiddle s L 5 125 (by decide) := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,Function.update_idem,dite_eq_ite,
    ttStartup_labels,ttStartup_naturals,ttStartup_reals,Function.iterate_succ_apply',ordinaryStep,
    hl,hs,hd,hn,ttStartup_code119,ttStartup_code120,ttStartup_code121,ttStartup_code122,ttStartup_code123,ttStartup_code124,ttStartupMiddle,
    ttStartupNaturalPrefix,List.foldl,Layout.input,pow_two,← Nat.two_mul]


theorem ttStartup_second (s : State ttProgram) (L : Layout) :
    (ordinaryStep ttProgram)^[6] (ttStartupMiddle s L 5 125 (by decide))=
      ttStartupMiddle s L 11 131 (by decide) := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,Function.update_idem,dite_eq_ite,
    ttStartup_labels,ttStartup_naturals,ttStartup_reals,Function.iterate_succ_apply',ordinaryStep,
    ttStartup_code125,ttStartup_code126,ttStartup_code127,ttStartup_code128,ttStartup_code129,ttStartup_code130,ttStartupMiddle,
    ttStartupNaturalPrefix,List.foldl,Layout.firstU,Layout.firstSigma,
    Layout.firstV,Layout.childSigma,Layout.childV,Layout.frames,pow_two]


theorem ttStartup_third (s : State ttProgram) (L : Layout)
    (hd : s.natural 0=L.order) :
    (ordinaryStep ttProgram)^[7] (ttStartupMiddle s L 11 131 (by decide))=
      ttStartupMiddle s L 18 138 (by decide) := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,Function.update_idem,dite_eq_ite,
    ttStartup_labels,ttStartup_naturals,ttStartup_reals,Function.iterate_succ_apply',ordinaryStep,
    hd,ttStartup_code131,ttStartup_code132,ttStartup_code133,ttStartup_code134,ttStartup_code135,ttStartup_code136,ttStartup_code137,ttStartupMiddle,
    ttStartupNaturalPrefix,List.foldl,Layout.metadata,Layout.workA,
    Layout.workB,Layout.store,pow_two]


theorem ttStartup_fourth (s : State ttProgram) (L : Layout)
    (hd : s.natural 0=L.order) (hz : s.natural 127=0) :
    (ordinaryStep ttProgram)^[6] (ttStartupMiddle s L 18 138 (by decide))=ttStartupEnd s L := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,Function.update_idem,dite_eq_ite,
    ttStartup_labels,ttStartup_naturals,ttStartup_reals,Function.iterate_succ_apply',ordinaryStep,
    hd,hz,ttStartup_code138,ttStartup_code139,ttStartup_code140,ttStartup_code141,ttStartup_code142,ttStartup_code143,ttStartupMiddle,
    ttStartupNaturalPrefix,ttStartupEnd,ttStartupNatural,List.foldl]


theorem ttStartup_steps (s : State ttProgram) (L : Layout)
    (hl : s.label=119) (hs : s.status=.running)
    (hd : s.natural 0=L.order) (hn : s.natural 2=L.entries) (hz : s.natural 127=0) :
    (ordinaryStep ttProgram)^[25] s=ttStartupEnd s L := by
  rw [show 25=6+(7+(6+6)) by omega,Function.iterate_add_apply,
    Function.iterate_add_apply,Function.iterate_add_apply,ttStartup_first s L hl hs hd hn,
    ttStartup_second,ttStartup_third s L hd,ttStartup_fourth s L hd hz]


structure TTAllocationRegisters (L : Layout) (s : State ttProgram) : Prop where
  order : s.natural 0=L.order
  entries : s.natural 64=L.entries
  square : s.natural 66=L.entries^2
  input : s.natural 92=L.input
  firstU : s.natural 72=L.firstU
  firstSigma : s.natural 73=L.firstSigma
  firstV : s.natural 74=L.firstV
  childSigma : s.natural 103=L.childSigma
  childV : s.natural 104=L.childV
  frames : s.natural 67=L.frames
  metadata : s.natural 68=L.metadata
  workA : s.natural 69=L.workA
  workB : s.natural 70=L.workB
  store : s.natural 71=L.store
  four : s.natural 125=4
  one : s.natural 126=1
  zero : s.natural 127=0

theorem ttStartup_allocation (s : State ttProgram) (L : Layout)
    (hd : s.natural 0=L.order) (hz : s.natural 127=0) :
    TTAllocationRegisters L (ttStartupEnd s L) := by
  constructor
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,Function.update_idem,dite_eq_ite,
    ttStartup_labels,ttStartup_naturals,ttStartup_reals,ttStartupEnd,ttStartupNatural,List.foldl,hd,hz]


theorem ttStartup_decoder (s : State ttProgram) (L : Layout) (value : ℕ)
    (hd : s.natural 0=L.order) (hm : s.memory 0=(value : ℝ)) :
    ttHeaderEmbedding.Relates
      (headerProductDecodeState s.memory L.order L.order 1 value (s.real 1))
      (ttStartupEnd s L) := by
  constructor
  · rfl
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,Function.update_idem,dite_eq_ite,
    ttStartup_labels,ttStartup_naturals,ttStartup_reals,ttStartupEnd,headerProductDecodeState,
      ttHeaderEmbedding,ttHeaderEmbeddingStage6,ttHeaderEmbeddingStage5,
      ttHeaderEmbeddingStage4,ttHeaderEmbeddingStage3,ttHeaderEmbeddingStage2,
      ttHeaderEmbeddingStage1,RoutineEmbedding.throughInstalledBank,installedBankEmbedding,
      ttHeaderRegisters,offsetBankRegisters,Function.comp_apply,headerProductProgram,ttControllerProgram,hm]
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,Function.update_idem,dite_eq_ite,
    ttStartup_labels,ttStartup_naturals,ttStartup_reals,ttStartupEnd,ttStartupNatural,List.foldl,
      headerProductDecodeState,ttHeaderEmbedding,ttHeaderEmbeddingStage6,
      ttHeaderEmbeddingStage5,ttHeaderEmbeddingStage4,ttHeaderEmbeddingStage3,
      ttHeaderEmbeddingStage2,ttHeaderEmbeddingStage1,RoutineEmbedding.throughInstalledBank,
      installedBankEmbedding,ttHeaderRegisters,offsetBankRegisters,Function.comp_apply,headerProductProgram,ttControllerProgram,hd]
  · rfl
  · rfl


theorem ttStartup_flags (s : State ttProgram) (L : Layout) :
    (ttStartupEnd s L).natural 76=0 ∧ (ttStartupEnd s L).natural 97=1 := by
  constructor
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,Function.update_idem,dite_eq_ite,
    ttStartup_labels,ttStartup_naturals,ttStartup_reals,ttStartupEnd,ttStartupNatural,List.foldl]

/-- The actual finite caller block allocates its ordinary natural pointers and
loads the first mode header before the decoder. Every legal trace follows it,
with exactly the same old tensor memory and at most25 added actual charges. -/
theorem ttStartup_run_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (L : Layout) (value : ℕ)
    (hl : (trace.state offset).label=119) (hs : (trace.state offset).status=.running)
    (hd : (trace.state offset).natural 0=L.order)
    (hn : (trace.state offset).natural 2=L.entries)
    (hz : (trace.state offset).natural 127=0)
    (hm : (trace.state offset).memory 0=(value : ℝ)) :
    ttHeaderEmbedding.Relates
      (headerProductDecodeState (trace.state offset).memory L.order L.order 1 value
        ((trace.state offset).real 1)) (trace.state (offset+25)) ∧
    TTAllocationRegisters L (trace.state (offset+25)) ∧
    (trace.state (offset+25)).natural 76=0 ∧
    (trace.state (offset+25)).natural 97=1 ∧
    CostThrough ttProgram trace (offset+25)≤CostThrough ttProgram trace offset+25 := by
  have heq := ttStartup_steps (trace.state offset) L hl hs hd hn hz
  have hrunning : ((ordinaryStep ttProgram)^[25] (trace.state offset)).status=.running := by
    rw [heq]
    rfl
  obtain ⟨hstate,hcost⟩ := trace_scalar_block_at ht offset 25
    (fun k hk _ => ordinary_nosvd_prefix_of_running _ _ hrunning k hk)
  have hfinish := hstate.trans heq
  obtain ⟨hzero,htag⟩ := ttStartup_flags (trace.state offset) L
  refine ⟨?_,?_,?_,?_,hcost⟩
  · rw [hfinish]
    exact ttStartup_decoder _ _ _ hd hm
  · rw [hfinish]
    exact ttStartup_allocation _ _ hd hz
  · rw [hfinish]
    exact hzero
  · rw [hfinish]
    exact htag

#assert_trust kernel ordinary_nosvd_prefix_of_running
#assert_trust kernel ttStartup_steps
#assert_trust kernel ttStartup_allocation
#assert_trust kernel ttStartup_decoder
#assert_trust kernel ttStartup_flags
#assert_trust kernel ttStartup_run_at
#print axioms ttStartup_steps
#print axioms ttStartup_run_at
end NLA.Proofs.TR04
