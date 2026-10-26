import NLA.Proofs.TR04.MachineTTReverseScalar

/-! Actual single-natural metadata decoding through the shared header bank,
followed by its literal tag7--10 caller dispatch. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
private theorem ttReverseRead_naturals : ttProgram.extraNatRegisters=127 := rfl
private theorem ttReverseRead_reals : ttProgram.realRegisters=16 := rfl

theorem ttReverseHeader_real_map (i : Fin 2) :
    ttHeaderEmbedding.reals i=(⟨i.val,by have := i.isLt;omega⟩ : Fin 16) := by
  apply Fin.ext
  change 0+i.val=i.val
  omega

theorem ttReverseHeader_natural_map (i : Fin 4) :
    ttHeaderEmbedding.naturals i=(⟨i.val,by have := i.isLt;omega⟩ : Fin 128) := by
  apply Fin.ext
  change 0+i.val=i.val
  omega

def ttReverseHeaderEnd (s : State ttProgram) (d value : ℕ) : State ttProgram where
  label := 10
  real := Function.update (Function.update s.real (0 : Fin 16) (value : ℝ)) (1 : Fin 16) (value : ℝ)
  natural := Function.update (Function.update (Function.update s.natural
    (1 : Fin 128) (d+1)) (2 : Fin 128) value) (3 : Fin 128) value
  memory := s.memory
  status := .running

 theorem ttReverseHeader_real_outside {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (memory : ℕ → ℝ)
    (d value : ℕ) (scratch : ℝ)
    (he : ttHeaderEmbedding.Relates
      (headerProductDecodeState memory d d 1 value scratch) (trace.state offset))
    (i : Fin 16) (hi : 2 ≤ i.val) :
    (trace.state (offset+(3*value+5))).real i=(trace.state offset).real i := by
  have hr : ((ordinaryStep headerProductProgram)^[3*value+5]
      (headerProductDecodeState memory d d 1 value scratch)).status=.running := by
    rw [headerSingle_return];rfl
  apply ttHeaderEmbedding.scalar_trace_real_outside _ he (legalTrace_shift ht offset) _
    (ordinary_nohalt_prefix_of_running _ _ hr) (fun _ _ => headerProductProgram_scalar _) i
  intro j hj
  have hv := congrArg Fin.val hj
  change i.val=0+j.val at hv
  have hlt := j.isLt
  change j.val<2 at hlt
  omega

 theorem ttReverseHeader_full_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (memory : ℕ → ℝ)
    (d value : ℕ) (scratch : ℝ)
    (he : ttHeaderEmbedding.Relates
      (headerProductDecodeState memory d d 1 value scratch) (trace.state offset)) :
    trace.state (offset+(3*value+5))=ttReverseHeaderEnd (trace.state offset) d value ∧
    CostThrough ttProgram trace (offset+(3*value+5))≤CostThrough ttProgram trace offset+(3*value+5) := by
  obtain ⟨hr,hn,hcost⟩ := ttHeaderSingle_full_at ht offset memory d value scratch he
  refine ⟨?_,hcost⟩
  apply machineState_ext
  · exact hr.label
  · funext i
    by_cases h0 : i.val=0
    · have hi : i=(0 : Fin 16) := Fin.ext h0
      subst i
      have hh := hr.real_apply (0 : Fin 2)
      change (trace.state (offset+(3*value+5))).real (0 : Fin 16)=(value : ℝ) at hh
      simpa (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
        -Fin.val_eq_zero_iff,ttReverseHeaderEnd,Fin.ext_iff] using hh
    · by_cases h1 : i.val=1
      · have hi : i=(1 : Fin 16) := Fin.ext h1
        subst i
        have hh := hr.real_apply (1 : Fin 2)
        change (trace.state (offset+(3*value+5))).real (1 : Fin 16)=(value : ℝ) at hh
        simpa only [ttReverseHeaderEnd,Function.update_self] using hh
      · have hi : 2 ≤ i.val := by omega
        rw [ttReverseHeader_real_outside ht offset memory d value scratch he i hi]
        have hi0 : i≠(0 : Fin 16) := fun h => h0 (congrArg Fin.val h)
        have hi1 : i≠(1 : Fin 16) := fun h => h1 (congrArg Fin.val h)
        simp only [ttReverseHeaderEnd,Function.update_of_ne hi0,Function.update_of_ne hi1]
  · funext i
    by_cases hsmall : i.val<4
    · obtain h0|h1|h2|h3 : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
      · have hi : i=(0 : Fin 128) := Fin.ext h0
        subst i
        have hh := (hr.natural_apply (0 : Fin 4)).trans (he.natural_apply (0 : Fin 4)).symm
        change (trace.state (offset+(3*value+5))).natural (0 : Fin 128)=(trace.state offset).natural (0 : Fin 128) at hh
        simpa (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
          -Fin.val_eq_zero_iff,ttReverseHeaderEnd,Fin.ext_iff] using hh
      · have hi : i=(1 : Fin 128) := Fin.ext h1
        subst i
        have hh := hr.natural_apply (1 : Fin 4)
        change (trace.state (offset+(3*value+5))).natural (1 : Fin 128)=d+1 at hh
        simpa (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
          -Fin.val_eq_zero_iff,ttReverseHeaderEnd,Fin.ext_iff] using hh
      · have hi : i=(2 : Fin 128) := Fin.ext h2
        subst i
        have hh := hr.natural_apply (2 : Fin 4)
        change (trace.state (offset+(3*value+5))).natural (2 : Fin 128)=value at hh
        simpa (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
          -Fin.val_eq_zero_iff,ttReverseHeaderEnd,Fin.ext_iff] using hh
      · have hi : i=(3 : Fin 128) := Fin.ext h3
        subst i
        have hh := hr.natural_apply (3 : Fin 4)
        change (trace.state (offset+(3*value+5))).natural (3 : Fin 128)=value at hh
        simpa only [ttReverseHeaderEnd,Function.update_self] using hh
    · rw [hn i (by omega)]
      have hi1 : i≠(1 : Fin 128) := by intro h;have := congrArg Fin.val h;change i.val=1 at this;omega
      have hi2 : i≠(2 : Fin 128) := by intro h;have := congrArg Fin.val h;change i.val=2 at this;omega
      have hi3 : i≠(3 : Fin 128) := by intro h;have := congrArg Fin.val h;change i.val=3 at this;omega
      simp only [ttReverseHeaderEnd,Function.update_of_ne hi1,Function.update_of_ne hi2,Function.update_of_ne hi3]
  · exact hr.memory.trans he.memory.symm
  · exact hr.status

 theorem ttReverseRead_relates (s : State ttProgram) (k : Fin 4) (value : ℕ)
    (hm : s.memory (ttReverseReadAddress s k)=(value : ℝ)) :
    ttHeaderEmbedding.Relates (headerProductDecodeState s.memory (s.natural 0) (s.natural 0) 1 value
      (s.real (1 : Fin 16))) (ttReverseReadEntry s k) := by
  constructor
  · rfl
  · funext i
    fin_cases i
    all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,ttReverseReadEntry,headerProductDecodeState,hm,ttReverseHeader_real_map]
  · funext i
    fin_cases i
    all_goals fin_cases k
    all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,ttReverseReadEntry,ttReverseReadNatural,
      headerProductDecodeState,ttReverseRead_naturals,ttReverseHeader_natural_map]
  · rfl
  · rfl

def ttReverseReadEnd (s : State ttProgram) (k : Fin 4) (value : ℕ) : State ttProgram :=
  ttHeaderDispatchEnd (ttReverseHeaderEnd (ttReverseReadEntry s k) (s.natural 0) value)
    ⟨7+k.val,by have := k.isLt;omega⟩

 theorem ttReverseRead_call_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (k : Fin 4) (value : ℕ)
    (hl : (trace.state offset).label=ttReverseReadLabel k) (hs : (trace.state offset).status=.running)
    (hfour : (trace.state offset).natural 125=4)
    (hm : (trace.state offset).memory (ttReverseReadAddress (trace.state offset) k)=(value : ℝ)) :
    let time := offset+8+(3*value+5)+(2*(7+k.val)+3)
    trace.state time=ttReverseReadEnd (trace.state offset) k value ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+8+(3*value+5)+(2*(7+k.val)+3) := by
  let s := trace.state offset
  obtain ⟨hv,hcost⟩ := ttScalar_finish_at ht offset 8 (ttReverseReadEntry s k)
    (ttReverseRead_steps s k hl hs hfour) rfl
  have he : ttHeaderEmbedding.Relates (headerProductDecodeState s.memory (s.natural 0) (s.natural 0) 1 value
      (s.real (1 : Fin 16))) (trace.state (offset+8)) := by
    rw [hv];exact ttReverseRead_relates s k value hm
  obtain ⟨hh,hc⟩ := ttReverseHeader_full_at ht (offset+8) s.memory (s.natural 0) value
    (s.real (1 : Fin 16)) he
  have hl' : (trace.state (offset+8+(3*value+5))).label=10 := by rw [hh];rfl
  have hs' : (trace.state (offset+8+(3*value+5))).status=.running := by rw [hh];rfl
  have ht' : (trace.state (offset+8+(3*value+5))).natural 97=7+k.val := by
    rw [hh,hv]
    simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,-Fin.val_eq_zero_iff,
      Fin.ext_iff,ttReverseHeaderEnd,ttReverseReadEntry,ttReverseReadNatural,ttReverseRead_naturals]
  obtain ⟨hd,hdcost⟩ := ttHeaderDispatch_run_at ht (offset+8+(3*value+5))
    ⟨7+k.val,by have := k.isLt;omega⟩ hl' hs' ht'
  refine ⟨?_,hdcost.trans (Nat.add_le_add_right (hc.trans (Nat.add_le_add_right hcost _)) _)⟩
  rw [hd,hh,hv]
  rfl

#assert_trust kernel ttReverseHeader_real_outside
#assert_trust kernel ttReverseHeader_full_at
#assert_trust kernel ttReverseRead_relates
#assert_trust kernel ttReverseRead_call_at
#print axioms ttReverseRead_call_at
end NLA.Proofs.TR04
