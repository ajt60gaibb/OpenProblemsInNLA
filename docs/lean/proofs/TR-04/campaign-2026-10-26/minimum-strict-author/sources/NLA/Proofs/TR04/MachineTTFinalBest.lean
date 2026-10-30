import NLA.Proofs.TR04.MachineTTFinalScalar

/-! Actual last candidate test, fixed selector bank and final halt. The minimum
is computed by reads/subtraction/squaring/lessReal over every stored array. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def ttBestData (s : State ttProgram) : BestCandidateData :=
  ⟨s.natural 75,s.natural 64,s.natural 92,s.natural 71,s.memory⟩

def ttBestScratch (s : State ttProgram) : BestCandidateScratch :=
  ⟨0,0,0,0,0,fun i => s.real (ttBestEmbedding.reals (Fin.castLE (by decide) i))⟩

def TTBestFinalKept (j : Fin 128) : Prop := (j.val<49 ∨ 61<j.val) ∧ j≠83

theorem ttBest_relates (s : State ttProgram) (hs : s.status=.running) :
    ttBestEmbedding.Relates (bestCandidateStart (ttBestData s) (s.real 12) (ttBestScratch s)) (ttBestEntry s) := by
  constructor
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i <;> first | rfl | simp [bestCandidateStart,bestCandidateLoopState,bestCandidateState,
      ttBestData,BestCandidateData.candidateBase]
    all_goals rfl
  · rfl
  · exact hs

theorem ttBestEntry_kept (s : State ttProgram) (j : Fin 128) (hj : j.val<49 ∨ 61<j.val) :
    (ttBestEntry s).natural j=s.natural j := by
  have hne : ∀ k : Fin 128,49≤k.val → k.val≤61 → j≠k := by
    intro k hk hk' he
    have hv := congrArg Fin.val he
    omega
  simp only [ttBestEntry,ttBestSetupNatural,
    Function.update_of_ne (hne 49 (by decide) (by decide)),Function.update_of_ne (hne 50 (by decide) (by decide)),
    Function.update_of_ne (hne 51 (by decide) (by decide)),Function.update_of_ne (hne 52 (by decide) (by decide)),
    Function.update_of_ne (hne 53 (by decide) (by decide)),Function.update_of_ne (hne 54 (by decide) (by decide)),
    Function.update_of_ne (hne 55 (by decide) (by decide)),Function.update_of_ne (hne 56 (by decide) (by decide)),
    Function.update_of_ne (hne 57 (by decide) (by decide)),Function.update_of_ne (hne 58 (by decide) (by decide)),
    Function.update_of_ne (hne 59 (by decide) (by decide)),Function.update_of_ne (hne 60 (by decide) (by decide)),
    Function.update_of_ne (hne 61 (by decide) (by decide))]

/-- Every actual full-candidate trace halts with a genuine least-error index
and its stored output base. The incoming error value is arbitrary. -/
theorem ttBest_halt_minimum_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=189) (hs : (trace.state offset).status=.running)
    (hz : (trace.state offset).natural 127=0)
    (hp : 0<(trace.state offset).natural 75)
    (hfull : (trace.state offset).natural 75≤(trace.state offset).natural 76) :
    let s := trace.state offset
    let time := offset+(bestCandidateReturnTime (ttBestData s)+17)
    ∃ winner < s.natural 75,
      (trace.state time).status=.halted (s.natural 71+winner*s.natural 64) ∧
      (trace.state time).natural 83=s.natural 71+winner*s.natural 64 ∧
      (trace.state time).natural 54=winner ∧
      (trace.state time).real 12=(ttBestData s).candidateError winner ∧
      (∀ i<s.natural 75,(ttBestData s).candidateError winner≤(ttBestData s).candidateError i) ∧
      (trace.state time).memory=s.memory ∧
      (∀ j : Fin 128,TTBestFinalKept j → (trace.state time).natural j=s.natural j) ∧
      (∀ j : Fin 16,(j.val<9 ∨ 12<j.val) → (trace.state time).real j=s.real j) ∧
      CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+
        67*(s.natural 75+s.natural 64+1)^2 := by
  let s := trace.state offset
  obtain ⟨he,hc0⟩ := ttScalar_finish_at ht offset 15 (ttBestEntry s) (ttBest_final_branch s hl hs hz hfull) hs
  have hrel : ttBestEmbedding.Relates (bestCandidateStart (ttBestData s) (s.real 12) (ttBestScratch s))
      (trace.state (offset+15)) := by rw [he]; exact ttBest_relates s hs
  obtain ⟨winner,hw,result,hr,hmin,hc1,hpoly,hreal,hnat⟩ := ttBestEmbedding.bestCandidate_run_at
    (ttBestData s) hp (s.real 12) (ttBestScratch s) ht (offset+15) hrel
  let mid := offset+15+bestCandidateReturnTime (ttBestData s)
  have hrl : (trace.state mid).label=114 := hr.label
  obtain ⟨hf,hc2⟩ := ttBest_halt_at ht mid hrl hr.status
  have hb : (trace.state mid).natural 55=s.natural 71+winner*s.natural 64 := hr.natural_apply 6
  have hwinner : (trace.state mid).natural 54=winner := hr.natural_apply 5
  have herr : (trace.state mid).real 12=(ttBestData s).candidateError winner := hr.real_apply 3
  have htime : mid+2=offset+(bestCandidateReturnTime (ttBestData s)+17) := by dsimp [mid]; omega
  refine ⟨winner,hw,?_,?_,?_,?_,hmin,?_,?_,?_,?_⟩
  · rw [← htime,hf]; exact congrArg Status.halted hb
  · rw [← htime,hf]; exact hb
  · rw [← htime,hf]; exact hwinner
  · rw [← htime,hf]; exact herr
  · rw [← htime,hf]; exact hr.memory
  · intro j hj
    rw [← htime,hf]
    change Function.update (trace.state mid).natural 83 ((trace.state mid).natural 55) j=s.natural j
    rw [Function.update_of_ne hj.2]
    have ho := hnat j (by
      intro i hij
      have hv := congrArg Fin.val hij
      change j.val=49+i.val at hv
      have hi : i.val<13 := i.isLt
      rcases hj.1 with h | h <;> omega)
    change (trace.state mid).natural j=(trace.state (offset+15)).natural j at ho
    rw [ho,he]
    exact ttBestEntry_kept s j hj.1
  · intro j hj
    rw [← htime,hf]
    change (trace.state mid).real j=s.real j
    have ho := hreal j (by
      intro i hij
      have hv := congrArg Fin.val hij
      change j.val=9+i.val at hv
      have hi : i.val<4 := i.isLt
      omega)
    change (trace.state mid).real j=(trace.state (offset+15)).real j at ho
    rw [ho,he]
    rfl
  · have hpos : 1≤(s.natural 75+s.natural 64+1)^2 := by nlinarith
    rw [← htime]
    dsimp [mid,ttBestData,s] at hc0 hpoly hc2 ⊢
    nlinarith

#assert_trust kernel ttBest_relates
#assert_trust kernel ttBestEntry_kept
#assert_trust kernel ttBest_halt_minimum_at
#print axioms ttBest_halt_minimum_at
end NLA.Proofs.TR04
