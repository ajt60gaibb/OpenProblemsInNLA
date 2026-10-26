import NLA.Proofs.TR04.MachineTTInitializationTrace
import NLA.Proofs.TR04.MachineBestCandidateCallable

/-! Literal final candidate-store and minimum-selector caller instructions. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
private theorem code347 : ttProgram.code 347 = .mulNat 123 76 64 348 := rfl
private theorem code348 : ttProgram.code 348 = .addNat 123 71 123 349 := rfl
private theorem code349 : ttProgram.code 349 = .copyNat 21 127 350 := rfl
private theorem code350 : ttProgram.code 350 = .copyNat 22 64 351 := rfl
private theorem code351 : ttProgram.code 351 = .copyNat 23 89 352 := rfl
private theorem code352 : ttProgram.code 352 = .copyNat 24 123 353 := rfl
private theorem code353 : ttProgram.code 353 = .copyNat 25 123 354 := rfl
private theorem code354 : ttProgram.code 354 = .jump 33 := rfl
private theorem code355 : ttProgram.code 355 = .increment 76 356 := rfl
private theorem code356 : ttProgram.code 356 = .jump 189 := rfl
private theorem code357 : ttProgram.code 357 = .copyNat 49 75 358 := rfl
private theorem code358 : ttProgram.code 358 = .copyNat 50 64 359 := rfl
private theorem code359 : ttProgram.code 359 = .copyNat 51 92 360 := rfl
private theorem code360 : ttProgram.code 360 = .copyNat 52 71 361 := rfl
private theorem code361 : ttProgram.code 361 = .copyNat 53 127 362 := rfl
private theorem code362 : ttProgram.code 362 = .copyNat 54 127 363 := rfl
private theorem code363 : ttProgram.code 363 = .copyNat 55 71 364 := rfl
private theorem code364 : ttProgram.code 364 = .copyNat 56 71 365 := rfl
private theorem code365 : ttProgram.code 365 = .copyNat 57 127 366 := rfl
private theorem code366 : ttProgram.code 366 = .copyNat 58 127 367 := rfl
private theorem code367 : ttProgram.code 367 = .copyNat 59 127 368 := rfl
private theorem code368 : ttProgram.code 368 = .copyNat 60 127 369 := rfl
private theorem code369 : ttProgram.code 369 = .copyNat 61 127 370 := rfl
private theorem code370 : ttProgram.code 370 = .jump 89 := rfl
private theorem code371 : ttProgram.code 371 = .halt 83 := rfl

def ttCandidateStoreBase (s : State ttProgram) : ℕ := s.natural 71 + s.natural 76 * s.natural 64

def ttCandidateCopyEntry (s : State ttProgram) : State ttProgram :=
  { s with
    label := 33
    natural := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update s.natural 123 (ttCandidateStoreBase s)) 21 0)
        22 (s.natural 64)) 23 (s.natural 89)) 24 (ttCandidateStoreBase s)) 25 (ttCandidateStoreBase s) }

def ttCandidateCopyReturn (s : State ttProgram) : State ttProgram :=
  { s with label := 189, natural := Function.update s.natural 76 (s.natural 76+1) }

def ttBestSetupNatural (s : State ttProgram) : Fin 128 → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (s.natural) 49 (s.natural 75)) 50 (s.natural 64)) 51 (s.natural 92)) 52 (s.natural 71)) 53 (0)) 54 (0)) 55 (s.natural 71)) 56 (s.natural 71)) 57 (0)) 58 (0)) 59 (0)) 60 (0)) 61 (0)

def ttBestEntry (s : State ttProgram) : State ttProgram :=
  { s with label := 89, natural := ttBestSetupNatural s }

def ttBestHaltEnd (s : State ttProgram) : State ttProgram :=
  { s with
    label := 371
    natural := Function.update s.natural 83 (s.natural 55)
    status := .halted (s.natural 55) }

theorem ttCandidate_copy_setup (s : State ttProgram) (hl : s.label=347)
    (hs : s.status=.running) (hz : s.natural 127=0) :
    (ordinaryStep ttProgram)^[8] s = ttCandidateCopyEntry s := by
  apply machineState_ext
  all_goals simp (disch := decide) only [Function.iterate_zero_apply,Function.iterate_succ_apply',
    ordinaryStep,Function.update_apply,Function.update_idem,
    if_pos,if_neg,hl,hs,hz,code347,code348,code349,code350,code351,code352,code353,code354,
    ttCandidateCopyEntry,ttCandidateStoreBase]

theorem ttCandidate_copy_return (s : State ttProgram) (hl : s.label=39)
    (hs : s.status=.running) : (ordinaryStep ttProgram)^[3] s = ttCandidateCopyReturn s := by
  apply machineState_ext
  all_goals simp (disch := decide) only [Function.iterate_zero_apply,Function.iterate_succ_apply',
    ordinaryStep,hl,hs,
    ttProgram_code_copy_exit,code355,code356,ttCandidateCopyReturn]

theorem ttBest_setup (s : State ttProgram) (hl : s.label=357)
    (hs : s.status=.running) (hz : s.natural 127=0) :
    (ordinaryStep ttProgram)^[14] s = ttBestEntry s := by
  apply machineState_ext
  all_goals simp (disch := decide) only [Function.iterate_zero_apply,Function.iterate_succ_apply',
    ordinaryStep,Function.update_apply,
    if_neg,hl,hs,hz,code357,code358,code359,code360,code361,code362,code363,code364,
    code365,code366,code367,code368,code369,code370,ttBestEntry,ttBestSetupNatural]

theorem ttBest_final_branch (s : State ttProgram) (hl : s.label=189)
    (hs : s.status=.running) (hz : s.natural 127=0) (hfull : s.natural 75≤s.natural 76) :
    (ordinaryStep ttProgram)^[15] s = ttBestEntry s := by
  have hc : ttProgram.code 189 = .lessNat 76 75 190 357 := rfl
  have hstep : ordinaryStep ttProgram s = {s with label := 357} := by
    simp only [ordinaryStep,hs,hl,hc,if_neg (show ¬s.natural 76<s.natural 75 by omega)]
  rw [show 15=14+1 by decide,Function.iterate_add_apply,Function.iterate_one,hstep]
  exact ttBest_setup {s with label := 357} rfl hs hz

theorem ttBest_halt_steps (s : State ttProgram) (hl : s.label=114) (hs : s.status=.running) :
    (ordinaryStep ttProgram)^[2] s = ttBestHaltEnd s := by
  apply machineState_ext
  all_goals simp (disch := decide) only [Function.iterate_zero_apply,Function.iterate_succ_apply',
    ordinaryStep,Function.update_apply,if_pos,hl,hs,
    ttProgram_code_best_exit,code371,ttBestHaltEnd]

theorem ttBest_halt_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=114) (hs : (trace.state offset).status=.running) :
    trace.state (offset+2)=ttBestHaltEnd (trace.state offset) ∧
      CostThrough ttProgram trace (offset+2)≤CostThrough ttProgram trace offset+2 := by
  obtain ⟨hv,hc⟩ := trace_scalar_block_at ht offset 2 (by
    intro k hk _
    interval_cases k
    · simp only [Function.iterate_zero_apply,hl,ttProgram_code_best_exit,instructionIsSVD]
    · simp only [Function.iterate_one,ordinaryStep,hs,hl,ttProgram_code_best_exit,code371,instructionIsSVD])
  exact ⟨hv.trans (ttBest_halt_steps _ hl hs),hc⟩

#assert_trust kernel ttCandidate_copy_setup
#assert_trust kernel ttCandidate_copy_return
#assert_trust kernel ttBest_setup
#assert_trust kernel ttBest_final_branch
#assert_trust kernel ttBest_halt_steps
#assert_trust kernel ttBest_halt_at
#print axioms ttBest_halt_at
end NLA.Proofs.TR04
