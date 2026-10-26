import NLA.Proofs.TR04.MachineTTProgramFacts
import Mathlib.Tactic.FinCases

/-! Actual finite header return dispatch. Every rejected tag executes its
literal natural/equality pair; handler choice is a fixed finite syntax map. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def ttHeaderHandler (k : Fin 11) : Fin 512 :=
  ![119,144,150,157,214,222,230,295,303,311,319] k

def ttHeaderTagLabel (k : Fin 11) : Fin 512 := ⟨372 + 2 * k.val, by have := k.isLt; omega⟩
def ttHeaderCompareLabel (k : Fin 11) : Fin 512 := ⟨373 + 2 * k.val, by have := k.isLt; omega⟩
def ttHeaderRejectLabel (k : Fin 11) : Fin 512 :=
  if h : k.val < 10 then ttHeaderTagLabel ⟨k.val + 1, by omega⟩ else 371

 theorem ttProgram_code_header_tag (k : Fin 11) :
    ttProgram.code (ttHeaderTagLabel k) = .natural 123 k.val (ttHeaderCompareLabel k) := by
  rw [ttProgram_code_caller _ (by dsimp [ttHeaderTagLabel]; omega)]
  fin_cases k <;> rfl

 theorem ttProgram_code_header_compare (k : Fin 11) :
    ttProgram.code (ttHeaderCompareLabel k) =
      .equalNat 97 123 (ttHeaderHandler k) (ttHeaderRejectLabel k) := by
  rw [ttProgram_code_caller _ (by dsimp [ttHeaderCompareLabel]; omega)]
  fin_cases k <;> rfl

 def ttHeaderRejectedState (s : State ttProgram) (j : Fin 11) : State ttProgram :=
  { s with label := ttHeaderRejectLabel j, natural := Function.update s.natural 123 j.val }

 def ttHeaderDispatchEnd (s : State ttProgram) (k : Fin 11) : State ttProgram :=
  { s with label := ttHeaderHandler k, natural := Function.update s.natural 123 k.val }

 theorem ttHeader_reject_steps (s : State ttProgram) (j k : Fin 11)
    (hj : j.val < k.val) (hl : s.label = ttHeaderTagLabel j)
    (hs : s.status = .running) (htag : s.natural 97 = k.val) :
    (ordinaryStep ttProgram)^[2] s = ttHeaderRejectedState s j := by
  have hne : k.val ≠ j.val := by omega
  have hu : Function.update s.natural 123 j.val 97 = k.val := by
    rw [Function.update_of_ne (by decide)]
    exact htag
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Function.iterate_succ_apply',ordinaryStep,hl,hs,
    ttProgram_code_header_tag,ttProgram_code_header_compare,ttHeaderRejectedState,hu,hne]
  all_goals rfl

 theorem ttHeader_accept_steps (s : State ttProgram) (k : Fin 11)
    (hl : s.label = ttHeaderTagLabel k) (hs : s.status = .running)
    (htag : s.natural 97 = k.val) :
    (ordinaryStep ttProgram)^[2] s = ttHeaderDispatchEnd s k := by
  have hu : Function.update s.natural 123 k.val 97 = k.val := by
    rw [Function.update_of_ne (by decide)]
    exact htag
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Function.iterate_succ_apply',ordinaryStep,hl,hs,
    ttProgram_code_header_tag,ttProgram_code_header_compare,ttHeaderDispatchEnd,hu]
  all_goals rfl

 theorem ttHeader_scan_steps (remaining : ℕ) (k j : Fin 11)
    (hj : j.val + remaining = k.val) (s : State ttProgram)
    (hl : s.label = ttHeaderTagLabel j) (hs : s.status = .running)
    (htag : s.natural 97 = k.val) :
    (ordinaryStep ttProgram)^[2 * remaining + 2] s = ttHeaderDispatchEnd s k := by
  induction remaining generalizing j s with
  | zero =>
    have he : j = k := Fin.ext (by omega)
    subst j
    exact ttHeader_accept_steps s k hl hs htag
  | succ remaining ih =>
    have hjk : j.val < k.val := by omega
    have hj10 : j.val < 10 := by have := k.isLt; omega
    let next : Fin 11 := ⟨j.val + 1, by omega⟩
    have hnext : ttHeaderRejectLabel j = ttHeaderTagLabel next := by
      simp only [ttHeaderRejectLabel,dif_pos hj10,next]
    have hn : next.val + remaining = k.val := by dsimp [next]; omega
    have hstateLabel : (ttHeaderRejectedState s j).label = ttHeaderTagLabel next := hnext
    have hstateTag : (ttHeaderRejectedState s j).natural 97 = k.val := by
      change Function.update s.natural 123 j.val 97 = k.val
      rw [Function.update_of_ne (by decide)]
      exact htag
    rw [show 2 * (remaining + 1) + 2 = (2 * remaining + 2) + 2 by omega,
      Function.iterate_add_apply,ttHeader_reject_steps s j k hjk hl hs htag,
      ih next hn (ttHeaderRejectedState s j) hstateLabel hs hstateTag]
    simp only [ttHeaderDispatchEnd,ttHeaderRejectedState,Function.update_idem]

 theorem ttHeaderDispatch_steps (s : State ttProgram) (k : Fin 11)
    (hl : s.label = 10) (hs : s.status = .running) (htag : s.natural 97 = k.val) :
    (ordinaryStep ttProgram)^[2 * k.val + 3] s = ttHeaderDispatchEnd s k := by
  have hjump : ordinaryStep ttProgram s = { s with label := ttHeaderTagLabel 0 } := by
    simp only [ordinaryStep,hs,hl,ttProgram_code_header_exit]
    rfl
  rw [show 2*k.val+3=(2*k.val+2)+1 by omega,Function.iterate_add_apply]
  simp only [Function.iterate_one,hjump]
  have hh := ttHeader_scan_steps k.val k 0 (by simp) {s with label := ttHeaderTagLabel 0}
    rfl hs htag
  exact hh

/-- If an ordinary finite prefix is still running, no SVD opcode occurred:
ordinaryStep fails at an SVD, and failure is absorbing. -/
 theorem ttOrdinary_nosvd_prefix_of_running {P : Program} (s : State P) (n : ℕ)
    (hn : ((ordinaryStep P)^[n] s).status=.running) (k : ℕ) (hk : k<n) :
    instructionIsSVD (P.code ((ordinaryStep P)^[k] s).label)=false := by
  have hs := ordinary_running_prefix s n hn k hk.le
  have hsnext := ordinary_running_prefix s n hn (k+1) (by omega)
  rw [Function.iterate_succ_apply'] at hsnext
  cases hi : P.code ((ordinaryStep P)^[k] s).label <;> simp only [instructionIsSVD]
  simp [ordinaryStep,hs,hi] at hsnext

 theorem ttHeaderDispatch_run_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (k : Fin 11)
    (hl : (trace.state offset).label = 10) (hs : (trace.state offset).status = .running)
    (htag : (trace.state offset).natural 97 = k.val) :
    trace.state (offset + (2*k.val+3)) = ttHeaderDispatchEnd (trace.state offset) k ∧
      CostThrough ttProgram trace (offset + (2*k.val+3)) ≤
        CostThrough ttProgram trace offset + (2*k.val+3) := by
  have he := ttHeaderDispatch_steps (trace.state offset) k hl hs htag
  have hn : ((ordinaryStep ttProgram)^[2*k.val+3] (trace.state offset)).status=.running := by
    rw [he]; exact hs
  obtain ⟨hv,hc⟩ := trace_scalar_block_at ht offset (2*k.val+3)
    (fun j hj _ => ttOrdinary_nosvd_prefix_of_running _ _ hn j hj)
  exact ⟨hv.trans he,hc⟩

theorem ttHeaderDispatch_fields_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (k : Fin 11)
    (hl : (trace.state offset).label = 10) (hs : (trace.state offset).status = .running)
    (htag : (trace.state offset).natural 97 = k.val) :
    let time := offset + (2*k.val+3)
    (trace.state time).label = ttHeaderHandler k ∧
    (trace.state time).status = .running ∧
    (trace.state time).memory = (trace.state offset).memory ∧
    (trace.state time).real = (trace.state offset).real ∧
    (trace.state time).natural 123 = k.val ∧
    (∀ i : Fin 128, i ≠ 123 → (trace.state time).natural i = (trace.state offset).natural i) ∧
    CostThrough ttProgram trace time ≤ CostThrough ttProgram trace offset + (2*k.val+3) := by
  obtain ⟨he,hc⟩ := ttHeaderDispatch_run_at ht offset k hl hs htag
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hc⟩
  · rw [he]; rfl
  · rw [he]; exact hs
  · rw [he]; rfl
  · rw [he]; rfl
  · rw [he]
    change Function.update (trace.state offset).natural 123 k.val 123 = k.val
    exact Function.update_self _ _ _
  · intro i hi
    rw [he]
    exact Function.update_of_ne hi _ _

#assert_trust kernel ttHeaderDispatch_fields_at
#print axioms ttHeaderDispatch_fields_at
#assert_trust kernel ttHeaderDispatch_steps
#assert_trust kernel ttHeaderDispatch_run_at
#print axioms ttHeaderDispatch_steps
#print axioms ttHeaderDispatch_run_at
end NLA.Proofs.TR04
