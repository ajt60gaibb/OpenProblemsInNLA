import NLA.Proofs.TR04.MachineTTProgramFacts
import NLA.Proofs.TR04.MachineThresholdScanSVD

/-! Literal caller blocks surrounding the first threshold-count bank.
These execute the fixed program and leave its memory untouched. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

instance ttFirstSelection_nonzero_reals : NeZero ttProgram.realRegisters := ⟨by decide⟩
private theorem code168 : ttProgram.code 168 = .lessNat 105 80 184 169 := rfl
attribute [local simp] code168

private theorem code169 : ttProgram.code 169 = .copyNat 122 80 170 := rfl
attribute [local simp] code169

private theorem code170 : ttProgram.code 170 = .decrement 122 171 := rfl
attribute [local simp] code170

private theorem code171 : ttProgram.code 171 = .addNat 122 73 122 172 := rfl
attribute [local simp] code171

private theorem code172 : ttProgram.code 172 = .read 7 122 173 := rfl
attribute [local simp] code172

private theorem code173 : ttProgram.code 173 = .castNat 13 127 174 := rfl
attribute [local simp] code173

private theorem code174 : ttProgram.code 174 = .lessReal 13 7 175 184 := rfl
attribute [local simp] code174

private theorem code175 : ttProgram.code 175 = .copyNat 42 105 176 := rfl
attribute [local simp] code175

private theorem code176 : ttProgram.code 176 = .copyNat 43 80 177 := rfl
attribute [local simp] code176

private theorem code177 : ttProgram.code 177 = .copyNat 44 73 178 := rfl
attribute [local simp] code177

private theorem code178 : ttProgram.code 178 = .jump 66 := rfl
attribute [local simp] code178

private theorem code179 : ttProgram.code 179 = .copyNat 77 46 180 := rfl
attribute [local simp] code179

private theorem code180 : ttProgram.code 180 = .copyNat 78 47 181 := rfl
attribute [local simp] code180

private theorem code181 : ttProgram.code 181 = .copyNat 79 48 182 := rfl
attribute [local simp] code181

private theorem code182 : ttProgram.code 182 = .copyNat 75 78 183 := rfl
attribute [local simp] code182

private theorem code183 : ttProgram.code 183 = .jump 189 := rfl
attribute [local simp] code183

private theorem code184 : ttProgram.code 184 = .copyNat 77 106 185 := rfl
attribute [local simp] code184

private theorem code185 : ttProgram.code 185 = .natural 78 1 186 := rfl
attribute [local simp] code185

private theorem code186 : ttProgram.code 186 = .natural 79 0 187 := rfl
attribute [local simp] code186

private theorem code187 : ttProgram.code 187 = .natural 75 1 188 := rfl
attribute [local simp] code187

private theorem code188 : ttProgram.code 188 = .jump 189 := rfl
attribute [local simp] code188

private theorem ne73_122 : (73 : Fin (ttProgram.extraNatRegisters + 1)) ≠ 122 := by decide
attribute [local simp] ne73_122

private theorem ne127_122 : (127 : Fin (ttProgram.extraNatRegisters + 1)) ≠ 122 := by decide
attribute [local simp] ne127_122

private theorem ne7_13 : (7 : Fin ttProgram.realRegisters) ≠ 13 := by decide
attribute [local simp] ne7_13

private theorem ne13_7 : (13 : Fin ttProgram.realRegisters) ≠ 7 := by decide
attribute [local simp] ne13_7

private theorem ne80_42 : (80 : Fin (ttProgram.extraNatRegisters + 1)) ≠ 42 := by decide
attribute [local simp] ne80_42

private theorem ne73_42 : (73 : Fin (ttProgram.extraNatRegisters + 1)) ≠ 42 := by decide
attribute [local simp] ne73_42

private theorem ne73_43 : (73 : Fin (ttProgram.extraNatRegisters + 1)) ≠ 43 := by decide
attribute [local simp] ne73_43

private theorem ne47_77 : (47 : Fin (ttProgram.extraNatRegisters + 1)) ≠ 77 := by decide
attribute [local simp] ne47_77

private theorem ne48_77 : (48 : Fin (ttProgram.extraNatRegisters + 1)) ≠ 77 := by decide
attribute [local simp] ne48_77

private theorem ne48_78 : (48 : Fin (ttProgram.extraNatRegisters + 1)) ≠ 78 := by decide
attribute [local simp] ne48_78

private theorem ne78_77 : (78 : Fin (ttProgram.extraNatRegisters + 1)) ≠ 77 := by decide
attribute [local simp] ne78_77

private theorem ne78_79 : (78 : Fin (ttProgram.extraNatRegisters + 1)) ≠ 79 := by decide
attribute [local simp] ne78_79

/-- The prefix fallback still has a positive cyclic modulus for the actual
frame-gather routine. Its take is zero, so its columns are exactly the prefix. -/
def ttFirstPrefixResult (s : State ttProgram) : State ttProgram :=
  { s with
    label := 189
    natural := (Function.update
      (Function.update (Function.update (Function.update s.natural 77 (s.natural 106)) 78 1) 79 0) 75 1) }

def ttFirstThresholdRead (s : State ttProgram) : State ttProgram :=
  { s with
    label := 175
    natural := Function.update s.natural 122 (s.natural 73 + (s.natural 80 - 1))
    real := Function.update (Function.update s.real 7
      (s.memory (s.natural 73 + (s.natural 80 - 1)))) 13 (s.natural 127 : ℝ) }

def ttFirstThresholdEntry (s : State ttProgram) : State ttProgram :=
  { s with
    label := 66
    natural := (Function.update
      (Function.update (Function.update s.natural 42 (s.natural 105)) 43 (s.natural 80)) 44 (s.natural 73)) }

def ttFirstCountResult (s : State ttProgram) : State ttProgram :=
  { s with
    label := 189
    natural := (Function.update
      (Function.update (Function.update (Function.update s.natural 77 (s.natural 46))
        78 (s.natural 47)) 79 (s.natural 48)) 75 (s.natural 47)) }

theorem ttFirstSelection_prefix_five (s : State ttProgram)
    (hl : s.label = 184) (hs : s.status = .running) :
    (ordinaryStep ttProgram)^[5] s = ttFirstPrefixResult s := by
  classical
  apply machineState_ext
  all_goals simp (disch := decide) only
    [
      Function.update_apply, Function.update_idem, dite_eq_ite, if_pos, if_neg, ne73_122, ne127_122, ne7_13, ne13_7, ne80_42, ne73_42, ne73_43, ne47_77, ne48_77, ne48_78, ne78_77, ne78_79,
      Function.iterate_zero_apply, Function.iterate_succ_apply', ordinaryStep, code168, code169, code170, code171, code172, code173, code174, code175, code176, code177, code178, code179, code180, code181, code182, code183, code184, code185, code186, code187, code188, hl, hs, ttFirstPrefixResult]

theorem ttFirstSelection_large_six (s : State ttProgram)
    (hl : s.label = 168) (hs : s.status = .running)
    (hr : s.natural 105 < s.natural 80) :
    (ordinaryStep ttProgram)^[6] s = ttFirstPrefixResult s := by
  classical
  have hfirst : ordinaryStep ttProgram s = {s with label := 184} := by
    simp (disch := decide) only
      [       ordinaryStep, hl, hs, hr, code168, if_pos, if_neg]
  rw [show 6 = 5 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one,
    hfirst]
  simpa only [ttFirstPrefixResult] using ttFirstSelection_prefix_five {s with label := 184} rfl hs

theorem ttFirstSelection_read_seven (s : State ttProgram)
    (hl : s.label = 168) (hs : s.status = .running)
    (hr : ¬s.natural 105 < s.natural 80)
    (ht : (s.natural 127 : ℝ) < s.memory (s.natural 73 + (s.natural 80 - 1))) :
    (ordinaryStep ttProgram)^[7] s = ttFirstThresholdRead s := by
  classical
  apply machineState_ext
  all_goals simp (disch := decide) only
    [
      Function.update_apply, Function.update_idem, dite_eq_ite, if_pos, if_neg, ne73_122, ne127_122, ne7_13, ne13_7, ne80_42, ne73_42, ne73_43, ne47_77, ne48_77, ne48_78, ne78_77, ne78_79,
      Function.iterate_zero_apply, Function.iterate_succ_apply', ordinaryStep, code168, code169, code170, code171, code172, code173, code174, code175, code176, code177, code178, code179, code180, code181, code182, code183, code184, code185, code186, code187, code188, hl, hs, hr, ht, ttFirstThresholdRead]

theorem ttFirstSelection_nonpositive_twelve (s : State ttProgram)
    (hl : s.label = 168) (hs : s.status = .running)
    (hr : ¬s.natural 105 < s.natural 80)
    (ht : ¬(s.natural 127 : ℝ) < s.memory (s.natural 73 + (s.natural 80 - 1))) :
    (ordinaryStep ttProgram)^[12] s =
      ttFirstPrefixResult {ttFirstThresholdRead s with label := 184} := by
  classical
  have hseven : (ordinaryStep ttProgram)^[7] s =
      {ttFirstThresholdRead s with label := 184} := by
    apply machineState_ext
    all_goals simp (disch := decide) only
      [
        Function.update_apply, Function.update_idem, dite_eq_ite, if_pos, if_neg, ne73_122, ne127_122, ne7_13, ne13_7, ne80_42, ne73_42, ne73_43, ne47_77, ne48_77, ne48_78, ne78_77, ne78_79,
      Function.iterate_zero_apply, Function.iterate_succ_apply', ordinaryStep, code168, code169, code170, code171, code172, code173, code174, code175, code176, code177, code178, code179, code180, code181, code182, code183, code184, code185, code186, code187, code188, hl, hs, hr, ht, ttFirstThresholdRead]
  rw [show 12 = 5 + 7 from rfl, Function.iterate_add_apply, hseven]
  exact ttFirstSelection_prefix_five {ttFirstThresholdRead s with label := 184} rfl hs

theorem ttFirstSelection_setup_four (s : State ttProgram)
    (hl : s.label = 175) (hs : s.status = .running) :
    (ordinaryStep ttProgram)^[4] s = ttFirstThresholdEntry s := by
  classical
  apply machineState_ext
  all_goals simp (disch := decide) only
    [
      Function.update_apply, Function.update_idem, dite_eq_ite, if_pos, if_neg, ne73_122, ne127_122, ne7_13, ne13_7, ne80_42, ne73_42, ne73_43, ne47_77, ne48_77, ne48_78, ne78_77, ne78_79,
      Function.iterate_zero_apply, Function.iterate_succ_apply', ordinaryStep, code168, code169, code170, code171, code172, code173, code174, code175, code176, code177, code178, code179, code180, code181, code182, code183, code184, code185, code186, code187, code188, hl, hs, ttFirstThresholdEntry]

theorem ttFirstSelection_return_six (s : State ttProgram)
    (hl : s.label = 88) (hs : s.status = .running) :
    (ordinaryStep ttProgram)^[6] s = ttFirstCountResult s := by
  classical
  have hfirst : ordinaryStep ttProgram s = {s with label := 179} := by
    simp only [ordinaryStep, hs, hl, ttProgram_code_threshold_exit]
  rw [show 6 = 5 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one, hfirst]
  apply machineState_ext
  all_goals simp (disch := decide) only
    [
      Function.update_apply, Function.update_idem, dite_eq_ite, if_pos, if_neg, ne73_122, ne127_122, ne7_13, ne13_7, ne80_42, ne73_42, ne73_43, ne47_77, ne48_77, ne48_78, ne78_77, ne78_79,
      Function.iterate_zero_apply, Function.iterate_succ_apply', ordinaryStep, code168, code169, code170, code171, code172, code173, code174, code175, code176, code177, code178, code179, code180, code181, code182, code183, code184, code185, code186, code187, code188, hs, ttFirstCountResult]

theorem ttFirstSelection_not_svd (s : State ttProgram)
    (ha : s.label.val ≠ 167) (hb : s.label.val ≠ 237) :
    instructionIsSVD (ttProgram.code s.label) = false := by
  classical
  cases h : instructionIsSVD (ttProgram.code s.label) with
  | false => rfl
  | true => have hh := (ttProgram_svd_positions s.label).mp h; omega

private theorem code88 : ttProgram.code 88 = .jump 179 := rfl
attribute [local simp] code88

theorem ttFirstSelection_prefix_safe (s : State ttProgram)
    (hl : s.label = 184) (hs : s.status = .running)  :
    ∀ k < 5, instructionIsSVD (ttProgram.code ((ordinaryStep ttProgram)^[k] s).label) = false := by
  classical
  intro k hk
  apply ttFirstSelection_not_svd
  all_goals interval_cases k <;> simp (config := {decide := false})
    [
      Function.update_apply, Function.update_idem, dite_eq_ite, if_pos, if_neg, ne73_122, ne127_122, ne7_13, ne13_7, ne80_42, ne73_42, ne73_43, ne47_77, ne48_77, ne48_78, ne78_77, ne78_79,
      Function.iterate_zero_apply, Function.iterate_succ_apply', ordinaryStep, code168, code169, code170, code171, code172, code173, code174, code175, code176, code177, code178, code179, code180, code181, code182, code183, code184, code185, code186, code187, code188, hl, hs]
  all_goals decide

#assert_trust kernel ttFirstSelection_prefix_safe

theorem ttFirstSelection_large_safe (s : State ttProgram)
    (hl : s.label = 168) (hs : s.status = .running) (hr : s.natural 105 < s.natural 80) :
    ∀ k < 6, instructionIsSVD (ttProgram.code ((ordinaryStep ttProgram)^[k] s).label) = false := by
  classical
  intro k hk
  apply ttFirstSelection_not_svd
  all_goals interval_cases k <;> simp (config := {decide := false})
    [
      Function.update_apply, Function.update_idem, dite_eq_ite, if_pos, if_neg, ne73_122, ne127_122, ne7_13, ne13_7, ne80_42, ne73_42, ne73_43, ne47_77, ne48_77, ne48_78, ne78_77, ne78_79,
      Function.iterate_zero_apply, Function.iterate_succ_apply', ordinaryStep, code168, code169, code170, code171, code172, code173, code174, code175, code176, code177, code178, code179, code180, code181, code182, code183, code184, code185, code186, code187, code188, hl, hs, hr]
  all_goals decide

#assert_trust kernel ttFirstSelection_large_safe

theorem ttFirstSelection_read_safe (s : State ttProgram)
    (hl : s.label = 168) (hs : s.status = .running) (hr : ¬s.natural 105 < s.natural 80) :
    ∀ k < 7, instructionIsSVD (ttProgram.code ((ordinaryStep ttProgram)^[k] s).label) = false := by
  classical
  intro k hk
  apply ttFirstSelection_not_svd
  all_goals interval_cases k <;> simp (config := {decide := false})
    [
      Function.update_apply, Function.update_idem, dite_eq_ite, if_pos, if_neg, ne73_122, ne127_122, ne7_13, ne13_7, ne80_42, ne73_42, ne73_43, ne47_77, ne48_77, ne48_78, ne78_77, ne78_79,
      Function.iterate_zero_apply, Function.iterate_succ_apply', ordinaryStep, code168, code169, code170, code171, code172, code173, code174, code175, code176, code177, code178, code179, code180, code181, code182, code183, code184, code185, code186, code187, code188, hl, hs, hr]
  all_goals decide

#assert_trust kernel ttFirstSelection_read_safe

theorem ttFirstSelection_nonpositive_safe (s : State ttProgram)
    (hl : s.label = 168) (hs : s.status = .running) (hr : ¬s.natural 105 < s.natural 80) (ht : ¬(s.natural 127 : ℝ) < s.memory (s.natural 73 + (s.natural 80 - 1))) :
    ∀ k < 12, instructionIsSVD (ttProgram.code ((ordinaryStep ttProgram)^[k] s).label) = false := by
  classical
  intro k hk
  apply ttFirstSelection_not_svd
  all_goals interval_cases k <;> simp (config := {decide := false})
    [
      Function.update_apply, Function.update_idem, dite_eq_ite, if_pos, if_neg, ne73_122, ne127_122, ne7_13, ne13_7, ne80_42, ne73_42, ne73_43, ne47_77, ne48_77, ne48_78, ne78_77, ne78_79,
      Function.iterate_zero_apply, Function.iterate_succ_apply', ordinaryStep, code168, code169, code170, code171, code172, code173, code174, code175, code176, code177, code178, code179, code180, code181, code182, code183, code184, code185, code186, code187, code188, hl, hs, hr, ht]
  all_goals decide

#assert_trust kernel ttFirstSelection_nonpositive_safe

theorem ttFirstSelection_setup_safe (s : State ttProgram)
    (hl : s.label = 175) (hs : s.status = .running)  :
    ∀ k < 4, instructionIsSVD (ttProgram.code ((ordinaryStep ttProgram)^[k] s).label) = false := by
  classical
  intro k hk
  apply ttFirstSelection_not_svd
  all_goals interval_cases k <;> simp (config := {decide := false})
    [
      Function.update_apply, Function.update_idem, dite_eq_ite, if_pos, if_neg, ne73_122, ne127_122, ne7_13, ne13_7, ne80_42, ne73_42, ne73_43, ne47_77, ne48_77, ne48_78, ne78_77, ne78_79,
      Function.iterate_zero_apply, Function.iterate_succ_apply', ordinaryStep, code168, code169, code170, code171, code172, code173, code174, code175, code176, code177, code178, code179, code180, code181, code182, code183, code184, code185, code186, code187, code188, hl, hs]
  all_goals decide

#assert_trust kernel ttFirstSelection_setup_safe

theorem ttFirstSelection_return_safe (s : State ttProgram)
    (hl : s.label = 88) (hs : s.status = .running)  :
    ∀ k < 6, instructionIsSVD (ttProgram.code ((ordinaryStep ttProgram)^[k] s).label) = false := by
  classical
  intro k hk
  apply ttFirstSelection_not_svd
  all_goals interval_cases k <;> simp (config := {decide := false})
    [
      Function.update_apply, Function.update_idem, dite_eq_ite, if_pos, if_neg, ne73_122, ne127_122, ne7_13, ne13_7, ne80_42, ne73_42, ne73_43, ne47_77, ne48_77, ne48_78, ne78_77, ne78_79,
      Function.iterate_zero_apply, Function.iterate_succ_apply', ordinaryStep, code88, code168, code169, code170, code171, code172, code173, code174, code175, code176, code177, code178, code179, code180, code181, code182, code183, code184, code185, code186, code187, code188, hl, hs]
  all_goals decide

#assert_trust kernel ttFirstSelection_return_safe

#assert_trust kernel ttFirstSelection_prefix_five
#assert_trust kernel ttFirstSelection_large_six
#assert_trust kernel ttFirstSelection_read_seven
#assert_trust kernel ttFirstSelection_nonpositive_twelve
#assert_trust kernel ttFirstSelection_setup_four
#assert_trust kernel ttFirstSelection_return_six
#print axioms ttFirstSelection_read_seven
end NLA.Proofs.TR04
