import NLA.Proofs.TR04.MachineRelocationOrdinary
import NLA.Proofs.TR04.MachineScalarRoutines
import Mathlib.Tactic.FinCases

/-! A fixed actual RAM loop for multiplying natural-valued shape headers stored
as reals. Every header is decoded through cast/equality/increment instructions.
The source memory is never modified. This is an input-initialization component. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

/-- Natural registers: original header count, cursor, accumulated product,
decoding counter. Real registers are the header and its current cast counter. -/
def headerProductProgram : Program where
  extraLabels := 10
  realRegisters := 2
  extraNatRegisters := 3
  constantCount := 0
  constants := Fin.elim0
  code label := match label.val with
    | 0 => .natural 1 0 1
    | 1 => .natural 2 1 2
    | 2 => .lessNat 1 0 3 10
    | 3 => .read 0 1 4
    | 4 => .natural 3 0 5
    | 5 => .castNat 1 3 6
    | 6 => .equalReal 1 0 8 7
    | 7 => .increment 3 5
    | 8 => .mulNat 2 2 3 9
    | 9 => .increment 1 2
    | _ => .halt 2

def headerDecoderLabelMap (i : Fin 4) : Fin 11 := ⟨i.val+5,by omega⟩
def headerDecoderNatMap (i : Fin 2) : Fin 4 :=
  if i.val = 0 then ⟨3,by decide⟩ else ⟨2,by decide⟩

def headerDecoderEmbedding : RoutineEmbedding decodeNaturalProgram headerProductProgram where
  labels := headerDecoderLabelMap
  reals := fun i => i
  naturals := headerDecoderNatMap
  constants := Fin.elim0
  reals_injective := Function.injective_id
  naturals_injective := by
    intro i j h
    apply Fin.ext
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals have hv := congrArg Fin.val h
    all_goals norm_num [headerDecoderNatMap,Matrix.cons_val_one] at hv
  constant_values := by intro i;exact Fin.elim0 i
  code := by
    intro l hl
    fin_cases l <;> first | rfl | cases hl

def headerPrefixProduct (values : ℕ → ℕ) (count : ℕ) : ℕ :=
  ∏ i ∈ Finset.range count, values i

def headerPrefixTime (values : ℕ → ℕ) (count : ℕ) : ℕ :=
  ∑ i ∈ Finset.range count, (3*values i+7)

def headerProductLoopState (memory : ℕ → ℝ) (d : ℕ) (values : ℕ → ℕ) (i counter : ℕ)
    (reals : Fin 2 → ℝ) : State headerProductProgram where
  label := 2
  real := reals
  natural := ![d,i,headerPrefixProduct values i,counter]
  memory := memory
  status := .running

def headerProductDecodeState (memory : ℕ → ℝ) (d i product value : ℕ) (scratch : ℝ) :
    State headerProductProgram where
  label := 5
  real := ![(value : ℝ),scratch]
  natural := ![d,i,product,0]
  memory := memory
  status := .running

theorem headerProductProgram_scalar (s : State headerProductProgram) :
    instructionIsSVD (headerProductProgram.code s.label) = false := by
  rcases s with ⟨label,reals,naturals,memory,status⟩
  fin_cases label <;> rfl

theorem headerProduct_setup (memory : ℕ → ℝ) (d : ℕ) (values : ℕ → ℕ)
    (i counter : ℕ) (reals : Fin 2 → ℝ) (hi : i<d) (hm : memory i = (values i : ℝ)) :
    (ordinaryStep headerProductProgram)^[3] (headerProductLoopState memory d values i counter reals) =
      headerProductDecodeState memory d i (headerPrefixProduct values i) (values i) (reals 1) := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.iterate_succ_apply',ordinaryStep,
    headerProductProgram,headerProductLoopState,headerProductDecodeState,hi,hm]
  all_goals try rfl
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff]
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff]

theorem headerProduct_decode_relates (memory : ℕ → ℝ) (d i product value : ℕ) (scratch : ℝ) :
    headerDecoderEmbedding.Relates (decodeNaturalLoopState memory product value 0 scratch)
      (headerProductDecodeState memory d i product value scratch) := by
  constructor
  · rfl
  · funext r
    fin_cases r <;> rfl
  · funext r
    fin_cases r <;> rfl
  · rfl
  · rfl

def headerProductAfterDecode (memory : ℕ → ℝ) (d i product value : ℕ) :
    State headerProductProgram where
  label := 8
  real := ![(value : ℝ),(value : ℝ)]
  natural := ![d,i,product,value]
  memory := memory
  status := .running

theorem headerProduct_decode (memory : ℕ → ℝ) (d i product value : ℕ) (scratch : ℝ) :
    (ordinaryStep headerProductProgram)^[3*value+2]
      (headerProductDecodeState memory d i product value scratch) =
        headerProductAfterDecode memory d i product value := by
  let E := headerDecoderEmbedding
  have hs := headerProduct_decode_relates memory d i product value scratch
  have hn := decodeNaturalProgram_nohalt_prefix memory product value scratch
  have hr := E.ordinary_iterate_relates hs (3*value+2) hn
  rw [decodeNaturalProgram_return] at hr
  have h0 := E.ordinary_iterate_natural_outside hs (3*value+2) hn 0 (by
    intro r
    fin_cases r
    · change (0 : Fin 4) ≠ ⟨3,by decide⟩
      decide
    · change (0 : Fin 4) ≠ ⟨2,by decide⟩
      decide)
  have h1 := E.ordinary_iterate_natural_outside hs (3*value+2) hn 1 (by
    intro r
    fin_cases r
    · change (1 : Fin 4) ≠ ⟨3,by decide⟩
      decide
    · change (1 : Fin 4) ≠ ⟨2,by decide⟩
      decide)
  apply machineState_ext
  · apply hr.label.trans
    apply Fin.ext
    norm_num [-Fin.val_eq_zero_iff,E,headerDecoderEmbedding,headerDecoderLabelMap,decodeNaturalReturnState,
      decodeNaturalFinalState,headerProductAfterDecode,decodeNaturalProgram,headerProductProgram]
  · funext r
    have hh := hr.real_apply r
    simpa [E,headerDecoderEmbedding,decodeNaturalReturnState,decodeNaturalFinalState,
      headerProductAfterDecode,headerProductProgram,decodeNaturalProgram,Matrix.cons_val_succ',Matrix.cons_val_zero'] using hh
  · funext r
    fin_cases r
    · exact h0
    · exact h1
    · have hh := hr.natural_apply ⟨1,by change 1 < 2;omega⟩
      simpa [E,headerDecoderEmbedding,headerDecoderNatMap,Matrix.cons_val_one,
        decodeNaturalReturnState,decodeNaturalFinalState,headerProductAfterDecode,headerProductProgram,decodeNaturalProgram,Matrix.cons_val_succ',Matrix.cons_val_zero'] using hh
    · have hh := hr.natural_apply ⟨0,by change 0 < 2;omega⟩
      simpa [E,headerDecoderEmbedding,headerDecoderNatMap,decodeNaturalReturnState,
        decodeNaturalFinalState,headerProductAfterDecode,headerProductProgram,decodeNaturalProgram,Matrix.cons_val_succ',Matrix.cons_val_zero'] using hh
  · exact hr.memory
  · exact hr.status

theorem headerPrefixProduct_succ (values : ℕ → ℕ) (i : ℕ) :
    headerPrefixProduct values (i+1) = headerPrefixProduct values i * values i := by
  simp [headerPrefixProduct,Finset.prod_range_succ]

theorem headerPrefixTime_succ (values : ℕ → ℕ) (i : ℕ) :
    headerPrefixTime values (i+1) = headerPrefixTime values i + (3*values i+7) := by
  simp [headerPrefixTime,Finset.sum_range_succ]

theorem headerProduct_finish (memory : ℕ → ℝ) (d : ℕ) (values : ℕ → ℕ) (i : ℕ) :
    (ordinaryStep headerProductProgram)^[2]
      (headerProductAfterDecode memory d i (headerPrefixProduct values i) (values i)) =
        headerProductLoopState memory d values (i+1) (values i) ![(values i : ℝ),(values i : ℝ)] := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.iterate_succ_apply',ordinaryStep,
    headerProductProgram,headerProductLoopState,headerProductAfterDecode,headerPrefixProduct_succ]
  all_goals try rfl
  funext r
  fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Matrix.cons_val_succ',Matrix.cons_val_zero']

theorem headerProduct_iteration (memory : ℕ → ℝ) (d : ℕ) (values : ℕ → ℕ)
    (i counter : ℕ) (reals : Fin 2 → ℝ) (hi : i<d) (hm : memory i = (values i : ℝ)) :
    (ordinaryStep headerProductProgram)^[3*values i+7]
      (headerProductLoopState memory d values i counter reals) =
        headerProductLoopState memory d values (i+1) (values i) ![(values i : ℝ),(values i : ℝ)] := by
  have ht : 3*values i+7 = 2+((3*values i+2)+3) := by omega
  rw [ht,Function.iterate_add_apply,Function.iterate_add_apply,
    headerProduct_setup memory d values i counter reals hi hm,headerProduct_decode]
  exact headerProduct_finish memory d values i

theorem headerProduct_iterations (memory : ℕ → ℝ) (d : ℕ) (values : ℕ → ℕ)
    (hm : ∀ j<d,memory j = (values j : ℝ)) (counter : ℕ) (reals : Fin 2 → ℝ)
    (i : ℕ) (hi : i≤d) :
    ∃ last : ℕ, ∃ registers : Fin 2 → ℝ,
      (ordinaryStep headerProductProgram)^[headerPrefixTime values i]
        (headerProductLoopState memory d values 0 counter reals) =
          headerProductLoopState memory d values i last registers := by
  induction i with
  | zero => exact ⟨counter,reals,rfl⟩
  | succ i ih =>
      obtain ⟨last,registers,hv⟩ := ih (by omega)
      refine ⟨values i,![(values i : ℝ),(values i : ℝ)],?_⟩
      rw [headerPrefixTime_succ,Nat.add_comm,Function.iterate_add_apply,hv]
      exact headerProduct_iteration memory d values i last registers (by omega) (hm i (by omega))

theorem headerProduct_initial (memory : ℕ → ℝ) (d : ℕ) (values : ℕ → ℕ) :
    (ordinaryStep headerProductProgram)^[2] (initial headerProductProgram d memory) =
      headerProductLoopState memory d values 0 0 (fun _ => 0) := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.iterate_succ_apply',ordinaryStep,
    headerProductProgram,initial,headerProductLoopState,headerPrefixProduct]
  all_goals try rfl
  funext r
  fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Matrix.cons_val_succ',Matrix.cons_val_zero']
  · exact if_pos rfl
  · apply if_neg
    intro h
    have hv := congrArg Fin.val h
    norm_num [headerProductProgram] at hv

def headerProductFinalState (memory : ℕ → ℝ) (d : ℕ) (values : ℕ → ℕ)
    (counter : ℕ) (reals : Fin 2 → ℝ) : State headerProductProgram :=
  { headerProductLoopState memory d values d counter reals with
    label := 10
    status := .halted (headerPrefixProduct values d) }

theorem headerProduct_exit (memory : ℕ → ℝ) (d : ℕ) (values : ℕ → ℕ)
    (counter : ℕ) (reals : Fin 2 → ℝ) :
    (ordinaryStep headerProductProgram)^[2] (headerProductLoopState memory d values d counter reals) =
      headerProductFinalState memory d values counter reals := by
  apply machineState_ext <;>
    simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,Function.iterate_succ_apply',ordinaryStep,
      headerProductProgram,headerProductLoopState,headerProductFinalState] <;> rfl

def headerProductTime (values : ℕ → ℕ) (d : ℕ) : ℕ := headerPrefixTime values d+4

theorem headerProduct_trace_result (memory : ℕ → ℝ) (d : ℕ) (values : ℕ → ℕ)
    (hm : ∀ j<d,memory j = (values j : ℝ)) (trace : Trace headerProductProgram)
    (ht : LegalTrace headerProductProgram (initial headerProductProgram d memory) trace) :
    ∃ counter : ℕ, ∃ reals : Fin 2 → ℝ,
      trace.state (headerProductTime values d) = headerProductFinalState memory d values counter reals := by
  obtain ⟨counter,reals,hv⟩ := headerProduct_iterations memory d values hm 0 (fun _ => 0) d le_rfl
  refine ⟨counter,reals,?_⟩
  have htime : headerProductTime values d = 2+(headerPrefixTime values d+2) := by
    unfold headerProductTime;omega
  rw [legalTrace_scalar_prefix ht _ (fun _ _ _ => headerProductProgram_scalar _),
    htime,Function.iterate_add_apply,Function.iterate_add_apply,headerProduct_initial,hv]
  exact headerProduct_exit memory d values counter reals

theorem headerProduct_trace_cost (memory : ℕ → ℝ) (d : ℕ) (values : ℕ → ℕ)
    (trace : Trace headerProductProgram)
    (ht : LegalTrace headerProductProgram (initial headerProductProgram d memory) trace) :
    CostThrough headerProductProgram trace (headerProductTime values d) ≤ headerProductTime values d :=
  costThrough_le_scalar ht headerProductProgram_scalar _

#assert_trust kernel headerProduct_finish
#assert_trust kernel headerProduct_iteration
#assert_trust kernel headerProduct_iterations
#assert_trust kernel headerProduct_initial
#assert_trust kernel headerProduct_exit
#assert_trust kernel headerProduct_trace_result
#assert_trust kernel headerProduct_trace_cost
#print axioms headerProduct_trace_result
#assert_trust kernel headerProduct_decode
#assert_trust kernel headerProductProgram
#assert_trust kernel headerDecoderEmbedding
#assert_trust kernel headerProduct_setup
#assert_trust kernel headerProduct_decode_relates
#print axioms headerDecoderEmbedding
#print axioms headerProduct_setup
end NLA.Proofs.TR04
