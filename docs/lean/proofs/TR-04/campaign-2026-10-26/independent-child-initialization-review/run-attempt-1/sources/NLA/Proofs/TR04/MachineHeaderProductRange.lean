import NLA.Proofs.TR04.MachineHeaderProductSingle
import Mathlib.Algebra.BigOperators.Intervals

/-! Suffix products using the literal header-product instruction bank. Entry is
the ordinary loop test at label2 with cursor `a` and accumulated product1.
Only memory addresses in `[a,d)` are read. Earlier headers have no precondition.
The padding function below is a proof device, not executable program data. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def headerRangeValues (values : ℕ → ℕ) (a : ℕ) (j : ℕ) : ℕ :=
  if j<a then 1 else values j

def headerRangeProduct (values : ℕ → ℕ) (a d : ℕ) : ℕ :=
  ∏ j ∈ Finset.Ico a d, values j

def headerRangeTime (values : ℕ → ℕ) (a d : ℕ) : ℕ :=
  (∑ j ∈ Finset.Ico a d, (3*values j+7))+1

theorem headerRange_prefix_start (values : ℕ → ℕ) (a : ℕ) :
    headerPrefixProduct (headerRangeValues values a) a = 1 := by
  apply Finset.prod_eq_one
  intro j hj
  exact if_pos (Finset.mem_range.mp hj)

theorem headerRange_prefix_product (values : ℕ → ℕ) (a d : ℕ) (had : a≤d) :
    headerPrefixProduct (headerRangeValues values a) d = headerRangeProduct values a d := by
  have h := Finset.prod_range_mul_prod_Ico (headerRangeValues values a) had
  rw [show (∏ j ∈ Finset.range a, headerRangeValues values a j) = 1 from
    headerRange_prefix_start values a,one_mul] at h
  change (∏ j ∈ Finset.range d, headerRangeValues values a j) =
    ∏ j ∈ Finset.Ico a d, values j
  rw [← h]
  apply Finset.prod_congr rfl
  intro j hj
  exact if_neg (by have := (Finset.mem_Ico.mp hj).1;omega)

theorem headerRange_iterations (memory : ℕ → ℝ) (d a : ℕ) (values : ℕ → ℕ)
    (hm : ∀ j, a≤j → j<d → memory j = (values j : ℝ)) (counter : ℕ)
    (reals : Fin 2 → ℝ) (q : ℕ) (hq : a+q≤d) :
    ∃ last : ℕ, ∃ registers : Fin 2 → ℝ,
      (ordinaryStep headerProductProgram)^[∑ j ∈ Finset.Ico a (a+q), (3*values j+7)]
        (headerProductLoopState memory d values a counter reals) =
          headerProductLoopState memory d values (a+q) last registers := by
  induction q with
  | zero => exact ⟨counter,reals,by simp⟩
  | succ q ih =>
      obtain ⟨last,registers,hv⟩ := ih (by omega)
      refine ⟨values (a+q),![(values (a+q) : ℝ),(values (a+q) : ℝ)],?_⟩
      rw [show a+(q+1) = (a+q)+1 by omega,
        Finset.sum_Ico_succ_top (by omega : a≤a+q),Nat.add_comm,
        Function.iterate_add_apply,hv]
      exact headerProduct_iteration memory d values (a+q) last registers
        (by omega) (hm (a+q) (by omega) (by omega))

def headerRangeEntryState (memory : ℕ → ℝ) (d a : ℕ) (values : ℕ → ℕ)
    (counter : ℕ) (reals : Fin 2 → ℝ) : State headerProductProgram :=
  headerProductLoopState memory d (headerRangeValues values a) a counter reals

def headerRangeReturnState (memory : ℕ → ℝ) (d a : ℕ) (values : ℕ → ℕ)
    (counter : ℕ) (reals : Fin 2 → ℝ) : State headerProductProgram :=
  headerProductReturnState memory d (headerRangeValues values a) counter reals

theorem headerRange_entry_product (memory : ℕ → ℝ) (d a : ℕ) (values : ℕ → ℕ)
    (counter : ℕ) (reals : Fin 2 → ℝ) :
    (headerRangeEntryState memory d a values counter reals).natural 2 = 1 :=
  headerRange_prefix_start values a

/-- The actual entry registers contain no data derived from the unread suffix. -/
theorem headerRange_entry_eq (memory : ℕ → ℝ) (d a : ℕ) (values : ℕ → ℕ)
    (counter : ℕ) (reals : Fin 2 → ℝ) :
    headerRangeEntryState memory d a values counter reals =
      { label := 2,real := reals,natural := ![d,a,1,counter],
        memory := memory,status := .running } := by
  unfold headerRangeEntryState headerProductLoopState
  rw [headerRange_prefix_start]

theorem headerRange_return_product (memory : ℕ → ℝ) (d a : ℕ) (values : ℕ → ℕ)
    (counter : ℕ) (reals : Fin 2 → ℝ) (had : a≤d) :
    (headerRangeReturnState memory d a values counter reals).natural 2 =
      headerRangeProduct values a d := headerRange_prefix_product values a d had

theorem headerRange_return (memory : ℕ → ℝ) (d a : ℕ) (values : ℕ → ℕ) (had : a≤d)
    (hm : ∀ j, a≤j → j<d → memory j = (values j : ℝ))
    (counter : ℕ) (reals : Fin 2 → ℝ) :
    ∃ last : ℕ, ∃ registers : Fin 2 → ℝ,
      (ordinaryStep headerProductProgram)^[headerRangeTime values a d]
        (headerRangeEntryState memory d a values counter reals) =
          headerRangeReturnState memory d a values last registers := by
  have hm' : ∀ j, a≤j → j<d → memory j = (headerRangeValues values a j : ℝ) := by
    intro j haj hjd
    simpa only [headerRangeValues,if_neg (by omega : ¬j<a)] using hm j haj hjd
  obtain ⟨last,registers,hv⟩ := headerRange_iterations memory d a
    (headerRangeValues values a) hm' counter reals (d-a) (by omega)
  have hsum : (∑ j ∈ Finset.Ico a d, (3*headerRangeValues values a j+7)) =
      ∑ j ∈ Finset.Ico a d, (3*values j+7) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [headerRangeValues,if_neg (by have := (Finset.mem_Ico.mp hj).1;omega)]
  rw [Nat.add_sub_of_le had,hsum] at hv
  refine ⟨last,registers,?_⟩
  rw [headerRangeTime,Nat.add_comm,Function.iterate_add_apply]
  change ordinaryStep headerProductProgram
    ((ordinaryStep headerProductProgram)^[∑ j ∈ Finset.Ico a d, (3*values j+7)]
      (headerProductLoopState memory d (headerRangeValues values a) a counter reals)) = _
  rw [hv]
  exact headerProduct_exit_test memory d (headerRangeValues values a) last registers

theorem headerRange_time_le (values : ℕ → ℕ) (a d : ℕ) :
    headerRangeTime values a d ≤ headerPrefixTime values d+1 := by
  apply Nat.add_le_add_right
  exact Finset.sum_le_sum_of_subset (by
    intro j hj
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2)

theorem RoutineEmbedding.headerRange_run_at {Q : Program}
    (E : RoutineEmbedding headerProductProgram Q) (memory : ℕ → ℝ)
    (d a : ℕ) (values : ℕ → ℕ) (had : a≤d)
    (hm : ∀ j, a≤j → j<d → memory j = (values j : ℝ))
    (counter : ℕ) (reals : Fin 2 → ℝ) {start : State Q} {trace : Trace Q}
    (ht : LegalTrace Q start trace) (offset : ℕ)
    (hs : E.Relates (headerRangeEntryState memory d a values counter reals) (trace.state offset)) :
    ∃ last : ℕ, ∃ registers : Fin 2 → ℝ,
      E.Relates (headerRangeReturnState memory d a values last registers)
        (trace.state (offset+headerRangeTime values a d)) ∧
      CostThrough Q trace (offset+headerRangeTime values a d) ≤
        CostThrough Q trace offset+headerRangeTime values a d := by
  obtain ⟨last,registers,hv⟩ := headerRange_return memory d a values had hm counter reals
  have hrunning : ((ordinaryStep headerProductProgram)^[headerRangeTime values a d]
      (headerRangeEntryState memory d a values counter reals)).status = .running := by
    rw [hv];rfl
  have hn := ordinary_nohalt_prefix_of_running _ _ hrunning
  have hc : ∀ k<headerRangeTime values a d, instructionIsSVD (headerProductProgram.code
      ((ordinaryStep headerProductProgram)^[k]
        (headerRangeEntryState memory d a values counter reals)).label) = false :=
    fun _ _ => headerProductProgram_scalar _
  have hr := E.scalar_trace_prefix _ hs (legalTrace_shift ht offset) _ hn hc
  rw [hv] at hr
  exact ⟨last,registers,hr,costThrough_compose_le le_rfl
    (E.scalar_trace_cost_le _ hs (legalTrace_shift ht offset) _ hn hc)⟩

#assert_trust kernel headerRange_prefix_start
#assert_trust kernel headerRange_prefix_product
#assert_trust kernel headerRange_iterations
#assert_trust kernel headerRange_entry_product
#assert_trust kernel headerRange_entry_eq
#assert_trust kernel headerRange_return_product
#assert_trust kernel headerRange_return
#assert_trust kernel headerRange_time_le
#assert_trust kernel RoutineEmbedding.headerRange_run_at
#print axioms RoutineEmbedding.headerRange_run_at
end NLA.Proofs.TR04
