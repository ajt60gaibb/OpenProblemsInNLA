import NLA.Proofs.TR04.MachineScalarBlocks

/-! Relocation of literal finite instruction blocks. Halt labels are exits:
caller code may occupy them, and no theorem simulates a step past that exit.
Register injections preserve the actual scalar/memory transition and charge. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def instructionIsHalt {l r n c : ℕ} : Instruction l r n c → Bool
  | .halt _ => true
  | _ => false

/-- Only finite operand and successor names are changed. -/
def relocateInstruction {l r n c L R N C : ℕ}
    (labels : Fin l → Fin L) (reals : Fin r → Fin R)
    (naturals : Fin n → Fin N) (constants : Fin c → Fin C) :
    Instruction l r n c → Instruction L R N C
  | .constant a b next => .constant (reals a) (constants b) (labels next)
  | .copyReal a b next => .copyReal (reals a) (reals b) (labels next)
  | .addReal a b d next => .addReal (reals a) (reals b) (reals d) (labels next)
  | .subReal a b d next => .subReal (reals a) (reals b) (reals d) (labels next)
  | .mulReal a b d next => .mulReal (reals a) (reals b) (reals d) (labels next)
  | .divReal a b d next => .divReal (reals a) (reals b) (reals d) (labels next)
  | .sqrtReal a b next => .sqrtReal (reals a) (reals b) (labels next)
  | .lessReal a b yes no => .lessReal (reals a) (reals b) (labels yes) (labels no)
  | .equalReal a b yes no => .equalReal (reals a) (reals b) (labels yes) (labels no)
  | .natural a b next => .natural (naturals a) b (labels next)
  | .copyNat a b next => .copyNat (naturals a) (naturals b) (labels next)
  | .increment a next => .increment (naturals a) (labels next)
  | .decrement a next => .decrement (naturals a) (labels next)
  | .addNat a b d next => .addNat (naturals a) (naturals b) (naturals d) (labels next)
  | .mulNat a b d next => .mulNat (naturals a) (naturals b) (naturals d) (labels next)
  | .lessNat a b yes no => .lessNat (naturals a) (naturals b) (labels yes) (labels no)
  | .equalNat a b yes no => .equalNat (naturals a) (naturals b) (labels yes) (labels no)
  | .castNat a b next => .castNat (reals a) (naturals b) (labels next)
  | .read a b next => .read (reals a) (naturals b) (labels next)
  | .write a b next => .write (naturals a) (reals b) (labels next)
  | .svd a b d e f g next =>
      .svd (naturals a) (naturals b) (naturals d) (naturals e) (naturals f) (naturals g) (labels next)
  | .jump next => .jump (labels next)
  | .halt a => .halt (naturals a)

structure RoutineEmbedding (P Q : Program) where
  labels : Fin (P.extraLabels + 1) → Fin (Q.extraLabels + 1)
  reals : Fin P.realRegisters → Fin Q.realRegisters
  naturals : Fin (P.extraNatRegisters + 1) → Fin (Q.extraNatRegisters + 1)
  constants : Fin P.constantCount → Fin Q.constantCount
  reals_injective : Function.Injective reals
  naturals_injective : Function.Injective naturals
  constant_values : ∀ i, Q.constants (constants i) = P.constants i
  code : ∀ l, instructionIsHalt (P.code l) = false →
    Q.code (labels l) = relocateInstruction labels reals naturals constants (P.code l)

structure RoutineEmbedding.Relates {P Q : Program} (E : RoutineEmbedding P Q)
    (s : State P) (t : State Q) : Prop where
  label : t.label = E.labels s.label
  real : t.real ∘ E.reals = s.real
  natural : t.natural ∘ E.naturals = s.natural
  memory : t.memory = s.memory
  status : t.status = s.status

theorem RoutineEmbedding.Relates.real_apply {P Q : Program} {E : RoutineEmbedding P Q}
    {s : State P} {t : State Q} (h : E.Relates s t) (i : Fin P.realRegisters) :
    t.real (E.reals i) = s.real i := congrFun h.real i

theorem RoutineEmbedding.Relates.natural_apply {P Q : Program} {E : RoutineEmbedding P Q}
    {s : State P} {t : State Q} (h : E.Relates s t) (i : Fin (P.extraNatRegisters + 1)) :
    t.natural (E.naturals i) = s.natural i := congrFun h.natural i

/-- One literal ordinary step is preserved before a routine exit. -/
theorem RoutineEmbedding.ordinaryStep_relates {P Q : Program} (E : RoutineEmbedding P Q)
    {s : State P} {t : State Q} (h : E.Relates s t)
    (hexit : instructionIsHalt (P.code s.label) = false) :
    E.Relates (ordinaryStep P s) (ordinaryStep Q t) := by
  classical
  have hcode : Q.code t.label =
      relocateInstruction E.labels E.reals E.naturals E.constants (P.code s.label) := by
    rw [h.label]
    exact E.code s.label hexit
  cases hs : s.status with
  | halted base => simpa only [ordinaryStep, hs, h.status] using h
  | failed => simpa only [ordinaryStep, hs, h.status] using h
  | running =>
    cases hi : P.code s.label <;>
      simp only [hi, instructionIsHalt] at hexit
    all_goals try contradiction
    all_goals constructor <;>
      simp_all [ordinaryStep, relocateInstruction, Function.update_comp_eq_of_injective,
        E.reals_injective, E.naturals_injective, h.real_apply, h.natural_apply,
        h.real, h.natural, h.memory, h.status, h.label, E.constant_values]
    all_goals split <;> simp_all [Function.update_comp_eq_of_injective,
      E.reals_injective, E.naturals_injective, h.real, h.natural]

theorem instructionIsSVD_relocate {l r n c L R N C : ℕ}
    (labels : Fin l → Fin L) (reals : Fin r → Fin R)
    (naturals : Fin n → Fin N) (constants : Fin c → Fin C) (i : Instruction l r n c) :
    instructionIsSVD (relocateInstruction labels reals naturals constants i) =
      instructionIsSVD i := by cases i <;> rfl

/-- Relocation preserves the model's exact instruction charge. -/
theorem RoutineEmbedding.charge_eq {P Q : Program} (E : RoutineEmbedding P Q)
    {s : State P} {t : State Q} (h : E.Relates s t)
    (hexit : instructionIsHalt (P.code s.label) = false) : charge Q t = charge P s := by
  have hcode : Q.code t.label =
      relocateInstruction E.labels E.reals E.naturals E.constants (P.code s.label) := by
    rw [h.label]
    exact E.code s.label hexit
  cases hs : s.status with
  | halted base => simp [charge, h.status, hs]
  | failed => simp [charge, h.status, hs]
  | running =>
    cases hi : P.code s.label <;>
      simp [charge, h.status, hs, hcode, hi, relocateInstruction, h.natural_apply]

/-- Every legal caller transition through a relocated scalar instruction follows
its actual local transition, including its exact charge. -/
theorem RoutineEmbedding.scalar_step {P Q : Program} (E : RoutineEmbedding P Q)
    {s : State P} {t t' : State Q} {cost : ℕ} (h : E.Relates s t)
    (hexit : instructionIsHalt (P.code s.label) = false)
    (hscalar : instructionIsSVD (P.code s.label) = false) (ht : Step Q t t' cost) :
    E.Relates (ordinaryStep P s) t' ∧ cost = charge P s := by
  have hQscalar : instructionIsSVD (Q.code t.label) = false := by
    rw [h.label, E.code s.label hexit, instructionIsSVD_relocate]
    exact hscalar
  obtain ⟨hc, heq⟩ := (step_iff_ordinary_of_scalar (fun _ => hQscalar)).1 ht
  rw [heq]
  exact ⟨E.ordinaryStep_relates h hexit, hc.trans (E.charge_eq h hexit)⟩

/-- A caller's legal trace follows the complete actual local scalar block until
its exit, regardless of caller instructions after that exit. -/
theorem RoutineEmbedding.scalar_trace_prefix {P Q : Program} (E : RoutineEmbedding P Q)
    (s : State P) {start : State Q} {trace : Trace Q} (hstart : E.Relates s start)
    (ht : LegalTrace Q start trace) (n : ℕ)
    (hexit : ∀ k < n, instructionIsHalt (P.code ((ordinaryStep P)^[k] s).label) = false)
    (hscalar : ∀ k < n, instructionIsSVD (P.code ((ordinaryStep P)^[k] s).label) = false) :
    E.Relates ((ordinaryStep P)^[n] s) (trace.state n) := by
  induction n with
  | zero => simpa only [Function.iterate_zero_apply, ht.1] using hstart
  | succ n ih =>
      have hr := ih (fun k hk => hexit k (by omega)) (fun k hk => hscalar k (by omega))
      have hn := E.scalar_step hr (hexit n (by omega)) (hscalar n (by omega)) (ht.2 n)
      simpa only [Function.iterate_succ_apply'] using hn.1

/-- The actual caller's charged prefix equals the local literal-charge sum. -/
theorem RoutineEmbedding.scalar_trace_cost {P Q : Program} (E : RoutineEmbedding P Q)
    (s : State P) {start : State Q} {trace : Trace Q} (hstart : E.Relates s start)
    (ht : LegalTrace Q start trace) (n : ℕ)
    (hexit : ∀ k < n, instructionIsHalt (P.code ((ordinaryStep P)^[k] s).label) = false)
    (hscalar : ∀ k < n, instructionIsSVD (P.code ((ordinaryStep P)^[k] s).label) = false) :
    CostThrough Q trace n = ∑ k ∈ Finset.range n, charge P ((ordinaryStep P)^[k] s) := by
  unfold CostThrough
  apply Finset.sum_congr rfl
  intro k hk
  have hkn := Finset.mem_range.mp hk
  have hr := E.scalar_trace_prefix s hstart ht k
    (fun j hj => hexit j (by omega)) (fun j hj => hscalar j (by omega))
  exact (E.scalar_step hr (hexit k hkn) (hscalar k hkn) (ht.2 k)).2

/-- A relocated scalar block has at most one actual charge per transition. -/
theorem RoutineEmbedding.scalar_trace_cost_le {P Q : Program} (E : RoutineEmbedding P Q)
    (s : State P) {start : State Q} {trace : Trace Q} (hstart : E.Relates s start)
    (ht : LegalTrace Q start trace) (n : ℕ)
    (hexit : ∀ k < n, instructionIsHalt (P.code ((ordinaryStep P)^[k] s).label) = false)
    (hscalar : ∀ k < n, instructionIsSVD (P.code ((ordinaryStep P)^[k] s).label) = false) :
    CostThrough Q trace n ≤ n := by
  rw [E.scalar_trace_cost s hstart ht n hexit hscalar]
  calc
    ∑ k ∈ Finset.range n, charge P ((ordinaryStep P)^[k] s) ≤
        ∑ _k ∈ Finset.range n, 1 := by
      apply Finset.sum_le_sum
      intro k hk
      exact charge_le_one_of_scalar (fun _ => hscalar k (Finset.mem_range.mp hk))
    _ = n := by simp

/-- A relocated block cannot overwrite a caller real register outside its frame. -/
theorem RoutineEmbedding.ordinaryStep_real_outside {P Q : Program} (E : RoutineEmbedding P Q)
    {l : Fin (P.extraLabels + 1)} {t : State Q} (hl : t.label = E.labels l)
    (hexit : instructionIsHalt (P.code l) = false) (j : Fin Q.realRegisters)
    (hj : ∀ i, j ≠ E.reals i) : (ordinaryStep Q t).real j = t.real j := by
  classical
  have hcode : Q.code t.label =
      relocateInstruction E.labels E.reals E.naturals E.constants (P.code l) := by
    rw [hl]; exact E.code l hexit
  cases hs : t.status with
  | halted base => simp [ordinaryStep, hs]
  | failed => simp [ordinaryStep, hs]
  | running =>
      cases hi : P.code l <;>
        simp [ordinaryStep, hs, hcode, hi, relocateInstruction, Function.update_of_ne, hj]
      all_goals split <;> simp [Function.update_of_ne, hj]

/-- Natural registers outside the injected frame are likewise preserved. -/
theorem RoutineEmbedding.ordinaryStep_natural_outside {P Q : Program} (E : RoutineEmbedding P Q)
    {l : Fin (P.extraLabels + 1)} {t : State Q} (hl : t.label = E.labels l)
    (hexit : instructionIsHalt (P.code l) = false) (j : Fin (Q.extraNatRegisters + 1))
    (hj : ∀ i, j ≠ E.naturals i) : (ordinaryStep Q t).natural j = t.natural j := by
  classical
  have hcode : Q.code t.label =
      relocateInstruction E.labels E.reals E.naturals E.constants (P.code l) := by
    rw [hl]; exact E.code l hexit
  cases hs : t.status with
  | halted base => simp [ordinaryStep, hs]
  | failed => simp [ordinaryStep, hs]
  | running =>
      cases hi : P.code l <;>
        simp [ordinaryStep, hs, hcode, hi, relocateInstruction, Function.update_of_ne, hj]
      all_goals split <;> simp [Function.update_of_ne, hj]

/-- Caller real registers outside the frame survive the entire legal block. -/
theorem RoutineEmbedding.scalar_trace_real_outside {P Q : Program} (E : RoutineEmbedding P Q)
    (s : State P) {start : State Q} {trace : Trace Q} (hstart : E.Relates s start)
    (ht : LegalTrace Q start trace) (n : ℕ)
    (hexit : ∀ k < n, instructionIsHalt (P.code ((ordinaryStep P)^[k] s).label) = false)
    (hscalar : ∀ k < n, instructionIsSVD (P.code ((ordinaryStep P)^[k] s).label) = false)
    (j : Fin Q.realRegisters) (hj : ∀ i, j ≠ E.reals i) :
    (trace.state n).real j = start.real j := by
  induction n with
  | zero => rw [ht.1]
  | succ n ih =>
      have hr := E.scalar_trace_prefix s hstart ht n
        (fun k hk => hexit k (by omega)) (fun k hk => hscalar k (by omega))
      have hQscalar : instructionIsSVD (Q.code (trace.state n).label) = false := by
        rw [hr.label, E.code _ (hexit n (by omega)), instructionIsSVD_relocate]
        exact hscalar n (by omega)
      have hnext := ((step_iff_ordinary_of_scalar (fun _ => hQscalar)).1 (ht.2 n)).2
      rw [hnext, E.ordinaryStep_real_outside hr.label (hexit n (by omega)) j hj]
      exact ih (fun k hk => hexit k (by omega)) (fun k hk => hscalar k (by omega))

theorem RoutineEmbedding.scalar_trace_natural_outside {P Q : Program} (E : RoutineEmbedding P Q)
    (s : State P) {start : State Q} {trace : Trace Q} (hstart : E.Relates s start)
    (ht : LegalTrace Q start trace) (n : ℕ)
    (hexit : ∀ k < n, instructionIsHalt (P.code ((ordinaryStep P)^[k] s).label) = false)
    (hscalar : ∀ k < n, instructionIsSVD (P.code ((ordinaryStep P)^[k] s).label) = false)
    (j : Fin (Q.extraNatRegisters + 1)) (hj : ∀ i, j ≠ E.naturals i) :
    (trace.state n).natural j = start.natural j := by
  induction n with
  | zero => rw [ht.1]
  | succ n ih =>
      have hr := E.scalar_trace_prefix s hstart ht n
        (fun k hk => hexit k (by omega)) (fun k hk => hscalar k (by omega))
      have hQscalar : instructionIsSVD (Q.code (trace.state n).label) = false := by
        rw [hr.label, E.code _ (hexit n (by omega)), instructionIsSVD_relocate]
        exact hscalar n (by omega)
      have hnext := ((step_iff_ordinary_of_scalar (fun _ => hQscalar)).1 (ht.2 n)).2
      rw [hnext, E.ordinaryStep_natural_outside hr.label (hexit n (by omega)) j hj]
      exact ih (fun k hk => hexit k (by omega)) (fun k hk => hscalar k (by omega))

#assert_trust kernel RoutineEmbedding.ordinaryStep_real_outside
#assert_trust kernel RoutineEmbedding.ordinaryStep_natural_outside
#assert_trust kernel RoutineEmbedding.scalar_trace_real_outside
#assert_trust kernel RoutineEmbedding.scalar_trace_natural_outside
#assert_trust kernel instructionIsSVD_relocate
#assert_trust kernel RoutineEmbedding.charge_eq
#assert_trust kernel RoutineEmbedding.scalar_step
#assert_trust kernel RoutineEmbedding.scalar_trace_prefix
#assert_trust kernel RoutineEmbedding.scalar_trace_cost
#assert_trust kernel RoutineEmbedding.scalar_trace_cost_le
#assert_trust kernel instructionIsHalt
#assert_trust kernel relocateInstruction
#assert_trust kernel RoutineEmbedding
#assert_trust kernel RoutineEmbedding.ordinaryStep_relates
#print axioms RoutineEmbedding.ordinaryStep_relates
end NLA.Proofs.TR04
