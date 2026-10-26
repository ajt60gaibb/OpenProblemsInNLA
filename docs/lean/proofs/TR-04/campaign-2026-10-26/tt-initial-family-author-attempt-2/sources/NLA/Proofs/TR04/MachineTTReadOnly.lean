import NLA.Proofs.TR04.MachineTTProgramFacts

/-! A literal syntactic natural-register invariant for the entire fixed TT
program, including every legal full-SVD reply and absorbing stopped states. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation

def instructionNaturalDestination {l r n c : ℕ} : Instruction l r n c → Option (Fin n)
  | .natural a _ _ => some a
  | .copyNat a _ _ => some a
  | .increment a _ => some a
  | .decrement a _ => some a
  | .addNat a _ _ _ => some a
  | .mulNat a _ _ _ => some a
  | _ => none

theorem ordinaryStep_natural_readOnly {P : Program} (s : State P)
    (j : Fin (P.extraNatRegisters+1))
    (h : instructionNaturalDestination (P.code s.label)≠some j) :
    (ordinaryStep P s).natural j=s.natural j := by
  cases hs : s.status with
  | halted b => simp [ordinaryStep,hs]
  | failed => simp [ordinaryStep,hs]
  | running =>
    cases hi : P.code s.label
    all_goals simp only [hi,instructionNaturalDestination,ne_eq,Option.some.injEq] at h
    all_goals simp only [ordinaryStep,hs,hi]
    all_goals first
      | exact Function.update_of_ne (Ne.symm h) _ _
      | rfl
      | split <;> rfl

theorem step_natural_readOnly {P : Program} {s t : State P} {cost : ℕ}
    (hstep : Step P s t cost) (j : Fin (P.extraNatRegisters+1))
    (h : instructionNaturalDestination (P.code s.label)≠some j) : t.natural j=s.natural j := by
  cases hs : s.status with
  | halted b =>
    have he : t=s := by simpa only [Step,hs] using hstep.2
    rw [he]
  | failed =>
    have he : t=s := by simpa only [Step,hs] using hstep.2
    rw [he]
  | running =>
    by_cases hscalar : instructionIsSVD (P.code s.label)=false
    · have he := ((step_iff_ordinary_of_scalar (fun _ => hscalar)).1 hstep).2
      rw [he]
      exact ordinaryStep_natural_readOnly s j h
    · cases hi : P.code s.label <;> simp [hi,instructionIsSVD] at hscalar
      have hv := hstep.2
      simp only [hs,hi] at hv
      split at hv
      · obtain ⟨U,sigma,V,_,he⟩ := hv
        rw [he]
      · rw [hv]

theorem trace_natural_readOnly {P : Program} {start : State P} {trace : Trace P}
    (ht : LegalTrace P start trace) (j : Fin (P.extraNatRegisters+1))
    (h : ∀ label,instructionNaturalDestination (P.code label)≠some j) (n : ℕ) :
    (trace.state n).natural j=start.natural j := by
  induction n with
  | zero => rw [ht.1]
  | succ n ih => exact (step_natural_readOnly (ht.2 n) j (h _)).trans ih

theorem ttProgram_order_readOnly : ∀ label : Fin 512,
    instructionNaturalDestination (ttProgram.code label)≠some 0 := by decide

theorem ttProgram_trace_order (S : Shape) (r : Ranks S) (A : Tensor S)
    (trace : Trace ttProgram) (ht : LegalTrace ttProgram (Start ttProgram S r A) trace) (n : ℕ) :
    (trace.state n).natural 0=S.order :=
  trace_natural_readOnly ht 0 ttProgram_order_readOnly n

#assert_trust kernel instructionNaturalDestination
#assert_trust kernel ordinaryStep_natural_readOnly
#assert_trust kernel step_natural_readOnly
#assert_trust kernel trace_natural_readOnly
#assert_trust kernel ttProgram_order_readOnly
#assert_trust kernel ttProgram_trace_order
#print axioms ttProgram_trace_order
end NLA.Proofs.TR04
