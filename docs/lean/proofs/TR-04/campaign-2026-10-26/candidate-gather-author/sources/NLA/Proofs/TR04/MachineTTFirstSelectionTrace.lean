import NLA.Proofs.TR04.MachineTTFirstSelectionScalar

/-! Actual trace composition for the first selection caller and its installed
read-only threshold scan. No SVD reply is selected by these interfaces. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

/-- Registers outside the first-selection scratch and result frame. -/
def TTFirstProtected (j : Fin 128) : Prop :=
  49 ≤ j.val ∧ j ≠ 75 ∧ j ≠ 77 ∧ j ≠ 78 ∧ j ≠ 79 ∧ j ≠ 122

def TTFirstPreserves (s t : State ttProgram) : Prop :=
  t.memory = s.memory ∧ ∀ j : Fin 128, TTFirstProtected j → t.natural j = s.natural j

theorem ttFirstPreserves_trans {s t u : State ttProgram}
    (h : TTFirstPreserves s t) (k : TTFirstPreserves t u) : TTFirstPreserves s u :=
  ⟨k.1.trans h.1, fun j hj => (k.2 j hj).trans (h.2 j hj)⟩

theorem ttFirstPrefix_preserves (s : State ttProgram) : TTFirstPreserves s (ttFirstPrefixResult s) := by
  refine ⟨rfl, ?_⟩
  intro j hj
  change (Function.update (Function.update (Function.update (Function.update s.natural 77 (s.natural 106)) 78 1) 79 0) 75 1) j = s.natural j
  calc
    _ = (Function.update (Function.update (Function.update s.natural 77 (s.natural 106)) 78 1) 79 0) j :=
      Function.update_of_ne hj.2.1 _ _
    _ = (Function.update (Function.update s.natural 77 (s.natural 106)) 78 1) j :=
      Function.update_of_ne hj.2.2.2.2.1 _ _
    _ = (Function.update s.natural 77 (s.natural 106)) j :=
      Function.update_of_ne hj.2.2.2.1 _ _
    _ = s.natural j := Function.update_of_ne hj.2.2.1 _ _

theorem ttFirstRead_preserves (s : State ttProgram) : TTFirstPreserves s (ttFirstThresholdRead s) := by
  refine ⟨rfl, ?_⟩
  intro j hj
  exact Function.update_of_ne hj.2.2.2.2.2 _ _

theorem ttFirstEntry_preserves (s : State ttProgram) : TTFirstPreserves s (ttFirstThresholdEntry s) := by
  refine ⟨rfl, ?_⟩
  intro j hj
  have h42 : j ≠ (42 : Fin 128) := by intro h; subst j; norm_num [TTFirstProtected] at hj
  have h43 : j ≠ (43 : Fin 128) := by intro h; subst j; norm_num [TTFirstProtected] at hj
  have h44 : j ≠ (44 : Fin 128) := by intro h; subst j; norm_num [TTFirstProtected] at hj
  change (Function.update (Function.update (Function.update s.natural 42 (s.natural 105)) 43 (s.natural 80)) 44 (s.natural 73)) j = s.natural j
  exact (Function.update_of_ne h44 _ _).trans
    ((Function.update_of_ne h43 _ _).trans (Function.update_of_ne h42 _ _))

theorem ttFirstCount_preserves (s : State ttProgram) : TTFirstPreserves s (ttFirstCountResult s) := by
  refine ⟨rfl, ?_⟩
  intro j hj
  change (Function.update (Function.update (Function.update (Function.update s.natural 77 (s.natural 46)) 78 (s.natural 47)) 79 (s.natural 48)) 75 (s.natural 47)) j = s.natural j
  calc
    _ = (Function.update (Function.update (Function.update s.natural 77 (s.natural 46)) 78 (s.natural 47)) 79 (s.natural 48)) j :=
      Function.update_of_ne hj.2.1 _ _
    _ = (Function.update (Function.update s.natural 77 (s.natural 46)) 78 (s.natural 47)) j :=
      Function.update_of_ne hj.2.2.2.2.1 _ _
    _ = (Function.update s.natural 77 (s.natural 46)) j :=
      Function.update_of_ne hj.2.2.2.1 _ _
    _ = s.natural j := Function.update_of_ne hj.2.2.1 _ _

/-- The caller's scratch is unrestricted at the bank entry. -/
def ttFirstThresholdAux (s : State ttProgram) : Fin 5 → ℕ :=
  ![s.natural 41, s.natural 45, s.natural 46, s.natural 47, s.natural 48]

theorem ttFirstThreshold_relates (s : State ttProgram) (hs : s.status = .running) :
    ttThresholdEmbedding.Relates
      (thresholdScanStart s.memory ⟨s.natural 105, s.natural 80, s.natural 73⟩
        (s.memory (s.natural 73 + (s.natural 80 - 1))) (s.real 8) (ttFirstThresholdAux s))
      (ttFirstThresholdEntry (ttFirstThresholdRead s)) := by
  constructor
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl
  · exact hs

theorem ttFirstThreshold_outside (memory : ℕ → ℝ) (P : ThresholdScanParameters)
    (tau scratch : ℝ) (aux : Fin 5 → ℕ)
    {start : State ttProgram} {trace : Trace ttProgram} (ht : LegalTrace ttProgram start trace)
    (offset : ℕ)
    (hs : ttThresholdEmbedding.Relates (thresholdScanStart memory P tau scratch aux) (trace.state offset))
    (j : Fin 128) (hj : 49 ≤ j.val) :
    (trace.state (offset + (9 * P.count + 6))).natural j = (trace.state offset).natural j := by
  obtain ⟨v, hv⟩ := thresholdScanProgram_return memory P tau scratch aux
  have hn := ordinary_nohalt_prefix_of_running (thresholdScanStart memory P tau scratch aux)
    (9 * P.count + 6) (by rw [hv]; rfl)
  have hj' : ∀ i, j ≠ ttThresholdEmbedding.naturals i := by
    intro i heq
    have hval := congrArg Fin.val heq
    have hi := i.isLt
    change j.val = 41 + i.val at hval
    change i.val < 8 at hi
    omega
  exact ttThresholdEmbedding.scalar_trace_natural_outside _ hs (legalTrace_shift ht offset)
    _ hn (fun _ _ => thresholdScanProgram_scalar _) j hj'

#assert_trust kernel ttFirstPreserves_trans
#assert_trust kernel ttFirstPrefix_preserves
#assert_trust kernel ttFirstRead_preserves
#assert_trust kernel ttFirstEntry_preserves
#assert_trust kernel ttFirstCount_preserves
#assert_trust kernel ttFirstThreshold_relates
#assert_trust kernel ttFirstThreshold_outside
#print axioms ttFirstThreshold_relates
end NLA.Proofs.TR04
