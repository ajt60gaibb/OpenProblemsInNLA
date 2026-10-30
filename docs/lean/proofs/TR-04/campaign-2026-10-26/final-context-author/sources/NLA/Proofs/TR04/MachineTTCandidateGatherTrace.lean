import NLA.Proofs.TR04.MachineTTCandidateGatherScalar

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def ttCandidateGatherParameters (s : State ttProgram) : FrameGatherParameters :=
  ⟨s.natural 81, s.natural 77, s.natural 78, s.natural 79, s.natural 76, s.natural 72, s.natural 67⟩

def ttCandidateGatherAux (s : State ttProgram) : Fin 5 → ℕ :=
  ![s.natural 35, s.natural 36, s.natural 37, s.natural 38, s.natural 39]

def TTCandidateOutsideBank (j : Fin 128) : Prop := j.val < 26 ∨ 41 ≤ j.val

def TTCandidateOutsideResult (j : Fin 128) : Prop :=
  j ≠ 84 ∧ j ≠ 85 ∧ j ≠ 86 ∧ j ≠ 87 ∧ j ≠ 88 ∧
    j ≠ 94 ∧ j ≠ 89 ∧ j ≠ 90 ∧ j ≠ 108

def TTCandidateProtectedNat (j : Fin 128) : Prop := TTCandidateOutsideBank j ∧ TTCandidateOutsideResult j

structure TTCandidateMetadataFields (s t : State ttProgram) : Prop where
  level : t.natural 84 = 0
  rows : t.natural 85 = s.natural 81
  width : t.natural 86 = s.natural 106
  cols : t.natural 87 = s.natural 82
  stride : t.natural 88 = s.natural 106
  frame : t.natural 94 = s.natural 67
  input : t.natural 89 = s.natural 92
  output : t.natural 90 = s.natural 69
  tag : t.natural 108 = 0

theorem ttCandidateMetadata_fields (s : State ttProgram) :
    TTCandidateMetadataFields s (ttCandidateMetadataResult s) := by constructor <;> rfl

theorem ttCandidate_entry_outside (s : State ttProgram) (j : Fin 128)
    (hj : TTCandidateOutsideBank j) : (ttCandidateEntryResult s).natural j = s.natural j := by
  have hne : ∀ a : Fin 128, 26 ≤ a.val → a.val < 41 → j ≠ a := by
    intro a ha hb he
    have hv := congrArg Fin.val he
    unfold TTCandidateOutsideBank at hj
    omega
  change (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update s.natural 27 (s.natural 81)) 28 (s.natural 77)) 29 (s.natural 78)) 30 (s.natural 79)) 31 (s.natural 76)) 32 (s.natural 72)) 33 (s.natural 67)) j = s.natural j
  calc
    _ = (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update s.natural 27 (s.natural 81)) 28 (s.natural 77)) 29 (s.natural 78)) 30 (s.natural 79)) 31 (s.natural 76)) 32 (s.natural 72)) j := Function.update_of_ne (hne 33 (by decide) (by decide)) _ _
    _ = (Function.update (Function.update (Function.update (Function.update (Function.update s.natural 27 (s.natural 81)) 28 (s.natural 77)) 29 (s.natural 78)) 30 (s.natural 79)) 31 (s.natural 76)) j := Function.update_of_ne (hne 32 (by decide) (by decide)) _ _
    _ = (Function.update (Function.update (Function.update (Function.update s.natural 27 (s.natural 81)) 28 (s.natural 77)) 29 (s.natural 78)) 30 (s.natural 79)) j := Function.update_of_ne (hne 31 (by decide) (by decide)) _ _
    _ = (Function.update (Function.update (Function.update s.natural 27 (s.natural 81)) 28 (s.natural 77)) 29 (s.natural 78)) j := Function.update_of_ne (hne 30 (by decide) (by decide)) _ _
    _ = (Function.update (Function.update s.natural 27 (s.natural 81)) 28 (s.natural 77)) j := Function.update_of_ne (hne 29 (by decide) (by decide)) _ _
    _ = (Function.update s.natural 27 (s.natural 81)) j := Function.update_of_ne (hne 28 (by decide) (by decide)) _ _
    _ = s.natural j := Function.update_of_ne (hne 27 (by decide) (by decide)) _ _

theorem ttCandidate_result_outside (s : State ttProgram) (j : Fin 128)
    (hj : TTCandidateOutsideResult j) : (ttCandidateMetadataResult s).natural j = s.natural j := by
  change (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update s.natural 84 (0)) 85 (s.natural 81)) 86 (s.natural 106)) 87 (s.natural 82)) 88 (s.natural 106)) 94 (s.natural 67)) 89 (s.natural 92)) 90 (s.natural 69)) 108 (0)) j = s.natural j
  calc
    _ = (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update s.natural 84 (0)) 85 (s.natural 81)) 86 (s.natural 106)) 87 (s.natural 82)) 88 (s.natural 106)) 94 (s.natural 67)) 89 (s.natural 92)) 90 (s.natural 69)) j := Function.update_of_ne hj.2.2.2.2.2.2.2.2 _ _
    _ = (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update s.natural 84 (0)) 85 (s.natural 81)) 86 (s.natural 106)) 87 (s.natural 82)) 88 (s.natural 106)) 94 (s.natural 67)) 89 (s.natural 92)) j := Function.update_of_ne hj.2.2.2.2.2.2.2.1 _ _
    _ = (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update s.natural 84 (0)) 85 (s.natural 81)) 86 (s.natural 106)) 87 (s.natural 82)) 88 (s.natural 106)) 94 (s.natural 67)) j := Function.update_of_ne hj.2.2.2.2.2.2.1 _ _
    _ = (Function.update (Function.update (Function.update (Function.update (Function.update s.natural 84 (0)) 85 (s.natural 81)) 86 (s.natural 106)) 87 (s.natural 82)) 88 (s.natural 106)) j := Function.update_of_ne hj.2.2.2.2.2.1 _ _
    _ = (Function.update (Function.update (Function.update (Function.update s.natural 84 (0)) 85 (s.natural 81)) 86 (s.natural 106)) 87 (s.natural 82)) j := Function.update_of_ne hj.2.2.2.2.1 _ _
    _ = (Function.update (Function.update (Function.update s.natural 84 (0)) 85 (s.natural 81)) 86 (s.natural 106)) j := Function.update_of_ne hj.2.2.2.1 _ _
    _ = (Function.update (Function.update s.natural 84 (0)) 85 (s.natural 81)) j := Function.update_of_ne hj.2.2.1 _ _
    _ = (Function.update s.natural 84 (0)) j := Function.update_of_ne hj.2.1 _ _
    _ = s.natural j := Function.update_of_ne hj.1 _ _

theorem ttCandidateGather_relates (s : State ttProgram) (hs : s.status = .running) :
    ttGatherEmbedding.Relates
      (frameGatherStart s.memory (ttCandidateGatherParameters s) (ttCandidateGatherAux s)
        (s.natural 26) (s.natural 34) (s.natural 40) (s.real 6))
      (ttCandidateEntryResult s) := by
  constructor
  · rfl
  · funext i; fin_cases i; rfl
  · funext i; fin_cases i <;> rfl
  · rfl
  · exact hs

theorem ttCandidateGather_bank_outside (memory : ℕ → ℝ) (P : FrameGatherParameters) (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (aux : Fin 5 → ℕ) (rowScratch widthScratch writeScratch : ℕ) (value : ℝ)
    {start : State ttProgram} {trace : Trace ttProgram} (ht : LegalTrace ttProgram start trace)
    (offset : ℕ)
    (hs : ttGatherEmbedding.Relates (frameGatherStart memory P aux rowScratch widthScratch writeScratch value)
      (trace.state offset)) :
    let n := offset + (P.rows * (11 * P.width + 7) + 4)
    (∀ j : Fin 128, TTCandidateOutsideBank j → (trace.state n).natural j = (trace.state offset).natural j) ∧
    (∀ j : Fin 16, j ≠ 6 → (trace.state n).real j = (trace.state offset).real j) := by
  obtain ⟨aux', v, hv⟩ := frameGatherProgram_return memory P hP hd aux rowScratch widthScratch writeScratch value
  have hn := ordinary_nohalt_prefix_of_running (frameGatherStart memory P aux rowScratch widthScratch writeScratch value)
    (P.rows * (11 * P.width + 7) + 4) (by rw [hv]; rfl)
  constructor
  · intro j hj
    have hj' : ∀ i, j ≠ ttGatherEmbedding.naturals i := by
      intro i he
      have hv := congrArg Fin.val he
      have hi := i.isLt
      change j.val = 26 + i.val at hv
      change i.val < 15 at hi
      unfold TTCandidateOutsideBank at hj
      omega
    exact ttGatherEmbedding.scalar_trace_natural_outside _ hs (legalTrace_shift ht offset)
      _ hn (fun _ _ => frameGatherProgram_scalar _) j hj'
  · intro j hj
    have hj' : ∀ i, j ≠ ttGatherEmbedding.reals i := by
      intro i
      fin_cases i
      exact hj
    exact ttGatherEmbedding.scalar_trace_real_outside _ hs (legalTrace_shift ht offset)
      _ hn (fun _ _ => frameGatherProgram_scalar _) j hj'

#assert_trust kernel ttCandidateMetadata_fields
#assert_trust kernel ttCandidate_entry_outside
#assert_trust kernel ttCandidate_result_outside
#assert_trust kernel ttCandidateGather_relates
#assert_trust kernel ttCandidateGather_bank_outside
#print axioms ttCandidateGather_bank_outside
end NLA.Proofs.TR04
