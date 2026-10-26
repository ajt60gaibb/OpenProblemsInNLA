import NLA.Proofs.TR04.MachineTTCandidateGatherTrace

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

/-- Actual candidate entry, finite gather bank, and return to metadata241. -/
theorem ttCandidateGather_run {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 189) (hs : s.status = .running)
    (hj : s.natural 76 < s.natural 75)
    (hP : (ttCandidateGatherParameters s).Valid)
    (hd : DisjointBlocks (s.natural 72) (s.natural 81 * s.natural 81)
      (s.natural 67) (s.natural 81 * (ttCandidateGatherParameters s).width)) :
    let P := ttCandidateGatherParameters s
    let n := offset + (P.rows * (11 * P.width + 7) + 24)
    (trace.state n).label = 241 ∧ (trace.state n).status = .running ∧
      (trace.state n).memory = frameGatherMemory s.memory P (P.rows * P.width) ∧
      TTCandidateMetadataFields s (trace.state n) ∧
      (∀ j : Fin 128, TTCandidateProtectedNat j → (trace.state n).natural j = s.natural j) ∧
      (∀ j : Fin 16, j ≠ 6 → (trace.state n).real j = s.real j) ∧
      CostThrough ttProgram trace n ≤ CostThrough ttProgram trace offset + (P.rows * (11 * P.width + 7) + 24) := by
  let P := ttCandidateGatherParameters s
  obtain ⟨hentry, hc9⟩ := ttCandidate_entry_at ht offset (by rw [he]; exact hl)
    (by rw [he]; exact hs) (by rw [he]; exact hj)
  rw [he] at hentry
  have hbank : ttGatherEmbedding.Relates
      (frameGatherStart s.memory P (ttCandidateGatherAux s) (s.natural 26) (s.natural 34) (s.natural 40) (s.real 6))
      (trace.state (offset + 9)) := by
    rw [hentry]
    exact ttCandidateGather_relates s hs
  obtain ⟨aux', value, hret, hcGather⟩ := ttGatherEmbedding.frameGather_run_at s.memory P hP hd
    (ttCandidateGatherAux s) (s.natural 26) (s.natural 34) (s.natural 40) (s.real 6) (offset + 9) hbank ht
  have hout := ttCandidateGather_bank_outside s.memory P hP hd (ttCandidateGatherAux s)
    (s.natural 26) (s.natural 34) (s.natural 40) (s.real 6) ht (offset + 9) hbank
  let u := trace.state (offset + 9 + (P.rows * (11 * P.width + 7) + 4))
  have hul : u.label = 65 := hret.label
  have hus : u.status = .running := hret.status
  obtain ⟨hresult, hc11⟩ := ttCandidate_return_at ht (offset + 9 + (P.rows * (11 * P.width + 7) + 4)) hul hus
  have hn : offset + 9 + (P.rows * (11 * P.width + 7) + 4) + 11 =
      offset + (P.rows * (11 * P.width + 7) + 24) := by omega
  rw [hn] at hresult hc11
  have hpres (j : Fin 128) (hj : TTCandidateOutsideBank j) : u.natural j = s.natural j := by
    exact (hout.1 j hj).trans (by rw [hentry]; exact ttCandidate_entry_outside s j hj)
  have hf := ttCandidateMetadata_fields u
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hresult]; rfl
  · rw [hresult]; exact hus
  · rw [hresult]; exact hret.memory
  · rw [hresult]
    exact ⟨hf.level, hf.rows.trans (hpres 81 (by unfold TTCandidateOutsideBank; decide)), hf.width.trans (hpres 106 (by unfold TTCandidateOutsideBank; decide)),
      hf.cols.trans (hpres 82 (by unfold TTCandidateOutsideBank; decide)), hf.stride.trans (hpres 106 (by unfold TTCandidateOutsideBank; decide)),
      hf.frame.trans (hpres 67 (by unfold TTCandidateOutsideBank; decide)), hf.input.trans (hpres 92 (by unfold TTCandidateOutsideBank; decide)),
      hf.output.trans (hpres 69 (by unfold TTCandidateOutsideBank; decide)), hf.tag⟩
  · intro j hj
    rw [hresult]
    exact (ttCandidate_result_outside u j hj.2).trans (hpres j hj.1)
  · intro j hj
    rw [hresult]
    exact (hout.2 j hj).trans (by rw [hentry]; rfl)
  · dsimp only [P] at hcGather hc11 ⊢
    omega

theorem ttCandidateGather_time_le_quadratic (m q bound : ℕ) (hm : m ≤ bound) (hq : q ≤ bound) :
    m * (11 * q + 7) + 24 ≤ 24 * (bound + 1)^2 := by
  have hprod := Nat.mul_le_mul hm hq
  nlinarith

#assert_trust kernel ttCandidateGather_run
#assert_trust kernel ttCandidateGather_time_le_quadratic
#print axioms ttCandidateGather_run
end NLA.Proofs.TR04
