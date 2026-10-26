import NLA.Proofs.TR04.MachineTTCandidateGatherProtection
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
open NLA.Proofs.TR04 NLA.Computation.SVDMachine
open NLA.Proofs.TR04.TensorFormat NLA.Proofs.TR04.TensorFormat.TTStrict NLA.Proofs.TR04.TTMemoryLayout
namespace CandidateGatherExactConsumer
theorem literal_saved_inputs_exact_candidate {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 189) (hs : s.status = .running)
    {B : Matrix (Fin (s.natural 81)) (Fin (s.natural 82)) ℝ}
    {U : Matrix (Fin (s.natural 81)) (Fin (s.natural 81)) ℝ}
    {sigma : Fin (min (s.natural 81) (s.natural 82)) → ℝ}
    {V : Matrix (Fin (s.natural 82)) (Fin (s.natural 82)) ℝ}
    (hvalid : ValidSVD B U sigma V) (hr : 1 ≤ s.natural 80)
    (hcap : s.natural 106 = min (s.natural 80) (min (s.natural 81) (s.natural 82)))
    (hselected : TTFirstSelected (ttFirstChoice sigma hvalid.2.2.2.1 (s.natural 80)
      (min (s.natural 80) (min (s.natural 81) (s.natural 82))) hr) s)
    (hj : s.natural 76 < s.natural 75)
    (hU : StoresFrame s.memory (s.natural 72) (s.natural 81) U)
    (hsigma : ∀ k, s.memory (s.natural 73 + k.val) = sigma k)
    (hV : readMatrix s.memory (s.natural 82) (s.natural 82) (s.natural 74) = V)
    (L : Layout) (hrows : s.natural 81 ≤ L.entries) (hwidth : s.natural 106 ≤ L.entries)
    (hcols : s.natural 82 ≤ L.entries)
    (hUbase : s.natural 72 = L.firstU) (hSbase : s.natural 73 = L.firstSigma)
    (hVbase : s.natural 74 = L.firstV) (hFbase : s.natural 67 = L.frames)
    (hIbase : s.natural 92 = L.input) :
    let F := explicitFirstFrames hvalid (s.natural 80)
    let time := s.natural 81 * (11 * s.natural 106 + 7) + 24
    let n := offset + time
    ∃ j : Fin F.count, j.val = s.natural 76 ∧ s.natural 106 = F.width ∧
      time ≤ 24 * (L.entries + 1)^2 ∧
      (trace.state n).label = 241 ∧ (trace.state n).status = .running ∧
      StoresFrame (trace.state n).memory (s.natural 67) F.width (F.frame j) ∧
      readMatrix (trace.state n).memory (s.natural 81) (s.natural 82) (s.natural 92) =
        readMatrix s.memory (s.natural 81) (s.natural 82) (s.natural 92) ∧
      readMatrix (trace.state n).memory (s.natural 81) (s.natural 81) (s.natural 72) = U ∧
      (∀ k, (trace.state n).memory (s.natural 73 + k.val) = sigma k) ∧
      readMatrix (trace.state n).memory (s.natural 82) (s.natural 82) (s.natural 74) = V ∧
      (∀ a, ¬(s.natural 67 ≤ a ∧ a < s.natural 67 + s.natural 81 * s.natural 106) →
        (trace.state n).memory a = s.memory a) ∧
      TTCandidateMetadataFields s (trace.state n) ∧
      (trace.state n).natural 85 ≤ L.entries ∧ (trace.state n).natural 86 ≤ L.entries ∧
      (trace.state n).natural 87 ≤ L.entries ∧ (trace.state n).natural 88 ≤ L.entries ∧
      (∀ k : Fin 128, TTCandidateProtectedNat k → (trace.state n).natural k = s.natural k) ∧
      (∀ k : Fin 16, k ≠ 6 → (trace.state n).real k = s.real k) ∧
      CostThrough ttProgram trace n ≤ CostThrough ttProgram trace offset + 24 * (L.entries + 1)^2 := by
  exact ttCandidateGather_protected ht offset s he hl hs hvalid hr hcap hselected hj hU hsigma hV L hrows hwidth hcols hUbase hSbase hVbase hFbase hIbase
#assert_trust kernel literal_saved_inputs_exact_candidate
#print axioms literal_saved_inputs_exact_candidate

theorem literal_actual_j_and_explicit_frame {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 189) (hs : s.status = .running)
    {B : Matrix (Fin (s.natural 81)) (Fin (s.natural 82)) ℝ}
    {U : Matrix (Fin (s.natural 81)) (Fin (s.natural 81)) ℝ}
    {sigma : Fin (min (s.natural 81) (s.natural 82)) → ℝ}
    {V : Matrix (Fin (s.natural 82)) (Fin (s.natural 82)) ℝ}
    (hvalid : ValidSVD B U sigma V) (hr : 1 ≤ s.natural 80)
    (hcap : s.natural 106 = min (s.natural 80) (min (s.natural 81) (s.natural 82)))
    (hselected : TTFirstSelected (ttFirstChoice sigma hvalid.2.2.2.1 (s.natural 80)
      (min (s.natural 80) (min (s.natural 81) (s.natural 82))) hr) s)
    (hj : s.natural 76 < s.natural 75)
    (hU : StoresFrame s.memory (s.natural 72) (s.natural 81) U)
    (hd : DisjointBlocks (s.natural 72) (s.natural 81 * s.natural 81)
      (s.natural 67) (s.natural 81 * s.natural 106)) :
    let F := explicitFirstFrames hvalid (s.natural 80)
    let n := offset + (s.natural 81 * (11 * s.natural 106 + 7) + 24)
    ∃ j : Fin F.count, j.val = s.natural 76 ∧
      s.natural 106 = F.width ∧
      (trace.state n).label = 241 ∧ (trace.state n).status = .running ∧
      StoresFrame (trace.state n).memory (s.natural 67) F.width (F.frame j) ∧
      (trace.state n).memory = frameGatherMemory s.memory (ttCandidateGatherParameters s)
        (s.natural 81 * s.natural 106) ∧
      (∀ a, ¬(s.natural 67 ≤ a ∧ a < s.natural 67 + s.natural 81 * s.natural 106) →
        (trace.state n).memory a = s.memory a) ∧
      TTCandidateMetadataFields s (trace.state n) ∧
      (∀ k : Fin 128, TTCandidateProtectedNat k → (trace.state n).natural k = s.natural k) ∧
      (∀ k : Fin 16, k ≠ 6 → (trace.state n).real k = s.real k) ∧
      CostThrough ttProgram trace n ≤ CostThrough ttProgram trace offset +
        (s.natural 81 * (11 * s.natural 106 + 7) + 24) := by
  exact ttCandidateGather_explicit ht offset s he hl hs hvalid hr hcap hselected hj hU hd
#assert_trust kernel literal_actual_j_and_explicit_frame
#print axioms literal_actual_j_and_explicit_frame

theorem literal_empty_gather_charge : 0 * (11 * 0 + 7) + 24 ≤ 24 * (0 + 1)^2 :=
  ttCandidateGather_time_le_quadratic 0 0 0 le_rfl le_rfl
#assert_trust kernel literal_empty_gather_charge
#print axioms literal_empty_gather_charge

theorem literal_candidate_branch_code : ttProgram.code 189 = .lessNat 76 75 190 357 := rfl
#assert_trust kernel literal_candidate_branch_code
#print axioms literal_candidate_branch_code

theorem literal_metadata_return_code : ttProgram.code 207 = .jump 241 := rfl
#assert_trust kernel literal_metadata_return_code
#print axioms literal_metadata_return_code
end CandidateGatherExactConsumer

#assert_trust kernel NLA.Proofs.TR04.ttCandidateEntryResult
#print axioms NLA.Proofs.TR04.ttCandidateEntryResult
#assert_trust kernel NLA.Proofs.TR04.ttCandidateMetadataResult
#print axioms NLA.Proofs.TR04.ttCandidateMetadataResult
#assert_trust kernel NLA.Proofs.TR04.ttCandidate_entry_nine
#print axioms NLA.Proofs.TR04.ttCandidate_entry_nine
#assert_trust kernel NLA.Proofs.TR04.ttCandidate_return_eleven
#print axioms NLA.Proofs.TR04.ttCandidate_return_eleven
#assert_trust kernel NLA.Proofs.TR04.ttCandidate_entry_at
#print axioms NLA.Proofs.TR04.ttCandidate_entry_at
#assert_trust kernel NLA.Proofs.TR04.ttCandidate_return_at
#print axioms NLA.Proofs.TR04.ttCandidate_return_at
#assert_trust kernel NLA.Proofs.TR04.ttCandidateGatherParameters
#print axioms NLA.Proofs.TR04.ttCandidateGatherParameters
#assert_trust kernel NLA.Proofs.TR04.ttCandidateGatherAux
#print axioms NLA.Proofs.TR04.ttCandidateGatherAux
#assert_trust kernel NLA.Proofs.TR04.TTCandidateOutsideBank
#print axioms NLA.Proofs.TR04.TTCandidateOutsideBank
#assert_trust kernel NLA.Proofs.TR04.TTCandidateOutsideResult
#print axioms NLA.Proofs.TR04.TTCandidateOutsideResult
#assert_trust kernel NLA.Proofs.TR04.TTCandidateProtectedNat
#print axioms NLA.Proofs.TR04.TTCandidateProtectedNat
#assert_trust kernel NLA.Proofs.TR04.TTCandidateMetadataFields
#print axioms NLA.Proofs.TR04.TTCandidateMetadataFields
#assert_trust kernel NLA.Proofs.TR04.ttCandidateMetadata_fields
#print axioms NLA.Proofs.TR04.ttCandidateMetadata_fields
#assert_trust kernel NLA.Proofs.TR04.ttCandidate_entry_outside
#print axioms NLA.Proofs.TR04.ttCandidate_entry_outside
#assert_trust kernel NLA.Proofs.TR04.ttCandidate_result_outside
#print axioms NLA.Proofs.TR04.ttCandidate_result_outside
#assert_trust kernel NLA.Proofs.TR04.ttCandidateGather_relates
#print axioms NLA.Proofs.TR04.ttCandidateGather_relates
#assert_trust kernel NLA.Proofs.TR04.ttCandidateGather_bank_outside
#print axioms NLA.Proofs.TR04.ttCandidateGather_bank_outside
#assert_trust kernel NLA.Proofs.TR04.ttCandidateGather_run
#print axioms NLA.Proofs.TR04.ttCandidateGather_run
#assert_trust kernel NLA.Proofs.TR04.ttCandidateGather_time_le_quadratic
#print axioms NLA.Proofs.TR04.ttCandidateGather_time_le_quadratic
#assert_trust kernel NLA.Proofs.TR04.ttCandidateGather_frame_memory
#print axioms NLA.Proofs.TR04.ttCandidateGather_frame_memory
#assert_trust kernel NLA.Proofs.TR04.ttCandidateGather_saved_block
#print axioms NLA.Proofs.TR04.ttCandidateGather_saved_block
#assert_trust kernel NLA.Proofs.TR04.ttCandidateGather_saved_matrix
#print axioms NLA.Proofs.TR04.ttCandidateGather_saved_matrix
#assert_trust kernel NLA.Proofs.TR04.ttCandidateGather_saved_tensor
#print axioms NLA.Proofs.TR04.ttCandidateGather_saved_tensor
#assert_trust kernel NLA.Proofs.TR04.ttCandidateGather_stored
#print axioms NLA.Proofs.TR04.ttCandidateGather_stored
#assert_trust kernel NLA.Proofs.TR04.ttCandidateGather_explicit
#print axioms NLA.Proofs.TR04.ttCandidateGather_explicit
#assert_trust kernel NLA.Proofs.TR04.ttCandidate_layout_saved
#print axioms NLA.Proofs.TR04.ttCandidate_layout_saved
#assert_trust kernel NLA.Proofs.TR04.ttCandidateGather_protected
#print axioms NLA.Proofs.TR04.ttCandidateGather_protected
