import NLA.Proofs.TR04.MachineTTCandidateGatherMemory

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat TensorFormat.TTStrict

/-- Candidate j is materialized from the exact deterministic family before any
future child SVD reply. All destination-exterior cells and caller globals are
preserved, and the real register exception is exactly gather scratch6. -/
theorem ttCandidateGather_explicit {start : State ttProgram} {trace : Trace ttProgram}
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
  let C := ttFirstChoice sigma hvalid.2.2.2.1 (s.natural 80)
    (min (s.natural 80) (min (s.natural 81) (s.natural 82))) hr
  let F := explicitFirstFrames hvalid (s.natural 80)
  let P := ttCandidateGatherParameters s
  obtain ⟨hc, hw, hframes⟩ := ttFirstChoice_realizes_explicit hvalid (s.natural 80) hr (s.natural 72) (s.natural 67)
  have hjC : s.natural 76 < C.count := by rw [←hselected.2.2.2]; exact hj
  let jC : Fin C.count := ⟨s.natural 76, hjC⟩
  obtain ⟨hPspec, hmatch⟩ := hframes jC
  have hp : P = ttFirstGatherParameters (s.natural 81) C jC.val (s.natural 72) (s.natural 67) := by
    unfold P ttCandidateGatherParameters ttFirstGatherParameters
    rw [hselected.1, hselected.2.1, hselected.2.2.1]
  have hP : P.Valid := by rw [hp]; exact hPspec
  have hwidth : P.width = F.width := by rw [hp]; exact hw
  have hq : s.natural 106 = P.width := by
    rw [hp]
    exact hcap.trans (ttFirstChoice_width sigma hvalid.2.2.2.1 (s.natural 80) hr).symm
  have hqF : s.natural 106 = F.width := hq.trans hwidth
  have hdP : DisjointBlocks (s.natural 72) (s.natural 81 * s.natural 81)
      (s.natural 67) (s.natural 81 * P.width) := by rw [←hq]; exact hd
  obtain ⟨hlabel, hrun, hm, hfields, hnat, hreal, hcost⟩ :=
    ttCandidateGather_run ht offset s he hl hs hj hP hdP
  have hmem : StoresFrame (trace.state (offset + (P.rows * (11 * P.width + 7) + 24))).memory
      P.outputBase P.width (frameGatherMatrix P hP U) := by
    rw [hm]
    exact ttCandidateGather_frame_memory s.memory P hP U hU
  have hmatch' : (frameGatherMatrix P hP U).submatrix id (Fin.cast hwidth.symm) = F.frame (Fin.cast hc jC) := by
    ext i k
    have hh := congrFun (congrFun hmatch i) k
    change U i ⟨_, _⟩ = _ at hh ⊢
    convert hh using 1
    congr 1
    apply Fin.ext
    change P.column k.val = (ttFirstGatherParameters (s.natural 81) C jC.val (s.natural 72) (s.natural 67)).column k.val
    exact congrArg (fun T : FrameGatherParameters => T.column k.val) hp
  have hsframe : StoresFrame (trace.state (offset + (P.rows * (11 * P.width + 7) + 24))).memory
      P.outputBase F.width (F.frame (Fin.cast hc jC)) := by
    intro i k
    have ha : P.outputBase + i.val * F.width + k.val =
        P.outputBase + i.val * P.width + (Fin.cast hwidth.symm k).val := by
      change P.outputBase + i.val * F.width + k.val = P.outputBase + i.val * P.width + k.val
      rw [hwidth]
    rw [ha]
    exact (hmem i (Fin.cast hwidth.symm k)).trans (congrFun (congrFun hmatch' i) k)
  have hout : ∀ a, ¬(P.outputBase ≤ a ∧ a < P.outputBase + P.rows * P.width) →
      (trace.state (offset + (P.rows * (11 * P.width + 7) + 24))).memory a = s.memory a := by
    intro a ha
    rw [hm]
    exact frameGatherMemory_outside s.memory P _ a ha
  have htime : P.rows * (11 * P.width + 7) + 24 = s.natural 81 * (11 * s.natural 106 + 7) + 24 := by
    rw [←hq]
    rfl
  rw [htime] at hlabel hrun hm hfields hnat hreal hcost hsframe hout
  refine ⟨Fin.cast hc jC, rfl, hqF, hlabel, hrun, hsframe, ?_, ?_, hfields, hnat, hreal, hcost⟩
  · calc
      _ = frameGatherMemory s.memory P (P.rows * P.width) := hm
      _ = frameGatherMemory s.memory P (s.natural 81 * s.natural 106) := by
        congr 1
        rw [←hq]
        rfl
  · intro a ha
    apply hout a
    change ¬(s.natural 67 ≤ a ∧ a < s.natural 67 + s.natural 81 * P.width)
    rw [←hq]
    exact ha

#assert_trust kernel ttCandidateGather_explicit
#print axioms ttCandidateGather_explicit
end NLA.Proofs.TR04
