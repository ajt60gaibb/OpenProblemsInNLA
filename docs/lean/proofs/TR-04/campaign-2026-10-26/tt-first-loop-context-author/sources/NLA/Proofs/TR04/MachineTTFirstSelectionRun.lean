import NLA.Proofs.TR04.MachineTTFirstSelectionTrace

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

theorem ttFirstSelection_large_run {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 168) (hs : s.status = .running)
    (hr : s.natural 105 < s.natural 80) :
    trace.state (offset + 6) = ttFirstPrefixResult s ∧
      TTFirstPreserves s (trace.state (offset + 6)) ∧
      CostThrough ttProgram trace (offset + 6) ≤ CostThrough ttProgram trace offset + 6 := by
  obtain ⟨hx, hc⟩ := trace_scalar_block_at ht offset 6 (by
    rw [he]
    exact fun k hk _ => ttFirstSelection_large_safe s hl hs hr k hk)
  rw [he, ttFirstSelection_large_six s hl hs hr] at hx
  exact ⟨hx, hx ▸ ttFirstPrefix_preserves s, hc⟩

theorem ttFirstSelection_nonpositive_run {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 168) (hs : s.status = .running)
    (hr : ¬s.natural 105 < s.natural 80)
    (hz : ¬(s.natural 127 : ℝ) < s.memory (s.natural 73 + (s.natural 80 - 1))) :
    trace.state (offset + 12) = ttFirstPrefixResult {ttFirstThresholdRead s with label := 184} ∧
      TTFirstPreserves s (trace.state (offset + 12)) ∧
      CostThrough ttProgram trace (offset + 12) ≤ CostThrough ttProgram trace offset + 12 := by
  obtain ⟨hx, hc⟩ := trace_scalar_block_at ht offset 12 (by
    rw [he]
    exact fun k hk _ => ttFirstSelection_nonpositive_safe s hl hs hr hz k hk)
  rw [he, ttFirstSelection_nonpositive_twelve s hl hs hr hz] at hx
  refine ⟨hx, ?_, hc⟩
  rw [hx]
  exact ttFirstPreserves_trans (ttFirstRead_preserves s)
    (ttFirstPrefix_preserves {ttFirstThresholdRead s with label := 184})

/-- Every positive-threshold path runs the literal read-only bank, then copies
its three exact counts into the actual candidate-loop registers. -/
theorem ttFirstSelection_positive_run {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 168) (hs : s.status = .running)
    (hr : ¬s.natural 105 < s.natural 80)
    (hz : (s.natural 127 : ℝ) < s.memory (s.natural 73 + (s.natural 80 - 1))) :
    let P : ThresholdScanParameters := ⟨s.natural 105, s.natural 80, s.natural 73⟩
    let tau := s.memory (s.natural 73 + (s.natural 80 - 1))
    let n := offset + (9 * P.count + 23)
    (trace.state n).label = 189 ∧ (trace.state n).status = .running ∧
      (trace.state n).natural 77 = thresholdAboveCount s.memory P tau P.count ∧
      (trace.state n).natural 78 = thresholdTiedCount s.memory P tau P.count ∧
      (trace.state n).natural 79 = thresholdTakeCount s.memory P tau P.count ∧
      (trace.state n).natural 75 = thresholdTiedCount s.memory P tau P.count ∧
      TTFirstPreserves s (trace.state n) ∧
      CostThrough ttProgram trace n ≤ CostThrough ttProgram trace offset + (9 * P.count + 23) := by
  let P : ThresholdScanParameters := ⟨s.natural 105, s.natural 80, s.natural 73⟩
  let tau := s.memory (s.natural 73 + (s.natural 80 - 1))
  obtain ⟨hread, hc7⟩ := trace_scalar_block_at ht offset 7 (by
    rw [he]
    exact fun k hk _ => ttFirstSelection_read_safe s hl hs hr k hk)
  rw [he, ttFirstSelection_read_seven s hl hs hr hz] at hread
  have hstatus7 : (trace.state (offset + 7)).status = .running := by rw [hread]; exact hs
  have hlabel7 : (trace.state (offset + 7)).label = 175 := by rw [hread]; rfl
  obtain ⟨hentry, hc4⟩ := trace_scalar_block_at ht (offset + 7) 4
    (fun k hk _ => ttFirstSelection_setup_safe _ hlabel7 hstatus7 k hk)
  rw [ttFirstSelection_setup_four _ hlabel7 hstatus7, hread] at hentry
  have hbank : ttThresholdEmbedding.Relates
      (thresholdScanStart s.memory P tau (s.real 8) (ttFirstThresholdAux s))
      (trace.state (offset + 7 + 4)) := by
    rw [hentry]
    exact ttFirstThreshold_relates s hs
  obtain ⟨v, hret, hcscan⟩ := ttThresholdEmbedding.thresholdScan_run_at s.memory P tau
    (s.real 8) (ttFirstThresholdAux s) (offset + 7 + 4) hbank ht
  have hout := ttFirstThreshold_outside s.memory P tau (s.real 8) (ttFirstThresholdAux s)
    ht (offset + 7 + 4) hbank
  have hlabelret : (trace.state (offset + 7 + 4 + (9 * P.count + 6))).label = 88 := hret.label
  have hstatusret : (trace.state (offset + 7 + 4 + (9 * P.count + 6))).status = .running := hret.status
  obtain ⟨hresult, hc6⟩ := trace_scalar_block_at ht (offset + 7 + 4 + (9 * P.count + 6)) 6
    (fun k hk _ => ttFirstSelection_return_safe _ hlabelret hstatusret k hk)
  rw [ttFirstSelection_return_six _ hlabelret hstatusret] at hresult
  have hn : offset + 7 + 4 + (9 * P.count + 6) + 6 = offset + (9 * P.count + 23) := by omega
  rw [hn] at hresult hc6
  have h46 := hret.natural_apply 5
  have h47 := hret.natural_apply 6
  have h48 := hret.natural_apply 7
  change (trace.state _).natural 46 = thresholdAboveCount s.memory P tau P.count at h46
  change (trace.state _).natural 47 = thresholdTiedCount s.memory P tau P.count at h47
  change (trace.state _).natural 48 = thresholdTakeCount s.memory P tau P.count at h48
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hresult]; rfl
  · rw [hresult]; exact hstatusret
  · rw [hresult]; simpa [ttFirstCountResult, Function.update_apply] using h46
  · rw [hresult]; simpa [ttFirstCountResult, Function.update_apply] using h47
  · rw [hresult]; simpa [ttFirstCountResult, Function.update_apply] using h48
  · rw [hresult]; simpa [ttFirstCountResult, Function.update_apply] using h47
  · have hentrypres := ttFirstPreserves_trans (ttFirstRead_preserves s)
      (ttFirstEntry_preserves (ttFirstThresholdRead s))
    have hscanpres : TTFirstPreserves (trace.state (offset + 7 + 4))
        (trace.state (offset + 7 + 4 + (9 * P.count + 6))) := by
      refine ⟨?_, fun j hj => hout j hj.1⟩
      exact hret.memory.trans hbank.memory.symm
    rw [hentry] at hscanpres
    have hpre := ttFirstPreserves_trans hentrypres hscanpres
    have hfinal := ttFirstCount_preserves (trace.state (offset + 7 + 4 + (9 * P.count + 6)))
    rw [←hresult] at hfinal
    exact ttFirstPreserves_trans hpre hfinal
  · dsimp only [P] at hcscan hc6 ⊢
    omega

#assert_trust kernel ttFirstSelection_large_run
#assert_trust kernel ttFirstSelection_nonpositive_run
#assert_trust kernel ttFirstSelection_positive_run
#print axioms ttFirstSelection_positive_run
end NLA.Proofs.TR04
