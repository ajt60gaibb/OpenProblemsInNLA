import NLA.Proofs.TR04.MachineTTChildInitializationCalls

/-! Read-only child setup at the literal controller labels. The three decoded
headers determine the SVD dimensions and cap; no matrix evaluator is assumed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

structure TTChildInitialized (s t : State ttProgram) (mode rank : ℕ) (values : ℕ → ℕ) : Prop where
  label : t.label = 237
  running : t.status = .running
  preserves : TTChildPreserves s t
  rows : t.natural 85 = s.natural 100 * mode
  columns : t.natural 87 = headerRangeProduct values (s.natural 84 + 1) (s.natural 0)
  cap : t.natural 86 = min rank (min (s.natural 100 * mode)
    (headerRangeProduct values (s.natural 84 + 1) (s.natural 0)))
  frame : t.natural 94 = s.natural 67 + s.natural 84 * s.natural 66
  modeValue : t.natural 109 = mode
  rankValue : t.natural 2 = rank

/-- Every legal caller trace follows the actual mode/range/rank decoders and
reaches the child SVD instruction. All dimensions, including zero, are allowed. -/
theorem ttChild_initialize_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset mode rank : ℕ) (values : ℕ → ℕ)
    (hl : (trace.state offset).label = 208) (hs : (trace.state offset).status = .running)
    (had : (trace.state offset).natural 84 + 1 ≤ (trace.state offset).natural 0)
    (hmode : (trace.state offset).memory ((trace.state offset).natural 84) = (mode : ℝ))
    (hrank : (trace.state offset).memory ((trace.state offset).natural 0 + (trace.state offset).natural 84) = (rank : ℝ))
    (hvalues : ∀ j, (trace.state offset).natural 84 + 1 ≤ j → j < (trace.state offset).natural 0 →
      (trace.state offset).memory j = (values j : ℝ)) :
    ∃ elapsed : ℕ, elapsed ≤ 3 * mode + 3 * rank +
        headerRangeTime values ((trace.state offset).natural 84 + 1) ((trace.state offset).natural 0) + 78 ∧
      TTChildInitialized (trace.state offset) (trace.state (offset + elapsed)) mode rank values ∧
      CostThrough ttProgram trace (offset + elapsed) ≤ CostThrough ttProgram trace offset +
        (3 * mode + 3 * rank + headerRangeTime values ((trace.state offset).natural 84 + 1)
          ((trace.state offset).natural 0) + 78) := by
  let s := trace.state offset
  let time1 := offset + (3 * mode + 22)
  obtain ⟨h1l,h1s,h1p,h1v,h1c⟩ := ttChild_mode_call_at ht offset mode hl hs hmode
  have h1level : (trace.state time1).natural 84 = s.natural 84 := h1p.2 84 (by unfold TTChildKept; decide)
  have h1order : (trace.state time1).natural 0 = s.natural 0 := h1p.2 0 (by unfold TTChildKept; decide)
  have h1prev : (trace.state time1).natural 100 = s.natural 100 := h1p.2 100 (by unfold TTChildKept; decide)
  have ha1 : (trace.state time1).natural 84 + 1 ≤ (trace.state time1).natural 0 := by rw [h1level,h1order]; exact had
  have hm1 : ∀ j, (trace.state time1).natural 84 + 1 ≤ j → j < (trace.state time1).natural 0 →
      (trace.state time1).memory j = (values j : ℝ) := by
    intro j hj hk
    rw [h1p.1]
    exact hvalues j (by rwa [h1level] at hj) (by rwa [h1order] at hk)
  obtain ⟨h2l,h2s,h2p,h2v,h2rows,h2mode,h2c⟩ := ttChild_suffix_call_at ht time1 values h1l h1s ha1 hm1
  simp only [h1level,h1order] at h2l h2s h2p h2v h2rows h2mode h2c
  rw [h1prev,h1v] at h2rows
  rw [h1v] at h2mode
  let time2 := time1 + (headerRangeTime values (s.natural 84 + 1) (s.natural 0) + 21)
  change (trace.state time2).label = 222 at h2l
  change (trace.state time2).status = .running at h2s
  change TTChildPreserves (trace.state time1) (trace.state time2) at h2p
  have hp2 : TTChildPreserves s (trace.state time2) := ttChildPreserves_trans h1p h2p
  have hm2 : (trace.state time2).memory ((trace.state time2).natural 0 + (trace.state time2).natural 84) = (rank : ℝ) := by
    rw [hp2.1,hp2.2 0 (by unfold TTChildKept; decide),hp2.2 84 (by unfold TTChildKept; decide)]
    exact hrank
  obtain ⟨h3l,h3s,h3p,h3v,h3cols,h3rows,h3mode,h3c⟩ := ttChild_rank_call_at ht time2 rank h2l h2s hm2
  let time3 := time2 + (3 * rank + 28)
  change (trace.state time3).label = 230 at h3l
  change (trace.state time3).status = .running at h3s
  obtain ⟨n,hn,hv,h4p,h4c⟩ := ttChild_cap_at ht time3 h3l h3s
  have hp3 : TTChildPreserves s (trace.state time3) := ttChildPreserves_trans hp2 h3p
  have hp4 := ttChildPreserves_trans hp3 h4p
  have hrows : (trace.state time3).natural 85 = s.natural 100 * mode := h3rows.trans h2rows
  have hcols : (trace.state time3).natural 87 = headerRangeProduct values (s.natural 84+1) (s.natural 0) := h3cols.trans h2v
  have hmode3 : (trace.state time3).natural 109 = mode := h3mode.trans h2mode
  have heTime : time3 + n = offset + ((3*mode+22) +
      (headerRangeTime values (s.natural 84+1) (s.natural 0)+21) + (3*rank+28) + n) := by dsimp [time3,time2,time1]; omega
  refine ⟨(3*mode+22) + (headerRangeTime values (s.natural 84+1) (s.natural 0)+21) + (3*rank+28) + n,
    by dsimp [s]; omega, ?_, ?_⟩
  · rw [← heTime,hv]
    obtain ⟨hcl,hcc,hcf,hcr,hcp,hcm,hcv⟩ := ttChild_cap_fields (trace.state time3)
    refine ⟨hcl, h3s, ?_, hcr.trans hrows, hcp.trans hcols, ?_, ?_, hcm.trans hmode3, hcv.trans h3v⟩
    · rw [← hv]; exact hp4
    · rw [hcc,h3v,hrows,hcols]
    · rw [hcf,hp3.2 67 (by unfold TTChildKept; decide),hp3.2 84 (by unfold TTChildKept; decide),
        hp3.2 66 (by unfold TTChildKept; decide)]
  · rw [← heTime]
    dsimp [time3,time2,time1,s] at h1c h2c h3c h4c ⊢
    omega

#assert_trust kernel ttChild_initialize_at
#print axioms ttChild_initialize_at
end NLA.Proofs.TR04
