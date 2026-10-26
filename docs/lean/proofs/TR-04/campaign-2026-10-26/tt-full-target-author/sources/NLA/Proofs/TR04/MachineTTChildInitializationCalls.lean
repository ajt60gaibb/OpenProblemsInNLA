import NLA.Proofs.TR04.MachineTTChildInitializationHelpers

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

/-- Actual mode read/Single bank/tag4 dispatch, with no premise on other cells. -/
theorem ttChild_mode_call_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset value : ℕ)
    (hl : (trace.state offset).label = 208) (hs : (trace.state offset).status = .running)
    (hm : (trace.state offset).memory ((trace.state offset).natural 84) = (value : ℝ)) :
    let time := offset + (3 * value + 22)
    (trace.state time).label = 214 ∧ (trace.state time).status = .running ∧
      TTChildPreserves (trace.state offset) (trace.state time) ∧
      (trace.state time).natural 2 = value ∧
      CostThrough ttProgram trace time ≤ CostThrough ttProgram trace offset + (3 * value + 22) := by
  let s := trace.state offset
  obtain ⟨hv, hc⟩ := ttScalar_finish_at ht offset 6 (ttChildModeEntry s) (ttChild_mode_steps s hl hs) hs
  have he : ttHeaderEmbedding.Relates
      (headerProductDecodeState s.memory (s.natural 0) (s.natural 0) 1 value (s.real 1))
      (trace.state (offset + 6)) := by
    rw [hv]
    exact ttChildMode_relates s value hm hs
  obtain ⟨hr, hn, hcost⟩ := ttHeaderSingle_full_at ht (offset + 6) s.memory (s.natural 0) value (s.real 1) he
  let mid := offset + 6 + (3 * value + 5)
  have htag : (trace.state mid).natural 97 = 4 := by
    rw [hn 97 (by decide), hv]
    rfl
  obtain ⟨hdl, hds, hdp, hdout, hdcost⟩ := ttHeaderDispatch_call_at ht mid 4 hr.label hr.status htag
  change (trace.state (mid + 11)).label = 214 at hdl
  change (trace.state (mid + 11)).status = .running at hds
  change TTInitPreserves (trace.state mid) (trace.state (mid + 11)) at hdp
  change ∀ j : Fin 128, j ≠ 123 → (trace.state (mid + 11)).natural j = (trace.state mid).natural j at hdout
  change CostThrough ttProgram trace (mid + 11) ≤ CostThrough ttProgram trace mid + 11 at hdcost
  have hp0 : TTChildPreserves s (trace.state (offset + 6)) := by rw [hv]; exact ttChild_mode_preserves s
  have hp1 : TTChildPreserves (trace.state (offset + 6)) (trace.state mid) :=
    ttChild_header_preserves (hr.memory.trans he.memory.symm)
      ((hr.natural_apply 0).trans (he.natural_apply 0).symm) hn
  have hp2 : TTChildPreserves (trace.state mid) (trace.state (mid + (2 * 4 + 3))) :=
    ⟨hdp.1, fun j hj => hdout j hj.2.2.2.2.2.2.2.2.2.2⟩
  have hvalue : (trace.state (mid + (2 * 4 + 3))).natural 2 = value :=
    (hdout 2 (by decide)).trans (hr.natural_apply 2)
  have htime : mid + (2 * 4 + 3) = offset + (3 * value + 22) := by dsimp [mid]; omega
  rw [htime] at hdl hds hp2 hvalue hdcost
  exact ⟨hdl, hds, ttChildPreserves_trans hp0 (ttChildPreserves_trans hp1 hp2), hvalue, by dsimp [mid,s] at hcost hdcost; omega⟩

/-- Actual suffix-range call and tag5 dispatch preserve all caller globals. -/
theorem ttChild_suffix_call_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (values : ℕ → ℕ)
    (hl : (trace.state offset).label = 214) (hs : (trace.state offset).status = .running)
    (had : (trace.state offset).natural 84 + 1 ≤ (trace.state offset).natural 0)
    (hm : ∀ j, (trace.state offset).natural 84 + 1 ≤ j → j < (trace.state offset).natural 0 →
      (trace.state offset).memory j = (values j : ℝ)) :
    let time := offset + (headerRangeTime values ((trace.state offset).natural 84 + 1)
      ((trace.state offset).natural 0) + 21)
    (trace.state time).label = 222 ∧ (trace.state time).status = .running ∧
      TTChildPreserves (trace.state offset) (trace.state time) ∧
      (trace.state time).natural 2 = headerRangeProduct values ((trace.state offset).natural 84 + 1)
        ((trace.state offset).natural 0) ∧
      (trace.state time).natural 85 = (trace.state offset).natural 100 * (trace.state offset).natural 2 ∧
      (trace.state time).natural 109 = (trace.state offset).natural 2 ∧
      CostThrough ttProgram trace time ≤ CostThrough ttProgram trace offset +
        (headerRangeTime values ((trace.state offset).natural 84 + 1) ((trace.state offset).natural 0) + 21) := by
  let s := trace.state offset
  obtain ⟨hv, hc⟩ := ttScalar_finish_at ht offset 8 (ttChildSuffixEntry s) (ttChild_suffix_steps s hl hs) hs
  have he : ttHeaderEmbedding.Relates
      (headerRangeEntryState s.memory (s.natural 0) (s.natural 84 + 1) values 0
        (fun i => s.real (ttHeaderEmbedding.reals i))) (trace.state (offset + 8)) := by
    rw [hv]
    exact ttChildSuffix_relates s values hs
  obtain ⟨last, reals, hr, hn, hcost⟩ := ttHeaderRange_full_at ht (offset + 8) s.memory (s.natural 0)
    (s.natural 84 + 1) values had hm 0 (fun i => s.real (ttHeaderEmbedding.reals i)) he
  let mid := offset + 8 + headerRangeTime values (s.natural 84 + 1) (s.natural 0)
  have htag : (trace.state mid).natural 97 = 5 := by rw [hn 97 (by decide), hv]; rfl
  obtain ⟨hdl, hds, hdp, hdout, hdcost⟩ := ttHeaderDispatch_call_at ht mid 5 hr.label hr.status htag
  change (trace.state (mid + 13)).label = 222 at hdl
  change (trace.state (mid + 13)).status = .running at hds
  change TTInitPreserves (trace.state mid) (trace.state (mid + 13)) at hdp
  change ∀ j : Fin 128, j ≠ 123 → (trace.state (mid + 13)).natural j = (trace.state mid).natural j at hdout
  change CostThrough ttProgram trace (mid + 13) ≤ CostThrough ttProgram trace mid + 13 at hdcost
  have hp0 : TTChildPreserves s (trace.state (offset + 8)) := by rw [hv]; exact ttChild_suffix_preserves s
  have hp1 : TTChildPreserves (trace.state (offset + 8)) (trace.state mid) :=
    ttChild_header_preserves (hr.memory.trans he.memory.symm)
      ((hr.natural_apply 0).trans (he.natural_apply 0).symm) hn
  have hp2 : TTChildPreserves (trace.state mid) (trace.state (mid + (2 * 5 + 3))) :=
    ⟨hdp.1, fun j hj => hdout j hj.2.2.2.2.2.2.2.2.2.2⟩
  have hvalue : (trace.state (mid + (2 * 5 + 3))).natural 2 =
      headerRangeProduct values (s.natural 84 + 1) (s.natural 0) :=
    (hdout 2 (by decide)).trans ((hr.natural_apply 2).trans (headerRange_return_product _ _ _ _ _ _ had))
  have hrows : (trace.state (mid + (2 * 5 + 3))).natural 85 = s.natural 100 * s.natural 2 := by
    exact (hdout 85 (by decide)).trans ((hn 85 (by decide)).trans (by rw [hv]; rfl))
  have hmode : (trace.state (mid + (2 * 5 + 3))).natural 109 = s.natural 2 := by
    exact (hdout 109 (by decide)).trans ((hn 109 (by decide)).trans (by rw [hv]; rfl))
  have htime : mid + (2 * 5 + 3) = offset + (headerRangeTime values (s.natural 84 + 1) (s.natural 0) + 21) := by
    dsimp [mid]; omega
  rw [htime] at hdl hds hp2 hvalue hrows hmode hdcost
  exact ⟨hdl, hds, ttChildPreserves_trans hp0 (ttChildPreserves_trans hp1 hp2), hvalue, hrows, hmode,
    by dsimp [mid,s] at hcost hdcost; omega⟩

/-- Actual rank-header read, Single bank and tag6 dispatch. -/
theorem ttChild_rank_call_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset value : ℕ)
    (hl : (trace.state offset).label = 222) (hs : (trace.state offset).status = .running)
    (hm : (trace.state offset).memory ((trace.state offset).natural 0 + (trace.state offset).natural 84) = (value : ℝ)) :
    let time := offset + (3 * value + 28)
    (trace.state time).label = 230 ∧ (trace.state time).status = .running ∧
      TTChildPreserves (trace.state offset) (trace.state time) ∧
      (trace.state time).natural 2 = value ∧
      (trace.state time).natural 87 = (trace.state offset).natural 2 ∧
      (trace.state time).natural 85 = (trace.state offset).natural 85 ∧
      (trace.state time).natural 109 = (trace.state offset).natural 109 ∧
      CostThrough ttProgram trace time ≤ CostThrough ttProgram trace offset + (3 * value + 28) := by
  let s := trace.state offset
  obtain ⟨hv, hc⟩ := ttScalar_finish_at ht offset 8 (ttChildRankEntry s) (ttChild_rank_steps s hl hs) hs
  have he : ttHeaderEmbedding.Relates
      (headerProductDecodeState s.memory (s.natural 0) (s.natural 0) 1 value (s.real 1))
      (trace.state (offset + 8)) := by rw [hv]; exact ttChildRank_relates s value hm hs
  obtain ⟨hr, hn, hcost⟩ := ttHeaderSingle_full_at ht (offset + 8) s.memory (s.natural 0) value (s.real 1) he
  let mid := offset + 8 + (3 * value + 5)
  have htag : (trace.state mid).natural 97 = 6 := by rw [hn 97 (by decide), hv]; rfl
  obtain ⟨hdl, hds, hdp, hdout, hdcost⟩ := ttHeaderDispatch_call_at ht mid 6 hr.label hr.status htag
  change (trace.state (mid + 15)).label = 230 at hdl
  change (trace.state (mid + 15)).status = .running at hds
  change TTInitPreserves (trace.state mid) (trace.state (mid + 15)) at hdp
  change ∀ j : Fin 128, j ≠ 123 → (trace.state (mid + 15)).natural j = (trace.state mid).natural j at hdout
  change CostThrough ttProgram trace (mid + 15) ≤ CostThrough ttProgram trace mid + 15 at hdcost
  have hp0 : TTChildPreserves s (trace.state (offset + 8)) := by rw [hv]; exact ttChild_rank_preserves s
  have hp1 : TTChildPreserves (trace.state (offset + 8)) (trace.state mid) :=
    ttChild_header_preserves (hr.memory.trans he.memory.symm)
      ((hr.natural_apply 0).trans (he.natural_apply 0).symm) hn
  have hp2 : TTChildPreserves (trace.state mid) (trace.state (mid + (2 * 6 + 3))) :=
    ⟨hdp.1, fun j hj => hdout j hj.2.2.2.2.2.2.2.2.2.2⟩
  have hvalue : (trace.state (mid + (2 * 6 + 3))).natural 2 = value :=
    (hdout 2 (by decide)).trans (hr.natural_apply 2)
  have hcols : (trace.state (mid + (2 * 6 + 3))).natural 87 = s.natural 2 := by
    exact (hdout 87 (by decide)).trans ((hn 87 (by decide)).trans (by rw [hv]; rfl))
  have hrows : (trace.state (mid + (2 * 6 + 3))).natural 85 = s.natural 85 := by
    exact (hdout 85 (by decide)).trans ((hn 85 (by decide)).trans (by rw [hv]; rfl))
  have hmode : (trace.state (mid + (2 * 6 + 3))).natural 109 = s.natural 109 := by
    exact (hdout 109 (by decide)).trans ((hn 109 (by decide)).trans (by rw [hv]; rfl))
  have htime : mid + (2 * 6 + 3) = offset + (3 * value + 28) := by dsimp [mid]; omega
  rw [htime] at hdl hds hp2 hvalue hcols hrows hmode hdcost
  exact ⟨hdl, hds, ttChildPreserves_trans hp0 (ttChildPreserves_trans hp1 hp2), hvalue, hcols, hrows, hmode,
    by dsimp [mid,s] at hcost hdcost; omega⟩

#assert_trust kernel ttChild_mode_call_at
#assert_trust kernel ttChild_suffix_call_at
#assert_trust kernel ttChild_rank_call_at
#print axioms ttChild_rank_call_at
end NLA.Proofs.TR04
