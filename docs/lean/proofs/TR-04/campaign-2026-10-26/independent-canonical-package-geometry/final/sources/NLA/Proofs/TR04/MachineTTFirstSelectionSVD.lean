import NLA.Proofs.TR04.MachineTTFirstSelection

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

/-- Every legal first SVD response is retained, and the actual caller computes
its deterministic first-frame parameters before entering the candidate loop. -/
theorem ttFirstSelection_svd_run {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 167) (hs : s.status = .running)
    (hp : s.natural 105 = min (s.natural 81) (s.natural 82))
    (hr : 1 ≤ s.natural 80) (hzero : s.natural 127 = 0)
    (hd : OutputBlocksDisjoint (s.natural 81) (s.natural 82)
      (s.natural 72) (s.natural 73) (s.natural 74)) :
    ∃ U : Matrix (Fin (s.natural 81)) (Fin (s.natural 81)) ℝ,
    ∃ sigma : Fin (min (s.natural 81) (s.natural 82)) → ℝ,
    ∃ V : Matrix (Fin (s.natural 82)) (Fin (s.natural 82)) ℝ,
    ∃ n : ℕ,
      ValidSVD (readMatrix s.memory (s.natural 81) (s.natural 82) (s.natural 92)) U sigma V ∧
      n ≤ 9 * min (s.natural 81) (s.natural 82) + 24 ∧
      (trace.state (offset + n)).label = 189 ∧ (trace.state (offset + n)).status = .running ∧
      (∃ hord : Antitone sigma, TTFirstSelected
        (ttFirstChoice sigma hord (s.natural 80) (s.natural 106) hr) (trace.state (offset + n))) ∧
      (trace.state (offset + n)).memory =
        writeSVD s.memory (s.natural 72) (s.natural 73) (s.natural 74) U sigma V ∧
      (∀ j : Fin 128, TTFirstProtected j → (trace.state (offset + n)).natural j = s.natural j) ∧
      readMatrix (trace.state (offset + n)).memory (s.natural 81) (s.natural 81) (s.natural 72) = U ∧
      (∀ k, (trace.state (offset + n)).memory (s.natural 73 + k.val) = sigma k) ∧
      readMatrix (trace.state (offset + n)).memory (s.natural 82) (s.natural 82) (s.natural 74) = V ∧
      CostThrough ttProgram trace (offset + n) ≤ CostThrough ttProgram trace offset +
        (s.natural 81 + s.natural 82 + 1)^3 + (9 * min (s.natural 81) (s.natural 82) + 23) := by
  have hcode : ttProgram.code (trace.state offset).label = .svd 81 82 92 72 73 74 168 := by
    rw [he, hl]
    exact ttProgram_code_first_svd
  have hstatus : (trace.state offset).status = .running := he ▸ hs
  have hdisj : OutputBlocksDisjoint ((trace.state offset).natural 81) ((trace.state offset).natural 82)
      ((trace.state offset).natural 72) ((trace.state offset).natural 73) ((trace.state offset).natural 74) := by
    simpa only [he] using hd
  have hreply := trace_svd_at ht offset 81 82 92 72 73 74 168 hcode hstatus hdisj
  rw [he] at hreply
  obtain ⟨U, sigma, V, hvalid, hnext, hcharge⟩ := hreply
  let saved := writeSVD s.memory (s.natural 72) (s.natural 73) (s.natural 74) U sigma V
  let next : State ttProgram := {s with label := 168, memory := saved}
  have hm (k : Fin (min (s.natural 81) (s.natural 82))) :
      next.memory (next.natural 73 + k.val) = sigma k :=
    writeSVD_sigma_entry s.memory _ _ _ U sigma V hd k
  have hnext' : trace.state (offset + 1) = next := hnext
  obtain ⟨n, hn, hlabel, hrun, hselect, hpres, hcost⟩ := ttFirstSelection_run ht (offset + 1)
    next hnext' rfl hs sigma hvalid.2.2.2.1 (s.natural 80) (s.natural 106) hr hp rfl rfl hzero hm
  have htime : offset + 1 + n = offset + (n + 1) := by omega
  rw [htime] at hlabel hrun hselect hpres hcost
  have hcost1 : CostThrough ttProgram trace (offset + 1) =
      CostThrough ttProgram trace offset + (s.natural 81 + s.natural 82 + 1)^3 := by
    simp only [CostThrough, Finset.sum_range_succ, hcharge]
  refine ⟨U, sigma, V, n + 1, hvalid, by omega, hlabel, hrun,
    ⟨hvalid.2.2.2.1, hselect⟩, hpres.1, ?_, ?_, ?_, ?_, ?_⟩
  · exact hpres.2
  · rw [hpres.1]
    exact readMatrix_writeSVD_u s.memory _ _ _ U sigma V
  · intro k
    rw [hpres.1]
    exact writeSVD_sigma_entry s.memory _ _ _ U sigma V hd k
  · rw [hpres.1]
    exact readMatrix_writeSVD_v s.memory _ _ _ U sigma V hd
  · rw [hcost1] at hcost
    exact hcost

#assert_trust kernel ttFirstSelection_svd_run
#print axioms ttFirstSelection_svd_run
end NLA.Proofs.TR04
