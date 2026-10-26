import NLA.Proofs.TR04.MachineTTFirstSelectionRun
import NLA.Proofs.TR04.MachineSVDMemory
import NLA.Proofs.TR04.TTStrictExplicitFrames

/-! The fixed first-selection phase computes a deterministic family from every
actual legal full-SVD response. No later child response or comparator is input
to this selection. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

structure TTFirstChoice where
  above : ℕ
  tied : ℕ
  take : ℕ
  count : ℕ

def ttFirstPrefixChoice (cap : ℕ) : TTFirstChoice := ⟨cap, 1, 0, 1⟩

def ttFirstChoice {p : ℕ} (sigma : Fin p → ℝ) (hord : Antitone sigma)
    (r cap : ℕ) (hr : 1 ≤ r) : TTFirstChoice :=
  if hp : r ≤ p then
    let a : Fin p := ⟨r - 1, by omega⟩
    if 0 < sigma a then
      let T := SVD.countedTieStructure sigma hord a
      ⟨T.above, T.tied, T.take, T.tied⟩
    else ttFirstPrefixChoice cap
  else ttFirstPrefixChoice cap

def TTFirstSelected (C : TTFirstChoice) (s : State ttProgram) : Prop :=
  s.natural 77 = C.above ∧ s.natural 78 = C.tied ∧
    s.natural 79 = C.take ∧ s.natural 75 = C.count

theorem ttFirstChoice_count_pos {p : ℕ} (sigma : Fin p → ℝ) (hord : Antitone sigma)
    (r cap : ℕ) (hr : 1 ≤ r) : 0 < (ttFirstChoice sigma hord r cap hr).count := by
  unfold ttFirstChoice
  split
  · dsimp only
    split
    · exact (SVD.countedTieStructure sigma hord _).tied_pos
    · exact Nat.zero_lt_one
  · exact Nat.zero_lt_one

theorem ttFirstChoice_width {p : ℕ} (sigma : Fin p → ℝ) (hord : Antitone sigma)
    (r : ℕ) (hr : 1 ≤ r) :
    (ttFirstChoice sigma hord r (min r p) hr).above +
      (ttFirstChoice sigma hord r (min r p) hr).take = min r p := by
  unfold ttFirstChoice
  split
  · next hp =>
      dsimp only
      split
      · have hx := (SVD.countedTieStructure sigma hord (⟨r - 1, by omega⟩ : Fin p)).rank_eq
        change _ + _ = min r p
        rw [hx, Nat.min_eq_left hp]
        change r - 1 + 1 = r
        omega
      · rfl
  · rfl

/-- Actual first-selection execution after the SVD return. Arbitrary source
arrays are allowed here; antitonicity identifies the exact complete tie block. -/
theorem ttFirstSelection_run {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 168) (hs : s.status = .running)
    {p : ℕ} (sigma : Fin p → ℝ) (hord : Antitone sigma) (r cap : ℕ) (hr : 1 ≤ r)
    (hp : s.natural 105 = p) (hrank : s.natural 80 = r) (hcap : s.natural 106 = cap)
    (hzero : s.natural 127 = 0)
    (hmem : ∀ k : Fin p, s.memory (s.natural 73 + k.val) = sigma k) :
    ∃ n : ℕ, n ≤ 9 * p + 23 ∧
      (trace.state (offset + n)).label = 189 ∧ (trace.state (offset + n)).status = .running ∧
      TTFirstSelected (ttFirstChoice sigma hord r cap hr) (trace.state (offset + n)) ∧
      TTFirstPreserves s (trace.state (offset + n)) ∧
      CostThrough ttProgram trace (offset + n) ≤ CostThrough ttProgram trace offset + (9 * p + 23) := by
  classical
  by_cases hrp : r ≤ p
  · let a : Fin p := ⟨r - 1, by omega⟩
    let T := SVD.countedTieStructure sigma hord a
    have hm : s.memory (s.natural 73 + (s.natural 80 - 1)) = sigma a := by
      simpa only [hrank] using hmem a
    have hnot : ¬s.natural 105 < s.natural 80 := by rw [hp, hrank]; omega
    by_cases htau : 0 < sigma a
    · have htest : (s.natural 127 : ℝ) < s.memory (s.natural 73 + (s.natural 80 - 1)) := by
        rw [hzero, Nat.cast_zero, hm]
        exact htau
      obtain ⟨hlabel, hstatus, hh, hT, hS, hK, hpres, hcost⟩ :=
        ttFirstSelection_positive_run ht offset s he hl hs hnot htest
      have hcounts := thresholdCounts_countedTieStructure sigma hord a s.memory (s.natural 73) hmem
      have ha : a.val + 1 = r := by dsimp [a]; omega
      dsimp only at hcounts
      simp only [ha] at hcounts
      simp only [hp, hrank] at hh hT hS hK hcost hlabel hstatus hpres
      have hm' : s.memory (s.natural 73 + (r - 1)) = sigma a := by simpa only [hrank] using hm
      rw [hm'] at hh hT hS hK
      refine ⟨9 * p + 23, le_rfl, hlabel, hstatus, ?_, hpres, hcost⟩
      have hchoice : ttFirstChoice sigma hord r cap hr = ⟨T.above, T.tied, T.take, T.tied⟩ := by
        unfold ttFirstChoice
        rw [dif_pos hrp]
        change (if 0 < sigma a then (⟨T.above, T.tied, T.take, T.tied⟩ : TTFirstChoice)
          else ttFirstPrefixChoice cap) = _
        exact if_pos htau
      rw [hchoice]
      exact ⟨hh.trans hcounts.1, hT.trans hcounts.2.1, hS.trans hcounts.2.2, hK.trans hcounts.2.1⟩
    · have htest : ¬(s.natural 127 : ℝ) < s.memory (s.natural 73 + (s.natural 80 - 1)) := by
        rw [hzero, Nat.cast_zero, hm]
        exact htau
      obtain ⟨hx, hpres, hcost⟩ := ttFirstSelection_nonpositive_run ht offset s he hl hs hnot htest
      refine ⟨12, by omega, ?_, ?_, ?_, hpres, by omega⟩
      · rw [hx]; rfl
      · rw [hx]; exact hs
      · have hchoice : ttFirstChoice sigma hord r cap hr = ttFirstPrefixChoice cap := by
          unfold ttFirstChoice
          rw [dif_pos hrp]
          change (if 0 < sigma a then _ else ttFirstPrefixChoice cap) = _
          exact if_neg htau
        rw [hchoice, hx]
        exact ⟨hcap, rfl, rfl, rfl⟩
  · have hlarge : s.natural 105 < s.natural 80 := by rw [hp, hrank]; omega
    obtain ⟨hx, hpres, hcost⟩ := ttFirstSelection_large_run ht offset s he hl hs hlarge
    refine ⟨6, by omega, ?_, ?_, ?_, hpres, by omega⟩
    · rw [hx]; rfl
    · rw [hx]; exact hs
    · have hchoice : ttFirstChoice sigma hord r cap hr = ttFirstPrefixChoice cap := by
        simp only [ttFirstChoice, dif_neg hrp]
      rw [hchoice, hx]
      exact ⟨hcap, rfl, rfl, rfl⟩

#assert_trust kernel ttFirstChoice_count_pos
#assert_trust kernel ttFirstChoice_width
#assert_trust kernel ttFirstSelection_run
#print axioms ttFirstSelection_run
end NLA.Proofs.TR04
