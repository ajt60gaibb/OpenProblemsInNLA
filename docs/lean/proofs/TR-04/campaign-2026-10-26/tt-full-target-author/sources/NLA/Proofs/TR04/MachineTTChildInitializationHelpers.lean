import NLA.Proofs.TR04.MachineTTChildInitializationScalar

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def TTChildKept (j : Fin 128) : Prop :=
  j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3 ∧ j ≠ 85 ∧ j ≠ 86 ∧ j ≠ 87 ∧
    j ≠ 94 ∧ j ≠ 97 ∧ j ≠ 109 ∧ j ≠ 122 ∧ j ≠ 123

def TTChildPreserves (s t : State ttProgram) : Prop :=
  t.memory = s.memory ∧ ∀ j : Fin 128, TTChildKept j → t.natural j = s.natural j

theorem ttChildPreserves_trans {s t u : State ttProgram}
    (h : TTChildPreserves s t) (k : TTChildPreserves t u) : TTChildPreserves s u :=
  ⟨k.1.trans h.1, fun j hj => (k.2 j hj).trans (h.2 j hj)⟩

theorem ttChild_mode_preserves (s : State ttProgram) : TTChildPreserves s (ttChildModeEntry s) := by
  refine ⟨rfl, ?_⟩
  intro j hj
  rcases hj with ⟨h1,h2,h3,h85,h86,h87,h94,h97,h109,h122,h123⟩
  simp only [ttChildModeEntry, Function.update_of_ne h97, Function.update_of_ne h3,
    Function.update_of_ne h2, Function.update_of_ne h1]

theorem ttChild_suffix_preserves (s : State ttProgram) : TTChildPreserves s (ttChildSuffixEntry s) := by
  refine ⟨rfl, ?_⟩
  intro j hj
  rcases hj with ⟨h1,h2,h3,h85,h86,h87,h94,h97,h109,h122,h123⟩
  simp only [ttChildSuffixEntry, Function.update_of_ne h97, Function.update_of_ne h3,
    Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h85, Function.update_of_ne h109]

theorem ttChild_rank_preserves (s : State ttProgram) : TTChildPreserves s (ttChildRankEntry s) := by
  refine ⟨rfl, ?_⟩
  intro j hj
  rcases hj with ⟨h1,h2,h3,h85,h86,h87,h94,h97,h109,h122,h123⟩
  simp only [ttChildRankEntry, Function.update_of_ne h97, Function.update_of_ne h3,
    Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h122, Function.update_of_ne h87]

theorem ttChild_cap_preserves (s : State ttProgram) : TTChildPreserves s (ttChildCapEnd s) := by
  refine ⟨rfl, ?_⟩
  intro j hj
  rcases hj with ⟨h1,h2,h3,h85,h86,h87,h94,h97,h109,h122,h123⟩
  simp only [ttChildCapEnd, ttChildCapRowsEnd, ttChildCapColsEnd,
    Function.update_of_ne h94, Function.update_of_ne h86]

theorem ttChild_dispatch_preserves (s : State ttProgram) (k : Fin 11) :
    TTChildPreserves s (ttHeaderDispatchEnd s k) := by
  refine ⟨rfl, ?_⟩
  intro j hj
  exact Function.update_of_ne hj.2.2.2.2.2.2.2.2.2.2 _ _

theorem ttChild_header_preserves {s t : State ttProgram}
    (hm : t.memory = s.memory) (hd : t.natural 0 = s.natural 0)
    (hn : ∀ j : Fin 128, 4 ≤ j.val → t.natural j = s.natural j) : TTChildPreserves s t := by
  refine ⟨hm, ?_⟩
  intro j hj
  by_cases h : 4 ≤ j.val
  · exact hn j h
  · have he : j = 0 := by
      have h1 : j.val ≠ 1 := fun hh => hj.1 (Fin.ext hh)
      have h2 : j.val ≠ 2 := fun hh => hj.2.1 (Fin.ext hh)
      have h3 : j.val ≠ 3 := fun hh => hj.2.2.1 (Fin.ext hh)
      apply Fin.ext
      change j.val = 0
      omega
    simpa only [he] using hd

theorem ttChildMode_relates (s : State ttProgram) (value : ℕ)
    (hm : s.memory (s.natural 84) = (value : ℝ)) (hs : s.status = .running) :
    ttHeaderEmbedding.Relates
      (headerProductDecodeState s.memory (s.natural 0) (s.natural 0) 1 value (s.real 1)) (ttChildModeEntry s) := by
  constructor
  · rfl
  · funext i
    fin_cases i
    · exact hm
    · rfl
  · funext i; fin_cases i <;> rfl
  · rfl
  · exact hs

theorem ttChildSuffix_relates (s : State ttProgram) (values : ℕ → ℕ) (hs : s.status = .running) :
    ttHeaderEmbedding.Relates
      (headerRangeEntryState s.memory (s.natural 0) (s.natural 84 + 1) values 0
        (fun i => s.real (ttHeaderEmbedding.reals i))) (ttChildSuffixEntry s) := by
  rw [headerRange_entry_eq]
  constructor
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl
  · exact hs

theorem ttChildRank_relates (s : State ttProgram) (value : ℕ)
    (hm : s.memory (s.natural 0 + s.natural 84) = (value : ℝ)) (hs : s.status = .running) :
    ttHeaderEmbedding.Relates
      (headerProductDecodeState s.memory (s.natural 0) (s.natural 0) 1 value (s.real 1)) (ttChildRankEntry s) := by
  constructor
  · rfl
  · funext i
    fin_cases i
    · exact hm
    · rfl
  · funext i; fin_cases i <;> rfl
  · rfl
  · exact hs

theorem ttChild_cap_fields (s : State ttProgram) :
    (ttChildCapEnd s).label = 237 ∧
      (ttChildCapEnd s).natural 86 = min (s.natural 2) (min (s.natural 85) (s.natural 87)) ∧
      (ttChildCapEnd s).natural 94 = s.natural 67 + s.natural 84 * s.natural 66 ∧
      (ttChildCapEnd s).natural 85 = s.natural 85 ∧ (ttChildCapEnd s).natural 87 = s.natural 87 ∧
      (ttChildCapEnd s).natural 109 = s.natural 109 ∧ (ttChildCapEnd s).natural 2 = s.natural 2 := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  change min (min (s.natural 2) (s.natural 85)) (s.natural 87) = _
  exact Nat.min_assoc _ _ _

theorem ttChild_cap_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label = 230) (hs : (trace.state offset).status = .running) :
    ∃ n : ℕ, n ≤ 7 ∧ trace.state (offset + n) = ttChildCapEnd (trace.state offset) ∧
      TTChildPreserves (trace.state offset) (trace.state (offset + n)) ∧
      CostThrough ttProgram trace (offset + n) ≤ CostThrough ttProgram trace offset + 7 := by
  obtain ⟨n, hn, he⟩ := ttChild_cap_steps (trace.state offset) hl hs
  obtain ⟨hv, hc⟩ := ttScalar_finish_at ht offset n _ he hs
  refine ⟨n, hn, hv, ?_, by omega⟩
  rw [hv]
  exact ttChild_cap_preserves _

#assert_trust kernel ttChildPreserves_trans
#assert_trust kernel ttChild_mode_preserves
#assert_trust kernel ttChild_suffix_preserves
#assert_trust kernel ttChild_rank_preserves
#assert_trust kernel ttChild_cap_preserves
#assert_trust kernel ttChild_dispatch_preserves
#assert_trust kernel ttChild_header_preserves
#assert_trust kernel ttChildMode_relates
#assert_trust kernel ttChildSuffix_relates
#assert_trust kernel ttChildRank_relates
#assert_trust kernel ttChild_cap_fields
#assert_trust kernel ttChild_cap_at
#print axioms ttChild_cap_at
end NLA.Proofs.TR04
