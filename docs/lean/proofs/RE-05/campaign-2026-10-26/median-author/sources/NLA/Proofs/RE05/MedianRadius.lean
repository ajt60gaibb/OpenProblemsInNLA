import NLA.Proofs.RE05.OrthogonalOptimum

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery

/-- An order statistic is bounded by any value attained by enough entries. -/
theorem sorted_get_le_of_count (l : List ℝ) (hs : l.Pairwise (· ≤ ·))
    (k : ℕ) (hk : k < l.length) (b : ℝ)
    (hc : k + 1 ≤ l.countP (fun x => decide (x ≤ b))) : l[k] ≤ b := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    rcases List.pairwise_cons.mp hs with ⟨ha, hl⟩
    cases k with
    | zero =>
      rcases List.countP_pos_iff.mp (show 0 < (a :: l).countP
          (fun x => decide (x ≤ b)) by omega) with ⟨x, hx, hb⟩
      have hxb : x ≤ b := by simpa using hb
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hxb
      · exact (ha x hx).trans hxb
    | succ k =>
      have hcount : k + 1 ≤ l.countP (fun x => decide (x ≤ b)) := by
        simp only [List.countP_cons] at hc
        split_ifs at hc <;> omega
      exact ih hl k (by simpa using hk) hcount

/-- At least the first `k+1` entries lie below the `k`th sorted entry. -/
theorem sorted_count_le_get (l : List ℝ) (hs : l.Pairwise (· ≤ ·))
    (k : ℕ) (hk : k < l.length) :
    k + 1 ≤ l.countP (fun x => decide (x ≤ l[k])) := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    rcases List.pairwise_cons.mp hs with ⟨ha, hl⟩
    cases k with
    | zero => simp
    | succ k =>
      have hk' : k < l.length := by simpa using hk
      have htail := ih hl k hk'
      have hab : a ≤ l[k] := ha _ (List.getElem_mem hk')
      simpa [List.countP_cons, hab] using Nat.add_le_add_right htail 1

/-- The literal eighth sorted score is bounded by eight nearby copies. -/
theorem medianRadius_le_of_eight {n q : ℕ} (P : Basis n q)
    (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ))
    (copy : Fin 15) (b : ℝ)
    (h : 8 ≤ (Finset.univ.filter fun other : Fin 15 =>
      coefficientDistance P (copyOutput P schedule responses copy)
        (copyOutput P schedule responses other) ≤ b).card) :
    medianRadius P schedule responses copy ≤ b := by
  classical
  let l := (List.finRange 15).map fun other =>
    coefficientDistance P (copyOutput P schedule responses copy)
      (copyOutput P schedule responses other)
  have hcard := (List.nodup_finRange 15).card_eq_countP
    (P := fun other => coefficientDistance P (copyOutput P schedule responses copy)
      (copyOutput P schedule responses other) ≤ b)
  have hcount : 8 ≤ l.countP (fun x => decide (x ≤ b)) := by
    simpa only [List.toFinset_finRange, List.countP_map, Function.comp_def, l]
      using hcard ▸ h
  have hk : 7 < (l.mergeSort (· ≤ ·)).length := by simp [l]
  have hs := sorted_get_le_of_count (l.mergeSort (· ≤ ·))
    (List.pairwise_mergeSort' (· ≤ ·) l) 7 hk b
  have hc : 8 ≤ (l.mergeSort (· ≤ ·)).countP (fun x => decide (x ≤ b)) := by
    rw [(List.mergeSort_perm l _).countP_eq]
    exact hcount
  simpa only [medianRadius, l, List.getElem?_eq_getElem hk, Option.getD_some]
    using hs hc

/-- The literal median ball always contains at least eight of the fifteen copies. -/
theorem medianRadius_eight {n q : ℕ} (P : Basis n q)
    (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ))
    (copy : Fin 15) :
    8 ≤ (Finset.univ.filter fun other : Fin 15 =>
      coefficientDistance P (copyOutput P schedule responses copy)
        (copyOutput P schedule responses other) ≤
          medianRadius P schedule responses copy).card := by
  classical
  let l := (List.finRange 15).map fun other =>
    coefficientDistance P (copyOutput P schedule responses copy)
      (copyOutput P schedule responses other)
  have hk : 7 < (l.mergeSort (· ≤ ·)).length := by simp [l]
  have hs := sorted_count_le_get (l.mergeSort (· ≤ ·))
    (List.pairwise_mergeSort' (· ≤ ·) l) 7 hk
  have hm : medianRadius P schedule responses copy = (l.mergeSort (· ≤ ·))[7] := by
    simp only [medianRadius, l, List.getElem?_eq_getElem hk, Option.getD_some]
  rw [(List.mergeSort_perm l _).countP_eq] at hs
  have hcard := (List.nodup_finRange 15).card_eq_countP
    (P := fun other => coefficientDistance P (copyOutput P schedule responses copy)
      (copyOutput P schedule responses other) ≤ medianRadius P schedule responses copy)
  rw [List.toFinset_finRange] at hcard
  rw [hcard, hm]
  simpa only [l, List.countP_map, Function.comp_def] using hs

/-- The exact first-index-tie-breaking scan minimizes every supplied score. -/
theorem foldl_score_minimum {α : Type*} (score : α → ℝ) (l : List α) (best : α) :
    score (l.foldl (fun b x => if score x < score b then x else b) best) ≤ score best ∧
    ∀ x ∈ l, score (l.foldl (fun b x => if score x < score b then x else b) best) ≤
      score x := by
  induction l generalizing best with
  | nil => simp
  | cons a l ih =>
    let next := if score a < score best then a else best
    have hn : score next ≤ score best ∧ score next ≤ score a := by
      dsimp [next]
      split_ifs with h
      · exact ⟨h.le, le_rfl⟩
      · exact ⟨le_rfl, le_of_not_gt h⟩
    rcases ih next with ⟨hb, hl⟩
    refine ⟨hb.trans hn.1, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hb.trans hn.2
    · exact hl x hx

theorem chooseCopy_le {n q : ℕ} (P : Basis n q)
    (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ)) (copy : Fin 15) :
    medianRadius P schedule responses (chooseCopy P schedule responses) ≤
      medianRadius P schedule responses copy := by
  exact (foldl_score_minimum (medianRadius P schedule responses)
    (List.finRange 15) 0).2 copy (List.mem_finRange copy)

#assert_trust kernel sorted_get_le_of_count
#assert_trust kernel sorted_count_le_get
#assert_trust kernel medianRadius_le_of_eight
#assert_trust kernel medianRadius_eight
#assert_trust kernel foldl_score_minimum
#assert_trust kernel chooseCopy_le
#print axioms sorted_get_le_of_count
#print axioms sorted_count_le_get
#print axioms medianRadius_le_of_eight
#print axioms medianRadius_eight
#print axioms foldl_score_minimum
#print axioms chooseCopy_le
end NLA.Proofs.RE05
