import NLA.TR07.DeletionDefect
import NLA.TR07.ProbabilityTransfer

/-! The deficiency vanishes whenever the selected matrix has the stated
smallest-singular-value lower bound, independently of the ordering of its columns. -/
noncomputable section
namespace NLA.TR07

theorem defect_ordered_eq_zero {k n r : ℕ} (M : Mat k n) (I : Fin r ↪ Fin n)
    {η : ℝ} (h : η < smallestSingular M (orderedRange I)) :
    defect (fun j : Fin r => WithLp.toLp 2 (fun i => M i (I j))) η = 0 := by
  classical
  let e : Fin r ≃ orderedRange I := rangeFiberEquiv (orderedRangeSample I) ⟨I, rfl⟩
  have hg := (good_selected_of_tail M (orderedRange I) h).reindex e
  apply defect_eq_zero_of_good
  convert hg using 1
  · ext j i
    rfl
  · ext j
    simp

theorem subsetTail_nonneg {k n : ℕ} (M : Mat k n) (r : ℕ) (η : ℝ) :
    0 ≤ subsetTail M r η := by unfold subsetTail; positivity

theorem subsetTail_le_of_defect_mean {k n r : ℕ} (M : Mat k n) (η : ℝ)
    (hn : 0 < n) (hr : 0 < r) (hrn : r ≤ n) {ρ : ℝ} (hρ : 0 < ρ)
    (hmean : ρ * r ≤ ((@Law.uniform (Fin n) _ ⟨⟨0, hn⟩⟩).iid r).expect
      (fun x => (defect (fun j => WithLp.toLp 2 (fun i => M i (x j))) η : ℝ))) :
    subsetTail M r η ≤ 4 / (ρ^2 * r) + (r-1) / (ρ*n) := by
  apply subset_prob_le_of_iid_expect hn hr hrn _ _ ?_ ?_ hρ hmean
  · intro x j a
    have h := defect_update (fun j => WithLp.toLp 2 (fun i => M i (x j))) η j
      (WithLp.toLp 2 (fun i => M i a))
    have he : (fun t => WithLp.toLp 2 (fun i => M i (Function.update x j a t))) =
        @Function.update (Fin r) (fun _ => Vec k) (fun _ _ => Classical.propDecidable _)
          (fun t => WithLp.toLp 2 (fun i => M i (x t))) j
          (WithLp.toLp 2 (fun i => M i a)) := by
      ext t i
      by_cases ht : t = j <;> simp [ht]
    simpa only [he] using h
  · intro I hI
    simp only [defect_ordered_eq_zero M I hI, Nat.cast_zero]

end NLA.TR07
