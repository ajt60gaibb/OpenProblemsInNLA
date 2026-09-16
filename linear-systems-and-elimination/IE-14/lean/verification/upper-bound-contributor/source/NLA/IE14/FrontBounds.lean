/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.IE14.Front

noncomputable section
namespace NLA.IE14

def frontMax {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (path : PivotPath n)
    (k : ℕ) (j : Fin n) : ℝ :=
  max ‖trajectory A path k (frontPair hn path k).1 j‖
    ‖trajectory A path k (frontPair hn path k).2 j‖

def frontSum {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (path : PivotPath n)
    (k : ℕ) (j : Fin n) : ℝ :=
  ‖trajectory A path k (frontPair hn path k).1 j‖ +
    ‖trajectory A path k (frontPair hn path k).2 j‖

theorem frontMax_nonneg {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (path : PivotPath n)
    (k : ℕ) (j : Fin n) : 0 ≤ frontMax hn A path k j :=
  le_trans (norm_nonneg _) (le_max_left _ _)

theorem frontSum_nonneg {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (path : PivotPath n)
    (k : ℕ) (j : Fin n) : 0 ≤ frontSum hn A path k j :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem frontMax_le_sum {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (path : PivotPath n)
    (k : ℕ) (j : Fin n) : frontMax hn A path k j ≤ frontSum hn A path k j := by
  exact max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left (norm_nonneg _))

theorem active_entry_le_front {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) (k : ℕ) (hk : k ≤ n-2)
    (i j : Fin n) (hi : k ≤ i.val) (hj : k ≤ j.val) :
    ‖trajectory A path k i j‖ ≤ max (frontMax hn A path k j) (entryMax A) := by
  have hF := frontInvariant_all hn A hA path hp k hk
  by_cases hl : i=(frontPair hn path k).1
  · subst i
    exact (le_max_left _ _).trans (le_max_left _ _)
  by_cases hr : i=(frontPair hn path k).2
  · subst i
    exact (le_max_right _ _).trans (le_max_left _ _)
  have hc := hF.cover i hi hl hr
  have hv := hF.future_value (origin path k i) hc.1 hc.2 j hj
  simp only [Equiv.symm_apply_apply] at hv
  rw [hv]
  exact (norm_le_entryMax A _ _).trans (le_max_right _ _)

/-- Three possible removed rows, with no restriction on which target value is largest. -/
theorem three_removal_bounds (a b c x y : ℝ)
    (h : (x ≤ b+a ∧ y ≤ c+a) ∨ (x ≤ a+b ∧ y ≤ c+b) ∨
      (x ≤ a+c ∧ y ≤ b+c)) :
    max x y ≤ max (a+b) (max a b+c) ∧
      x+y ≤ a+b+c+max (max a b) c := by
  have ha := le_max_left a b
  have hb := le_max_right a b
  have ht := le_max_left (a+b) (max a b+c)
  have hm := le_max_right (a+b) (max a b+c)
  have hz := le_max_left (max a b) c
  have hc := le_max_right (max a b) c
  rcases h with h | h | h
  all_goals
    constructor
    · apply max_le <;> linarith [h.1,h.2]
    · linarith [h.1,h.2]

theorem trajectory_survivor_norm {n : ℕ} (A : Mat n) (path : PivotPath n)
    (hp : AdmissiblePath A path) (k : ℕ) (hk : k<n) (q j : Fin n)
    (hq : k ≤ q.val) (hne : q ≠ path ⟨k,hk⟩) (hj : k<j.val) :
    ‖trajectory A path (k+1) (Equiv.swap ⟨k,hk⟩ (path ⟨k,hk⟩) q) j‖ ≤
      ‖trajectory A path k q j‖ + ‖trajectory A path k (path ⟨k,hk⟩) j‖ := by
  let z : Fin n := ⟨k,hk⟩
  rw [trajectory_survivor_entry A path k hk q j (hp z).1 hq hne hj]
  calc
    _ ≤ ‖trajectory A path k q j‖ +
        ‖(trajectory A path k q z / trajectory A path k (path z) z) *
          trajectory A path k (path z) j‖ := norm_sub_le _ _
    _ = ‖trajectory A path k q j‖ +
        ‖trajectory A path k q z / trajectory A path k (path z) z‖ *
          ‖trajectory A path k (path z) j‖ := by rw [norm_mul]
    _ ≤ _ := by
      apply add_le_add le_rfl
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (multiplier_bound _ z (path z) (hp z) q hq) (norm_nonneg (trajectory A path k (path z) j))

theorem front_step_bounds {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) (k : ℕ) (hk : k+2<n)
    (j : Fin n) (hj : k<j.val) (c : ℝ) (hc : ‖A ⟨k+1,by omega⟩ j‖ ≤ c) :
    frontMax hn A path (k+1) j ≤
      max (frontSum hn A path k j) (frontMax hn A path k j+c) ∧
    frontSum hn A path (k+1) j ≤ frontSum hn A path k j+c+
      max (frontMax hn A path k j) c := by
  let z : Fin n := ⟨k,by omega⟩
  let p := path z
  let r := (frontPair hn path k).1
  let s := (frontPair hn path k).2
  let f := (origin path k).symm (⟨k+1,by omega⟩ : Fin n)
  let τ := Equiv.swap z p
  let rem := remainingPair r s f p
  have hF := frontInvariant_all hn A hA path hp k (by omega)
  change FrontInvariant A path k r s at hF
  have hf := front_fresh_distinct hF hk
  change k ≤ f.val ∧ r ≠ f ∧ s ≠ f at hf
  have hpf := pivot_in_front hA hp hF hk
  change p=r ∨ p=s ∨ p=f at hpf
  have hpair : frontPair hn path (k+1)=(τ rem.1,τ rem.2) := by
    simp only [frontPair, dif_pos hk]; rfl
  have hfj : trajectory A path k f j=A ⟨k+1,by omega⟩ j :=
    hF.future_value _ (by simp) (by simp; omega) j (by omega)
  have hfc : ‖trajectory A path k f j‖ ≤ c := by simpa only [hfj] using hc
  have hnorm : ∀ q : Fin n, k ≤ q.val → q ≠ p →
      ‖trajectory A path (k+1) (τ q) j‖ ≤
        ‖trajectory A path k q j‖ + ‖trajectory A path k p j‖ := by
    intro q hq hne
    exact trajectory_survivor_norm A path hp k z.isLt q j hq hne hj
  have hcases :
      (‖trajectory A path (k+1) (τ rem.1) j‖ ≤
          ‖trajectory A path k s j‖+‖trajectory A path k r j‖ ∧
        ‖trajectory A path (k+1) (τ rem.2) j‖ ≤ c+‖trajectory A path k r j‖) ∨
      (‖trajectory A path (k+1) (τ rem.1) j‖ ≤
          ‖trajectory A path k r j‖+‖trajectory A path k s j‖ ∧
        ‖trajectory A path (k+1) (τ rem.2) j‖ ≤ c+‖trajectory A path k s j‖) ∨
      (‖trajectory A path (k+1) (τ rem.1) j‖ ≤ ‖trajectory A path k r j‖+c ∧
        ‖trajectory A path (k+1) (τ rem.2) j‖ ≤ ‖trajectory A path k s j‖+c) := by
    rcases hpf with hpr | hps | hpf
    · left
      have hs := hnorm s hF.right_active (by simpa only [hpr] using Ne.symm hF.distinct)
      have hf' := hnorm f hf.1 (by simpa only [hpr] using Ne.symm hf.2.1)
      simp only [hpr] at hs hf'
      simp only [rem, remainingPair, hpr, ite_true]
      exact ⟨hs, by linarith⟩
    · right; left
      have hr := hnorm r hF.left_active (by simpa only [hps] using hF.distinct)
      have hf' := hnorm f hf.1 (by simpa only [hps] using Ne.symm hf.2.2)
      simp only [hps] at hr hf'
      simp only [rem, remainingPair, hps, if_neg (Ne.symm hF.distinct), ite_true]
      exact ⟨hr, by linarith⟩
    · right; right
      have hr := hnorm r hF.left_active (by simpa only [hpf] using hf.2.1)
      have hs := hnorm s hF.right_active (by simpa only [hpf] using hf.2.2)
      simp only [hpf] at hr hs
      simp only [rem, remainingPair, hpf, if_neg (Ne.symm hf.2.1), if_neg (Ne.symm hf.2.2)]
      exact ⟨by linarith, by linarith⟩
  have h := three_removal_bounds _ _ _ _ _ hcases
  simpa only [frontMax, frontSum, hpair, r, s] using h

theorem front_zero_step {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) (k : ℕ) (hk : k+2<n)
    (j : Fin n) (hj : k<j.val) (hz : A ⟨k+1,by omega⟩ j=0) :
    frontMax hn A path (k+1) j ≤ frontSum hn A path k j ∧
    frontSum hn A path (k+1) j ≤ frontSum hn A path k j+frontMax hn A path k j := by
  have h := front_step_bounds hn A hA path hp k hk j hj 0 (by simp [hz])
  simpa only [add_zero, max_eq_left (frontMax_le_sum hn A path k j),
    max_eq_left (frontMax_nonneg hn A path k j)] using h

theorem final_scalar_le_frontSum {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) :
    ‖trajectory A path (n-1) ⟨n-1,by omega⟩ ⟨n-1,by omega⟩‖ ≤
      frontSum hn A path (n-2) ⟨n-1,by omega⟩ := by
  let z : Fin n := ⟨n-2,by omega⟩
  let last : Fin n := ⟨n-1,by omega⟩
  let p := path z
  let r := (frontPair hn path (n-2)).1
  let s := (frontPair hn path (n-2)).2
  have hF := frontInvariant_all hn A hA path hp (n-2) le_rfl
  change FrontInvariant A path (n-2) r s at hF
  have hpf : p=r ∨ p=s := by
    by_cases hr : p=r
    · exact Or.inl hr
    right
    by_contra hs
    have h := hF.cover p (hp z).1 hr hs
    omega
  have hbound : ∀ q : Fin n, n-2 ≤ q.val → q ≠ p →
      ‖trajectory A path (n-1) last last‖ ≤
        ‖trajectory A path (n-2) q last‖ + ‖trajectory A path (n-2) p last‖ := by
    intro q hq hne
    have hswap := swap_survivor_active z p q (hp z).1 hq hne
    have he : Equiv.swap z p q=last := by
      apply Fin.ext
      change n-2<(Equiv.swap z p q).val at hswap
      have hi := (Equiv.swap z p q).isLt
      change (Equiv.swap z p q).val=n-1
      omega
    have ht := trajectory_survivor_norm A path hp (n-2) z.isLt q last hq hne (by dsimp [last]; omega)
    have hk : n-2+1=n-1 := by omega
    change ‖trajectory A path (n-2+1) (Equiv.swap z p q) last‖ ≤
      ‖trajectory A path (n-2) q last‖ + ‖trajectory A path (n-2) p last‖ at ht
    simpa only [hk, he] using ht
  change ‖trajectory A path (n-1) last last‖ ≤
    ‖trajectory A path (n-2) r last‖ + ‖trajectory A path (n-2) s last‖
  rcases hpf with hr | hs
  · have h := hbound s hF.right_active (by simpa only [hr] using Ne.symm hF.distinct)
    simpa only [hr, add_comm] using h
  · have h := hbound r hF.left_active (by simpa only [hs] using hF.distinct)
    simpa only [hs] using h

#assert_trust kernel front_step_bounds
#print axioms front_step_bounds
#assert_trust kernel final_scalar_le_frontSum
#print axioms final_scalar_le_frontSum

end NLA.IE14
