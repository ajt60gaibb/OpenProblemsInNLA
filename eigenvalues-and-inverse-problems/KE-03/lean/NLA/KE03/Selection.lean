import NLA.KE03.CircleNet

noncomputable section

namespace NLA.KE03

private def maxStep {α : Type*} (score : α → ℝ) (a b : α) : α := by
  classical
  exact if score a < score b then b else a

private theorem maxStep_left {α : Type*} (score : α → ℝ) (a b : α) :
    score a ≤ score (maxStep score a b) := by
  unfold maxStep
  split_ifs <;> linarith

private theorem maxStep_right {α : Type*} (score : α → ℝ) (a b : α) :
    score b ≤ score (maxStep score a b) := by
  unfold maxStep
  split_ifs <;> linarith

private theorem foldMax_mem {α : Type*} (score : α → ℝ) (l : List α) (a : α) :
    l.foldl (maxStep score) a ∈ a :: l := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons]
    have h := ih (maxStep score a b)
    simp only [List.mem_cons] at h ⊢
    rcases h with h | h
    · have hs : maxStep score a b = a ∨ maxStep score a b = b := by
        unfold maxStep
        split_ifs <;> simp
      rcases hs with hs | hs
      · exact Or.inl (h.trans hs)
      · exact Or.inr (Or.inl (h.trans hs))
    · exact Or.inr (Or.inr h)

private theorem foldMax_bound {α : Type*} (score : α → ℝ) (l : List α) (a x : α)
    (hx : x ∈ a :: l) : score x ≤ score (l.foldl (maxStep score) a) := by
  induction l generalizing a x with
  | nil => simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; simp [hx]
  | cons b l ih =>
    simp only [List.foldl_cons]
    have hb := ih (maxStep score a b) (maxStep score a b)
      (by simp : maxStep score a b ∈ maxStep score a b :: l)
    simp only [List.mem_cons] at hx
    rcases hx with hx | hx | hx
    · rw [hx]; exact (maxStep_left score a b).trans hb
    · rw [hx]; exact (maxStep_right score a b).trans hb
    · exact ih (maxStep score a b) x (by simp [hx])

theorem selectShift_mem {n : ℕ} (h : List (Vec n)) (m q : ℕ) (r : ℝ) :
    selectShift h m q r ∈ circleMesh q := by
  let score := fun u : ℂ => normSq (shiftedPower h m ((r : ℂ) * u))
  have hm := foldMax_mem score (circleMesh q) 1
  change selectShift h m q r ∈ 1 :: circleMesh q at hm
  rcases List.mem_cons.mp hm with he | he
  · rw [he]
    simp [circleMesh]
  · exact he

theorem selectShift_unit {n : ℕ} (h : List (Vec n)) (m q : ℕ) (r : ℝ) :
    ‖selectShift h m q r‖ = 1 := circleMesh_unit (selectShift_mem h m q r)

theorem selectShift_max {n : ℕ} (h : List (Vec n)) (m q : ℕ) (r : ℝ)
    {u : ℂ} (hu : u ∈ circleMesh q) :
    ‖shiftedPower h m ((r : ℂ) * u)‖ ≤
      ‖shiftedPower h m ((r : ℂ) * selectShift h m q r)‖ := by
  let score := fun u : ℂ => normSq (shiftedPower h m ((r : ℂ) * u))
  have hb := foldMax_bound score (circleMesh q) 1 u (by simp [hu])
  change normSq (shiftedPower h m ((r : ℂ) * u)) ≤
    normSq (shiftedPower h m ((r : ℂ) * selectShift h m q r)) at hb
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at hb
  nlinarith [norm_nonneg (shiftedPower h m ((r : ℂ) * u)),
    norm_nonneg (shiftedPower h m ((r : ℂ) * selectShift h m q r))]

theorem finish_spec {n m : ℕ} {h : List (Vec n)} {ε : ℝ} {z : ℂ}
    (hz : z ∈ finish h m ε) (hS : normSq (h.headD 0) ≠ 0) :
    ∃ (r : ℝ) (q : ℕ), r ∈ radiusSearch m ε (normSq (h.headD 0)) ∧
      q ∈ meshSearch ε ∧ z = (r : ℂ) * selectShift h m q r := by
  classical
  unfold finish at hz
  rw [if_neg hS] at hz
  rcases Part.mem_bind_iff.mp hz with ⟨r, hr, hz⟩
  rcases Part.mem_bind_iff.mp hz with ⟨q, hq, hz⟩
  exact ⟨r, q, hr, hq, Part.mem_some_iff.mp hz⟩

end NLA.KE03
