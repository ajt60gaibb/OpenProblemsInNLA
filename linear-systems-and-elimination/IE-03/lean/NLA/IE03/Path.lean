import NLA.IE03.Definitions

/-! Composition of certified prefixes on their active squares. -/

namespace NLA.IE03

noncomputable section

def Agree (n : ℕ) (A B : Entries ℝ) : Prop :=
  ∀ i j, i < n → j < n → A i j = B i j

theorem Agree.refl (n : ℕ) (A : Entries ℝ) : Agree n A A :=
  fun _ _ _ _ => rfl

theorem Agree.symm {n : ℕ} {A B : Entries ℝ} (h : Agree n A B) : Agree n B A :=
  fun i j hi hj => (h i j hi hj).symm

theorem Agree.trans {n : ℕ} {A B C : Entries ℝ} (h : Agree n A B)
    (h' : Agree n B C) : Agree n A C :=
  fun i j hi hj => (h i j hi hj).trans (h' i j hi hj)

theorem skip_lt {n r i : ℕ} (hi : i < n) : skip r i < n + 1 := by
  unfold skip
  split <;> omega

theorem Agree.pivot {n : ℕ} {A B : Entries ℝ} {r c : ℕ}
    (h : Agree n A B) (p : IsPivot n A r c) : IsPivot n B r c := by
  obtain ⟨hr, hc, hn, hmax⟩ := p
  have he := h r c hr hc
  refine ⟨hr, hc, he ▸ hn, ?_⟩
  intro i j hi hj
  rw [← h i j hi hj, ← he]
  exact hmax i j hi hj

theorem Agree.schur {n : ℕ} {A B : Entries ℝ} {r c : ℕ}
    (h : Agree (n + 1) A B) (hr : r < n + 1) (hc : c < n + 1) :
    Agree n (IE03.schur A r c) (IE03.schur B r c) := by
  intro i j hi hj
  simp only [IE03.schur, h _ _ (skip_lt hi) (skip_lt hj), h _ _ (skip_lt hi) hc,
    h _ _ hr (skip_lt hj), h _ _ hr hc]

theorem PivotPrefix.growth_nonneg {n m : ℕ} {A B : Entries ℝ} {g : ℝ}
    (h : PivotPrefix n A m B g) : 0 ≤ g := by
  cases h with
  | empty => exact le_rfl
  | step r c _ _ => exact (abs_nonneg (A r c)).trans (le_max_left _ _)

theorem PivotPrefix.append {n m k : ℕ} {A B C : Entries ℝ} {g f : ℝ}
    (h : PivotPrefix n A m B g) (h' : PivotPrefix m B k C f) :
    PivotPrefix n A k C (max g f) := by
  induction h with
  | empty => simpa only [max_eq_right h'.growth_nonneg] using h'
  | step r c hp _ ih =>
    simpa only [max_assoc] using PivotPrefix.step r c hp (ih h')

theorem PivotPrefix.transport {n m : ℕ} {A B A' : Entries ℝ} {g : ℝ}
    (h : PivotPrefix n A m B g) (e : Agree n A A') :
    ∃ B', PivotPrefix n A' m B' g ∧ Agree m B B' := by
  induction h generalizing A' with
  | empty n _ => exact ⟨A', .empty n A', e⟩
  | step r c hp _ ih =>
    obtain ⟨B', hB', hAgree⟩ := ih (e.schur hp.1 hp.2.1)
    refine ⟨B', ?_, hAgree⟩
    rw [e _ _ hp.1 hp.2.1]
    exact .step r c (e.pivot hp) hB'

/-- A prefix whose last active square is represented by the entries of `B`.
The padding of the terminal function can differ. -/
def Trace (n : ℕ) (A : Entries ℝ) (m : ℕ) (B : Entries ℝ) (g : ℝ) : Prop :=
  ∃ B', PivotPrefix n A m B' g ∧ Agree m B' B

theorem Trace.empty (n : ℕ) (A : Entries ℝ) : Trace n A n A 0 :=
  ⟨A, .empty n A, .refl n A⟩

theorem Trace.start {n m : ℕ} {A A' B : Entries ℝ} {g : ℝ}
    (h : Trace n A m B g) (e : Agree n A A') : Trace n A' m B g := by
  obtain ⟨C, hC, hCB⟩ := h
  obtain ⟨C', hC', hCC'⟩ := hC.transport e
  exact ⟨C', hC', hCC'.symm.trans hCB⟩

theorem Trace.finish {n m : ℕ} {A B B' : Entries ℝ} {g : ℝ}
    (h : Trace n A m B g) (e : Agree m B B') : Trace n A m B' g := by
  obtain ⟨C, hC, hCB⟩ := h
  exact ⟨C, hC, hCB.trans e⟩

theorem Trace.step {n m r c : ℕ} {A B : Entries ℝ} {g : ℝ}
    (hp : IsPivot (n + 1) A r c) (h : Trace n (schur A r c) m B g) :
    Trace (n + 1) A m B (max |A r c| g) := by
  obtain ⟨B', hB', he⟩ := h
  exact ⟨B', .step r c hp hB', he⟩

theorem Trace.append {n m k : ℕ} {A B C : Entries ℝ} {g f : ℝ}
    (h : Trace n A m B g) (h' : Trace m B k C f) : Trace n A k C (max g f) := by
  obtain ⟨B', hB', e⟩ := h
  obtain ⟨C', hC', e'⟩ := h'.start e.symm
  exact ⟨C', hB'.append hC', e'⟩

theorem Trace.complete {n : ℕ} {A B : Entries ℝ} {g : ℝ}
    (h : Trace n A 0 B g) : CompletePath n A g := by
  obtain ⟨B', hB', _⟩ := h
  exact ⟨B', hB'⟩

end

end NLA.IE03
