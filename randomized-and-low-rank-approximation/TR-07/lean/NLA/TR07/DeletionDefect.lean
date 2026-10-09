import NLA.TR07.ColumnAction

/-!
# Deletion deficiency

The statistic counts the minimum deletions leaving a restriction bounded below
by the threshold. Its replacement bound uses only coordinate restrictions;
no eigenvalue interlacing or concentration theorem is assumed.
-/

noncomputable section
open scoped BigOperators
open Classical
attribute [local instance] Classical.propDecidable

namespace NLA.TR07

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem exists_deletion (a : ι → E) (η : ℝ) :
    ∃ d : ℕ, ∃ D : Finset ι, D.card = d ∧ Good a η Dᶜ := by
  classical
  exact ⟨Fintype.card ι, Finset.univ, by simp, by simpa using good_empty a η⟩

/-- The least number of column deletions giving the prescribed lower bound. -/
def defect (a : ι → E) (η : ℝ) : ℕ := Nat.find (exists_deletion a η)

theorem exists_optimal_deletion (a : ι → E) (η : ℝ) :
    ∃ D : Finset ι, D.card = defect a η ∧ Good a η Dᶜ :=
  Nat.find_spec (exists_deletion a η)

theorem defect_le_card (a : ι → E) (η : ℝ) (D : Finset ι)
    (h : Good a η Dᶜ) : defect a η ≤ D.card :=
  Nat.find_min' (exists_deletion a η) ⟨D, rfl, h⟩

theorem defect_le (a : ι → E) (η : ℝ) : defect a η ≤ Fintype.card ι := by
  classical
  simpa using defect_le_card a η Finset.univ (by simpa using good_empty a η)

theorem defect_eq_zero_of_good (a : ι → E) (η : ℝ) (h : Good a η Finset.univ) :
    defect a η = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  simpa using defect_le_card a η ∅ (by simpa using h)

theorem defect_le_add_of_eq_off (a b : ι → E) (η : ℝ) (T : Finset ι)
    (hab : ∀ i, i ∉ T → a i = b i) :
    defect b η ≤ defect a η + T.card := by
  classical
  obtain ⟨D, hD, hg⟩ := exists_optimal_deletion a η
  have hsub : (D ∪ T)ᶜ ⊆ Dᶜ := by
    intro i hi
    simp only [Finset.mem_compl, Finset.mem_union, not_or] at hi ⊢
    exact hi.1
  have hg' : Good b η (D ∪ T)ᶜ := (hg.mono hsub).congr (by
    intro i hi
    apply hab
    simp only [Finset.mem_compl, Finset.mem_union, not_or] at hi
    exact hi.2)
  calc
    defect b η ≤ (D ∪ T).card := defect_le_card b η (D ∪ T) hg'
    _ ≤ D.card + T.card := Finset.card_union_le D T
    _ = defect a η + T.card := by rw [hD]

theorem defect_abs_sub_le (a b : ι → E) (η : ℝ) (T : Finset ι)
    (hab : ∀ i, i ∉ T → a i = b i) :
    |(defect b η : ℝ) - defect a η| ≤ T.card := by
  have h₁ := defect_le_add_of_eq_off a b η T hab
  have h₂ := defect_le_add_of_eq_off b a η T (fun i hi => (hab i hi).symm)
  have h₁' : (defect b η : ℝ) ≤ defect a η + T.card := by exact_mod_cast h₁
  have h₂' : (defect a η : ℝ) ≤ defect b η + T.card := by exact_mod_cast h₂
  rw [abs_le]
  constructor <;> linarith

theorem defect_update (a : ι → E) (η : ℝ) (i : ι) (v : E) :
    |(defect (Function.update a i v) η : ℝ) - defect a η| ≤ 1 := by
  classical
  simpa using defect_abs_sub_le a (Function.update a i v) η {i} (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [Function.update_of_ne hj])

private theorem defect_reindex_le (e : ι ≃ κ) (a : κ → E) (η : ℝ) :
    defect (a ∘ e) η ≤ defect a η := by
  classical
  obtain ⟨D, hD, hg⟩ := exists_optimal_deletion a η
  have hr := hg.reindex e
  have hc : Dᶜ.preimage e e.injective.injOn = (D.preimage e e.injective.injOn)ᶜ := by
    ext i
    simp
  rw [hc] at hr
  calc
    defect (a ∘ e) η ≤ (D.preimage e e.injective.injOn).card := defect_le_card _ _ _ hr
    _ = D.card := by
      have he : D.preimage e e.injective.injOn = D.map e.symm.toEmbedding := by
        ext i
        simp
      rw [he, Finset.card_map]
    _ = defect a η := hD

theorem defect_reindex (e : ι ≃ κ) (a : κ → E) (η : ℝ) :
    defect (a ∘ e) η = defect a η := by
  apply le_antisymm (defect_reindex_le e a η)
  simpa [Function.comp_def] using defect_reindex_le e.symm (a ∘ e) η

end NLA.TR07
