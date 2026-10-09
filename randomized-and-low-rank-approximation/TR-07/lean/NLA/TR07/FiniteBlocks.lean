import NLA.TR07.FiniteVariance
import Mathlib.Logic.Equiv.Prod

/-! Independent finite blocks, including reindexing and regrouping their coordinates. -/
noncomputable section
open scoped BigOperators
namespace NLA.TR07.Law
variable {α ι κ : Type*} [Fintype α] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Independent copies of a finite law indexed by an arbitrary finite type. -/
def power (p : Law α) (ι : Type*) [Fintype ι] [DecidableEq ι] : Law (ι → α) where
  wt x := ∏ i, p.wt (x i)
  nonneg x := Finset.prod_nonneg fun i _ => p.nonneg _
  sum_eq_one := by rw [← Fintype.prod_sum]; simp [p.sum_eq_one]

@[simp] theorem power_wt (p : Law α) (x : ι → α) : (p.power ι).wt x = ∏ i, p.wt (x i) := rfl

@[simp] theorem power_fin (p : Law α) (n : ℕ) : p.power (Fin n) = p.iid n := rfl

theorem expect_power_equiv (p : Law α) (e : ι ≃ κ) (f : (κ → α) → ℝ) :
    (p.power κ).expect f = (p.power ι).expect (fun x => f (x ∘ e.symm)) := by
  unfold expect
  rw [← Equiv.sum_comp (Equiv.arrowCongr e (Equiv.refl α))]
  apply Finset.sum_congr rfl
  intro x _
  change (∏ j : κ, p.wt (x (e.symm j))) * f (x ∘ e.symm) = _
  rw [Equiv.prod_comp e.symm (fun i => p.wt (x i))]
  rfl

theorem expect_power_sum (p : Law α) (f : (ι ⊕ κ → α) → ℝ) :
    (p.power (ι ⊕ κ)).expect f =
      (p.power ι).expect (fun x => (p.power κ).expect (fun y => f (Sum.elim x y))) := by
  unfold expect
  rw [← Equiv.sum_comp (Equiv.sumArrowEquivProdArrow ι κ α).symm]
  simp only [Fintype.sum_prod_type, power_wt, Fintype.prod_sum_type,
    Equiv.sumArrowEquivProdArrow_symm_apply_inl, Equiv.sumArrowEquivProdArrow_symm_apply_inr,
    Finset.mul_sum, mul_assoc]
  rfl

theorem expect_power_prod (p : Law α) (f : (ι × κ → α) → ℝ) :
    (p.power (ι × κ)).expect f =
      ((p.power κ).power ι).expect (fun x => f (fun j => x j.1 j.2)) := by
  unfold expect
  rw [← Equiv.sum_comp (Equiv.curry ι κ α).symm]
  apply Finset.sum_congr rfl
  intro x _
  change (∏ j : ι × κ, p.wt (x j.1 j.2)) * f (fun j => x j.1 j.2) = _
  rw [Fintype.prod_prod_type]
  rfl

/-- Pointwise relabeling commutes with an independent product. -/
theorem expect_power_map {β : Type*} [Fintype β] (p : Law α) (g : α → β)
    (f : (ι → β) → ℝ) :
    ((p.map g).power ι).expect f = (p.power ι).expect (fun x => f (g ∘ x)) := by
  let e := Fintype.equivFin ι
  rw [expect_power_equiv _ e.symm, expect_power_equiv _ e.symm]
  simp only [power_fin]
  -- IID mapping is proved here without any kernel support assumptions.
  have hm (n : ℕ) (h : (Fin n → β) → ℝ) :
      ((p.map g).iid n).expect h = (p.iid n).expect (fun x => h (g ∘ x)) := by
    induction n with
    | zero => simp only [expect_iid_zero]; congr 1; funext i; exact Fin.elim0 i
    | succ n ih =>
      rw [expect_iid_succ, expect_iid_succ, expect_map]
      apply p.expect_congr
      intro a
      rw [ih]
      apply (p.iid n).expect_congr
      intro x
      congr 1
      funext j
      refine Fin.cases rfl (fun _ => rfl) j
  exact hm _ _

theorem expect_power_triple_fin (p : Law α) (b L ℓ : ℕ)
    (f : (Fin b × Fin L × Fin ℓ → α) → ℝ) :
    (p.power (Fin b × Fin L × Fin ℓ)).expect f =
      (((p.iid ℓ).iid L).iid b).expect (fun z => f (fun i => z i.1 i.2.1 i.2.2)) := by
  have hinner : p.power (Fin L × Fin ℓ) =
      (((p.iid ℓ).iid L).map (fun z => fun i : Fin L × Fin ℓ => z i.1 i.2)) := by
    apply (expect_eq_iff _ _).mp
    intro g
    rw [expect_power_prod, expect_map]
    rfl
  rw [expect_power_prod, hinner, expect_power_map]
  rfl

end NLA.TR07.Law
