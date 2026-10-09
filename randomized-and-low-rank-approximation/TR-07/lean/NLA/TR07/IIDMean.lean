import NLA.TR07.FiniteBlocks
import NLA.TR07.FiniteCommonReservoir

/-! Expected deletion deficiency from a common independent reservoir. -/
noncomputable section
open scoped BigOperators
namespace NLA.TR07
open Law
variable {α δ ξ : Type*} [Fintype α] [Fintype δ] [Fintype ξ]
  [DecidableEq δ] [DecidableEq ξ]

private def countCenters (m : ℕ) (R : α → (δ → α) → Prop)
    (x : Fin m ⊕ (δ ⊕ ξ) → α) : ℝ := by
  classical
  exact ∑ i : Fin m, if R (x (Sum.inl i)) (fun j => x (Sum.inr (Sum.inl j))) then 1 else 0

private theorem countCenters_expect (p : Law α) (m : ℕ) (R : α → (δ → α) → Prop) :
    (p.power (Fin m ⊕ (δ ⊕ ξ))).expect (countCenters m R) =
      (m:ℝ) * p.expect (fun a => (p.power δ).prob (fun y => R a y)) := by
  classical
  simp only [countCenters, expect_power_sum, Sum.elim_inl, Sum.elim_inr, power_fin]
  rw [expect_comm]
  calc
    _ = (p.power δ).expect (fun y => (m:ℝ) * p.prob (fun a => R a y)) := by
      apply expect_congr
      intro y
      calc
        _ = (p.iid m).expect (fun x => ∑ i, if R (x i) y then (1:ℝ) else 0) := by
          apply expect_congr
          intro x
          calc
            _ = (p.power ξ).expect (fun _ => ∑ i : Fin m, if R (x i) y then (1:ℝ) else 0) := by
              apply expect_congr
              intro z
              apply Finset.sum_congr rfl
              intro i _
              by_cases h : R (x i) y <;> simp [h]
            _ = _ := (p.power ξ).expect_const _
        _ = _ := expect_iid_sum p m (fun a => if R a y then 1 else 0)
    _ = _ := by
      rw [expect_const_mul]
      congr 1
      exact expect_comm (p.power δ) p (fun y a => if R a y then 1 else 0)

/-- A lower bound for each center's reconstruction probability gives an expected deficiency bound. -/
theorem expected_defect_blocks {k : ℕ} (p : Law α) (u : α → Vec k)
    {η : ℝ} (hη : 0 < η) (m : ℕ) :
    (m:ℝ)/2 * p.expect (fun a => (p.power δ).prob
      (fun y => Reconstructible (u a) (fun j => u (y j)) (η/2))) ≤
      (p.power (Fin m ⊕ (δ ⊕ ξ))).expect (fun x => (defect (fun j => u (x j)) η : ℝ)) := by
  classical
  let R (a : α) (y : δ → α) := Reconstructible (u a) (fun j => u (y j)) (η/2)
  have hpoint (x : Fin m ⊕ (δ ⊕ ξ) → α) :
      countCenters m R x / 2 ≤ (defect (fun j => u (x j)) η : ℝ) := by
    have h := defect_ge_half_reconstructible (fun j => u (x j)) hη
    simpa only [countCenters, Finset.sum_boole, R] using h
  have h := (p.power (Fin m ⊕ (δ ⊕ ξ))).expect_mono hpoint
  have he : (p.power (Fin m ⊕ (δ ⊕ ξ))).expect (fun x => countCenters m R x / 2) =
      (m:ℝ)/2 * p.expect (fun a => (p.power δ).prob (R a)) := by
    simp only [div_eq_mul_inv, expect_mul_const, countCenters_expect]
    ring
  rwa [he] at h

/-- The shared reservoir occupies `b*L*ℓ` columns; the remaining columns can be ignored. -/
theorem expected_defect_of_reconstruction {k : ℕ} (p : Law α) (u : α → Vec k)
    {η : ℝ} (hη : 0 < η) (m L b ℓ r : ℕ) (hsize : m + b*L*ℓ ≤ r) {q : ℝ}
    (hprob : q ≤ p.expect (fun a => (((p.iid ℓ).iid L).iid b).prob (fun z =>
      Reconstructible (u a) (fun i : Fin b × Fin L × Fin ℓ => u (z i.1 i.2.1 i.2.2)) (η/2)))) :
    q*(m:ℝ)/2 ≤ (p.iid r).expect (fun x => (defect (fun j => u (x j)) η : ℝ)) := by
  classical
  let δ := Fin b × Fin L × Fin ℓ
  let ξ := Fin (r-(m+b*L*ℓ))
  let ι := Fin m ⊕ (δ ⊕ ξ)
  have hcard : Fintype.card ι = r := by
    simp only [ι, δ, ξ, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    simp only [← Nat.mul_assoc]
    omega
  let e : ι ≃ Fin r := Fintype.equivFinOfCardEq hcard
  have he : (p.iid r).expect (fun x => (defect (fun j => u (x j)) η : ℝ)) =
      (p.power ι).expect (fun x => (defect (fun j => u (x j)) η : ℝ)) := by
    rw [← power_fin, expect_power_equiv p e]
    apply expect_congr
    intro x
    exact_mod_cast defect_reindex e.symm (fun j => u (x j)) η
  have hprob' : q ≤ p.expect (fun a => (p.power δ).prob
      (fun y => Reconstructible (u a) (fun j => u (y j)) (η/2))) := by
    convert hprob using 1
    apply expect_congr
    intro a
    exact expect_power_triple_fin p b L ℓ (fun y =>
      if Reconstructible (u a) (fun j => u (y j)) (η/2) then 1 else 0)
  rw [he]
  calc
    q*(m:ℝ)/2 ≤ (m:ℝ)/2 * p.expect (fun a => (p.power δ).prob
        (fun y => Reconstructible (u a) (fun j => u (y j)) (η/2))) := by
      nlinarith [mul_le_mul_of_nonneg_right hprob' (Nat.cast_nonneg m)]
    _ ≤ _ := expected_defect_blocks (δ := δ) (ξ := ξ) p u hη m

end NLA.TR07
