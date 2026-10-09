import NLA.TR07.FiniteSubsets

/-! Transfer an IID expectation bound for a coordinate-Lipschitz deficiency to uniform subsets. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace NLA.TR07
open Law

/-- Chebyshev controls IID deficiency, and the collision repair cost controls the change
from IID draws to uniform distinct draws. -/
theorem subset_prob_le_of_iid_expect
    {n r : ℕ} (hn : 0 < n) (hr : 0 < r) (hrn : r ≤ n)
    (F : (Fin r → Fin n) → ℝ) (P : Finset (Fin n) → Prop)
    (hLip : ∀ x i a, |F (Function.update x i a) - F x| ≤ 1)
    (hP : ∀ I : Fin r ↪ Fin n, P (orderedRange I) → F I = 0)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hmean : ρ * r ≤ ((@Law.uniform (Fin n) _ ⟨⟨0, hn⟩⟩).iid r).expect F) :
    subsetProbability n r P ≤ 4 / (ρ^2 * r) + (r-1) / (ρ*n) := by
  let : NeZero n := ⟨hn.ne'⟩
  obtain ⟨p, hp₁, hp₂, hpH⟩ := exists_collision_coupling (Fin n) r (by simpa using hrn)
  let μ := ((Law.uniform (Fin n)).iid r).expect F
  let t : ℝ := ρ * r / 2
  have hrR : 0 < (r:ℝ) := by exact_mod_cast hr
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have ht : 0 < t := div_pos (mul_pos hρ hrR) (by norm_num)
  have hcontain (z : (Fin r → Fin n) × (Fin r ↪ Fin n))
      (hz : P (orderedRange z.2)) :
      t ≤ |F z.1 - μ| ∨ t ≤ hamming z.1 z.2 := by
    by_contra h
    push Not at h
    have hL := abs_sub_le_hamming r F hLip z.1 z.2
    rw [hP z.2 hz, sub_zero] at hL
    have hf := (abs_lt.mp h.1).1
    have hF := le_abs_self (F z.1)
    dsimp [μ] at hf
    dsimp [t] at h
    dsimp [t] at hf
    linarith
  have hprob : subsetProbability n r P = p.prob (fun z => P (orderedRange z.2)) := by
    rw [← ordered_range_prob hrn P]
    exact (hp₂ (fun I => if P (orderedRange I) then 1 else 0)).symm
  have hcheb : p.prob (fun z => t ≤ |F z.1 - μ|) ≤ (r:ℝ) / t^2 := by
    calc
      _ = ((Law.uniform (Fin n)).iid r).prob (fun x => t ≤ |F x - μ|) :=
        hp₁ (fun x => if t ≤ |F x - μ| then 1 else 0)
      _ ≤ ((Law.uniform (Fin n)).iid r).variance F / t^2 :=
        ((Law.uniform (Fin n)).iid r).chebyshev F ht
      _ ≤ (r:ℝ) / t^2 :=
        div_le_div_of_nonneg_right (variance_iid_le _ r F hLip) (sq_nonneg t)
  have hmarkov : p.prob (fun z => t ≤ hamming z.1 z.2) ≤
      ((r:ℝ)*(r-1)/(2*n)) / t := by
    have h := p.markov (fun z => hamming z.1 z.2) (fun z => hamming_nonneg _ _) ht
    simpa only [hpH, Fintype.card_fin] using h
  have hcalc : (r:ℝ) / t^2 + ((r:ℝ)*(r-1)/(2*n)) / t =
      4 / (ρ^2*r) + (r-1) / (ρ*n) := by
    dsimp [t]
    field_simp
    ring
  rw [hprob]
  exact (p.prob_mono hcontain).trans
    ((p.prob_or_le _ _).trans ((add_le_add hcheb hmarkov).trans_eq hcalc))

end NLA.TR07
