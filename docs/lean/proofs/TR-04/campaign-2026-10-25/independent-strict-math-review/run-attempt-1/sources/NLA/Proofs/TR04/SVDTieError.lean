import NLA.Proofs.TR04.SVDTieProjectors

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04.SVD
open NLA.Computation.SVDMachine

theorem prefixEnergy_eq_sum_fin {p r : ℕ} (hr : r ≤ p) (f : Fin p → ℝ) :
    prefixEnergy f r = ∑ k : Fin r, f (Fin.castLE hr k) := by
  rw [prefixEnergy, sum_fin_truncate hr]
  · simp
  · intro k hk
    simp [Nat.not_lt.mpr hk]

theorem sum_prefixDirections {p h t : ℕ} (ht : h + t ≤ p) (f : Fin p → ℝ) :
    (∑ k ∈ prefixDirections h t ht, f k) =
      ∑ k : Fin h, f (Fin.castLE ((Nat.le_add_right h t).trans ht) k) := by
  rw [prefixDirections, Finset.sum_image]
  intro i _ j _ he
  exact Fin.ext (congrArg (fun k : Fin p => k.val) he)

theorem prefixEnergy_tie_split {p h t : ℕ} (ht : h + t ≤ p)
    (s : ℕ) (hst : s ≤ t) (f : Fin p → ℝ) (c : ℝ)
    (hf : ∀ i : Fin t, f (tieEmbedding h t ht i) = c) :
    prefixEnergy f (h + s) = (∑ k ∈ prefixDirections h t ht, f k) + (s : ℝ) * c := by
  have hrs : h + s ≤ p := (Nat.add_le_add_left hst h).trans ht
  rw [prefixEnergy_eq_sum_fin hrs, Fin.sum_univ_add, sum_prefixDirections]
  congr 1
  have hi (i : Fin s) : f (Fin.castLE hrs (Fin.natAdd h i)) = c := by
    have he : Fin.castLE hrs (Fin.natAdd h i) =
        tieEmbedding h t ht ⟨i.val, lt_of_lt_of_le i.isLt hst⟩ := Fin.ext rfl
    rw [he, hf]
  simp_rw [hi]
  simp

theorem sum_tieSelection_constant_block {p h t : ℕ} [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (hst : s ≤ t) (j : Fin t) (f : Fin p → ℝ) (c : ℝ)
    (hf : ∀ i : Fin t, f (tieEmbedding h t ht i) = c) :
    (∑ k ∈ tieSelection h t ht s j, f k) = prefixEnergy f (h + s) := by
  rw [sum_tieSelection ht s j, prefixEnergy_tie_split ht s hst f c hf]
  congr 1
  simp_rw [hf]
  have hterm (i : Fin t) : (if cyclicWindow s j i then c else 0) =
      (if cyclicWindow s j i then (1 : ℝ) else 0) * c := by split_ifs <;> simp
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  have hc : (∑ i : Fin t, if cyclicWindow s j i then (1 : ℝ) else 0) = s := by
    have hcard := card_cyclicWindow s hst j
    rw [Fintype.card_subtype] at hcard
    have hsum := Finset.card_filter (cyclicWindow s j) (Finset.univ : Finset (Fin t))
    have hsum' : (∑ i : Fin t, if cyclicWindow s j i then (1 : ℕ) else 0) = s := by
      rw [← hsum]
      exact hcard
    exact_mod_cast hsum'
  rw [hc]

/-- Every tested H-plus-window projector has exactly the original first-cut
discarded energy, in every supplied legal SVD basis. -/
theorem validSVD_tieSelection_error {m l h t : ℕ} [NeZero t]
    {B : Matrix (Fin m) (Fin l) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {sigma : Fin (min m l) → ℝ} {V : Matrix (Fin l) (Fin l) ℝ}
    (hsvd : ValidSVD B U sigma V) (ht : h + t ≤ min m l)
    (s : ℕ) (hst : s ≤ t) (j : Fin t) (tau : ℝ)
    (htau : ∀ i : Fin t, sigma (tieEmbedding h t ht i) = tau) :
    matrixEnergy (B - projectMatrix (directionSubspace U (tieSelection h t ht s j)) B) =
      tailEnergy sigma (h + s) := by
  have hpy := projectMatrix_energy_decomposition
    (directionSubspace U (tieSelection h t ht s j)) B
  have hc : matrixEnergy (projectMatrix (directionSubspace U (tieSelection h t ht s j)) B) =
      prefixEnergy (fun k => (sigma k)^2) (h + s) := by
    rw [directionSubspace, validSVD_selected_energy hsvd, sum_indicator_finset]
    exact sum_tieSelection_constant_block ht s hst j (fun k => (sigma k)^2) (tau^2)
      (by intro i; rw [htau])
  rw [validSVD_energy hsvd, hc] at hpy
  have hs := prefix_add_tail sigma (h + s)
  linarith

#assert_trust kernel sum_tieSelection_constant_block
#assert_trust kernel validSVD_tieSelection_error
#print axioms validSVD_tieSelection_error
end NLA.Proofs.TR04.SVD
