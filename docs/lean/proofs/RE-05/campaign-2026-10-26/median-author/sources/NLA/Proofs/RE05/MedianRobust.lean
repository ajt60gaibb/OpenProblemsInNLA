import NLA.Proofs.RE05.MedianRadius

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery

theorem coefficientDistance_symm {n q : ℕ} (P : Basis n q)
    (x y : Fin (q + 1) → ℝ) :
    coefficientDistance P x y = coefficientDistance P y x := by
  simp only [coefficientDistance, frobenius_eq_norm]
  exact norm_sub_rev _ _

theorem coefficientDistance_triangle {n q : ℕ} (P : Basis n q)
    (x y z : Fin (q + 1) → ℝ) :
    coefficientDistance P x z ≤ coefficientDistance P x y + coefficientDistance P y z :=
  frobenius_triangle _ _ _

/-- Two sets of eight indices among the literal fifteen copies intersect. -/
theorem eight_intersection (s t : Finset (Fin 15)) (hs : 8 ≤ s.card) (ht : 8 ≤ t.card) :
    ∃ j, j ∈ s ∧ j ∈ t := by
  have hu : (s ∪ t).card ≤ 15 := by
    simpa using Finset.card_le_univ (s ∪ t)
  have hc := Finset.card_inter_add_card_union s t
  have hp : 0 < (s ∩ t).card := by omega
  rcases Finset.card_pos.mp hp with ⟨j, hj⟩
  exact ⟨j, Finset.mem_inter.mp hj⟩

/-- Eight good copies force the actual sorted-median/scan output within
three radii of the same true coefficient vector, including radius zero. -/
theorem postprocess_distance_of_eight {n q : ℕ} (P : Basis n q)
    (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ))
    (center : Fin (q + 1) → ℝ) (ρ : ℝ)
    (hgood : 8 ≤ (Finset.univ.filter fun j : Fin 15 =>
      coefficientDistance P (copyOutput P schedule responses j) center ≤ ρ).card) :
    coefficientDistance P (postprocess P schedule responses) center ≤ 3 * ρ := by
  classical
  let G := Finset.univ.filter fun j : Fin 15 =>
    coefficientDistance P (copyOutput P schedule responses j) center ≤ ρ
  have hG : 8 ≤ G.card := hgood
  rcases Finset.card_pos.mp (show 0 < G.card by omega) with ⟨g, hg⟩
  have hgρ := (Finset.mem_filter.mp hg).2
  have hgball : medianRadius P schedule responses g ≤ 2 * ρ := by
    apply medianRadius_le_of_eight
    apply hG.trans
    apply Finset.card_le_card
    intro j hj
    have hjρ := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have ht := coefficientDistance_triangle P
      (copyOutput P schedule responses g) center (copyOutput P schedule responses j)
    rw [coefficientDistance_symm P center _] at ht
    linarith
  let chosen := chooseCopy P schedule responses
  have hchosen : medianRadius P schedule responses chosen ≤ 2 * ρ :=
    (chooseCopy_le P schedule responses g).trans hgball
  let B := Finset.univ.filter fun j : Fin 15 =>
    coefficientDistance P (copyOutput P schedule responses chosen)
      (copyOutput P schedule responses j) ≤ medianRadius P schedule responses chosen
  have hB : 8 ≤ B.card := medianRadius_eight P schedule responses chosen
  rcases eight_intersection G B hG hB with ⟨j, hjG, hjB⟩
  have hjρ := (Finset.mem_filter.mp hjG).2
  have hclose := (Finset.mem_filter.mp hjB).2
  have ht := coefficientDistance_triangle P (copyOutput P schedule responses chosen)
    (copyOutput P schedule responses j) center
  change coefficientDistance P (copyOutput P schedule responses chosen) center ≤ _
  linarith

/-- The manuscript's eight-copy squared-error event implies the literal
pure relative-error bound for the actual postprocessor. No nonzero-optimum
premise is needed. -/
theorem postprocess_relative_of_eight {n q : ℕ} (P : Basis n q)
    (A : Square n) (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hgood : 8 ≤ (Finset.univ.filter fun j : Fin 15 =>
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent P (copyOutput P schedule responses j)) ^ 2 ≤
      (1 + squaredAccuracy ε) * NLA.Computation.LinearFamilyQuery.optimum P A ^ 2).card) :
    NLA.Computation.NonadaptiveMatrixQuery.frobenius A
      (represent P (postprocess P schedule responses)) ≤
        (1 + ε) * NLA.Computation.LinearFamilyQuery.optimum P A := by
  classical
  rcases exists_pythagorean_optimum P A with ⟨center, hopt, hpy⟩
  let o := NLA.Computation.LinearFamilyQuery.optimum P A
  let δ := squaredAccuracy ε * o ^ 2
  let ρ := Real.sqrt δ
  have ho : 0 ≤ o := by
    rw [show o = NLA.Computation.NonadaptiveMatrixQuery.frobenius A
      (represent P center) from hopt.symm]
    exact Real.sqrt_nonneg _
  have hδ : 0 ≤ δ := mul_nonneg (by dsimp [squaredAccuracy]; positivity) (sq_nonneg o)
  have hρ : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρsq : ρ ^ 2 = δ := Real.sq_sqrt hδ
  have hnear : 8 ≤ (Finset.univ.filter fun j : Fin 15 =>
      coefficientDistance P (copyOutput P schedule responses j) center ≤ ρ).card := by
    apply hgood.trans
    apply Finset.card_le_card
    intro j hj
    have hjerr := (Finset.mem_filter.mp hj).2
    have hp := hpy (copyOutput P schedule responses j)
    have hn : 0 ≤ coefficientDistance P (copyOutput P schedule responses j) center :=
      Real.sqrt_nonneg _
    have hd : coefficientDistance P (copyOutput P schedule responses j) center ^ 2 ≤ δ := by
      change NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent P (copyOutput P schedule responses j)) ^ 2 =
          o ^ 2 + coefficientDistance P center (copyOutput P schedule responses j) ^ 2 at hp
      rw [coefficientDistance_symm P center _] at hp
      dsimp [δ, o]
      nlinarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by nlinarith⟩
  have hout := postprocess_distance_of_eight P schedule responses center ρ hnear
  have hpout := hpy (postprocess P schedule responses)
  change NLA.Computation.NonadaptiveMatrixQuery.frobenius A
    (represent P (postprocess P schedule responses)) ^ 2 =
      o ^ 2 + coefficientDistance P center (postprocess P schedule responses) ^ 2 at hpout
  rw [coefficientDistance_symm P center _] at hpout
  have hdout : 0 ≤ coefficientDistance P (postprocess P schedule responses) center :=
    Real.sqrt_nonneg _
  have hsq : NLA.Computation.NonadaptiveMatrixQuery.frobenius A
      (represent P (postprocess P schedule responses)) ^ 2 ≤ (1 + ε) * o ^ 2 := by
    dsimp [δ, squaredAccuracy] at hρsq
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right
    (show 1 + ε ≤ (1 + ε) ^ 2 by nlinarith) (sq_nonneg o)
  have hright : 0 ≤ (1 + ε) * o := mul_nonneg (by linarith) ho
  nlinarith

#assert_trust kernel coefficientDistance_symm
#assert_trust kernel coefficientDistance_triangle
#assert_trust kernel eight_intersection
#assert_trust kernel postprocess_distance_of_eight
#assert_trust kernel postprocess_relative_of_eight
#print axioms coefficientDistance_symm
#print axioms coefficientDistance_triangle
#print axioms eight_intersection
#print axioms postprocess_distance_of_eight
#print axioms postprocess_relative_of_eight
end NLA.Proofs.RE05
