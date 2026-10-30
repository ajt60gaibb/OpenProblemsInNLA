import NLA.Proofs.TR04.SVDCyclicSelection

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04.SVD

def directionSubspace {m l : ℕ} (U : Matrix (Fin m) (Fin m) ℝ)
    (S : Finset (Fin (min m l))) : Submodule ℝ (Space m) :=
  singularSubspace U (fun k => k ∈ S)

theorem directionSubspace_project_energy {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (S : Finset (Fin (min m l))) (R : Matrix (Fin m) (Fin l) ℝ) :
    matrixEnergy (projectMatrix (directionSubspace U S) R) =
      ∑ k ∈ S, singularCoordinateEnergy U R k := by
  rw [directionSubspace, singularSubspace_projectMatrix_energy hU, sum_indicator_finset]

set_option backward.isDefEq.respectTransparency false in
theorem rank_directionFrame {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (S : Finset (Fin (min m l))) :
    Matrix.rank (selectedFrame U (fun k => k ∈ S)) = S.card := by
  have hs : Finset.Subtype.fintype S = Subtype.fintype (fun k => k ∈ S) :=
    Subsingleton.elim _ _
  rw [hs]
  simpa only [Fintype.card_coe] using rank_selectedFrame (l := l) hU (fun k => k ∈ S)

theorem rank_directionProjection_le {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (S : Finset (Fin (min m l))) (B : Matrix (Fin m) (Fin l) ℝ) :
    Matrix.rank (projectMatrix (directionSubspace U S) B) ≤ S.card := by
  simpa only [directionSubspace, Fintype.card_coe] using
    rank_selected_projection_le_card hU (fun k => k ∈ S) B

theorem rank_tieSelectionFrame {m l h t : ℕ} [NeZero t]
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (ht : h + t ≤ min m l) (s : ℕ) (hst : s ≤ t) (j : Fin t) :
    Matrix.rank (selectedFrame U (fun k => k ∈ tieSelection h t ht s j)) = h + s := by
  rw [rank_directionFrame hU, card_tieSelection ht s hst j]

theorem rank_tieSelectionProjection_le {m l h t : ℕ} [NeZero t]
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (ht : h + t ≤ min m l) (s : ℕ) (hst : s ≤ t) (j : Fin t)
    (B : Matrix (Fin m) (Fin l) ℝ) :
    Matrix.rank (projectMatrix (directionSubspace U (tieSelection h t ht s j)) B) ≤ h + s := by
  simpa only [card_tieSelection ht s hst j] using
    rank_directionProjection_le hU (tieSelection h t ht s j) B

/-- The actual total projected residual energy over all t candidates. -/
theorem sum_tieSelection_project_energy {m l h t : ℕ} [NeZero t]
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (ht : h + t ≤ min m l) (s : ℕ) (hst : s ≤ t)
    (R : Matrix (Fin m) (Fin l) ℝ) :
    (∑ j : Fin t, matrixEnergy
      (projectMatrix (directionSubspace U (tieSelection h t ht s j)) R)) =
      (t : ℝ) * matrixEnergy (projectMatrix (directionSubspace U (prefixDirections h t ht)) R) +
        (s : ℝ) * matrixEnergy (projectMatrix (directionSubspace U (tieDirections h t ht)) R) := by
  simp_rw [directionSubspace_project_energy hU]
  exact sum_all_tieSelections ht s hst (singularCoordinateEnergy U R)

theorem average_tieSelection_project_energy {m l h t : ℕ} [NeZero t]
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (ht : h + t ≤ min m l) (s : ℕ) (hst : s ≤ t)
    (R : Matrix (Fin m) (Fin l) ℝ)
    (hH : projectMatrix (directionSubspace U (prefixDirections h t ht)) R = 0) :
    (∑ j : Fin t, matrixEnergy
      (projectMatrix (directionSubspace U (tieSelection h t ht s j)) R)) / t =
      ((s : ℝ) / t) * matrixEnergy
        (projectMatrix (directionSubspace U (tieDirections h t ht)) R) := by
  rw [sum_tieSelection_project_energy hU ht s hst, hH]
  simp only [matrixEnergy, Matrix.zero_apply, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, mul_zero, zero_add]
  ring

theorem average_tieSelection_project_energy_le {m l h t : ℕ} [NeZero t]
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (ht : h + t ≤ min m l) (s : ℕ) (hst : s ≤ t)
    (R : Matrix (Fin m) (Fin l) ℝ)
    (hH : projectMatrix (directionSubspace U (prefixDirections h t ht)) R = 0) :
    (∑ j : Fin t, matrixEnergy
      (projectMatrix (directionSubspace U (tieSelection h t ht s j)) R)) / t ≤
        ((s : ℝ) / t) * matrixEnergy R := by
  rw [average_tieSelection_project_energy hU ht s hst R hH]
  have hpy := projectMatrix_energy_decomposition (directionSubspace U (tieDirections h t ht)) R
  have hn := matrixEnergy_nonneg (R - projectMatrix (directionSubspace U (tieDirections h t ht)) R)
  apply mul_le_mul_of_nonneg_left (by linarith)
  positivity

theorem exists_tieSelection_project_energy_le {m l h t : ℕ} [NeZero t]
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (ht : h + t ≤ min m l) (s : ℕ) (hst : s ≤ t)
    (R : Matrix (Fin m) (Fin l) ℝ)
    (hH : projectMatrix (directionSubspace U (prefixDirections h t ht)) R = 0) :
    ∃ j : Fin t, matrixEnergy (projectMatrix (directionSubspace U (tieSelection h t ht s j)) R) ≤
      ((s : ℝ) / t) * matrixEnergy R := by
  classical
  have htpos : 0 < (t : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t)
  have havg := average_tieSelection_project_energy_le hU ht s hst R hH
  by_contra hn
  push Not at hn
  have hsum : (∑ j : Fin t, ((s : ℝ) / t) * matrixEnergy R) <
      ∑ j : Fin t, matrixEnergy (projectMatrix (directionSubspace U (tieSelection h t ht s j)) R) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hn j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hle := (div_le_iff₀ htpos).mp havg
  nlinarith

#assert_trust kernel rank_tieSelectionFrame
#assert_trust kernel sum_tieSelection_project_energy
#assert_trust kernel average_tieSelection_project_energy
#assert_trust kernel exists_tieSelection_project_energy_le
#print axioms exists_tieSelection_project_energy_le
end NLA.Proofs.TR04.SVD
