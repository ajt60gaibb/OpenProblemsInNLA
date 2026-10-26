import NLA.Proofs.TR04.SVDTieStructure

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04.SVD
open NLA.Computation.SVDMachine

theorem mem_prefixDirections_iff {p h t : ℕ} (ht : h + t ≤ p) (k : Fin p) :
    k ∈ prefixDirections h t ht ↔ k.val < h := by
  constructor
  · intro hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    exact i.isLt
  · intro hk
    exact Finset.mem_image.mpr ⟨⟨k.val, hk⟩, Finset.mem_univ _, Fin.ext rfl⟩

theorem tieSelection_val_lt {p h t : ℕ} [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (j : Fin t) (k : Fin p) (hk : k ∈ tieSelection h t ht s j) :
    k.val < h + t := by
  rcases Finset.mem_union.mp hk with hk | hk
  · have hv := (mem_prefixDirections_iff ht k).mp hk
    omega
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    exact Nat.add_lt_add_left i.isLt h

theorem TieStructure.above_subspace {m l : ℕ}
    {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)} (T : TieStructure sigma a)
    (U : Matrix (Fin m) (Fin m) ℝ) :
    directionSubspace U (prefixDirections T.above T.tied T.fits) =
      singularSubspace U (fun k => sigma a < sigma k) := by
  unfold directionSubspace
  congr 1
  funext k
  apply propext
  exact (mem_prefixDirections_iff T.fits k).trans (T.above_iff k).symm

theorem TieStructure.first_error {m l : ℕ}
    {B : Matrix (Fin m) (Fin l) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {sigma : Fin (min m l) → ℝ} {V : Matrix (Fin l) (Fin l) ℝ}
    (h : ValidSVD B U sigma V) {a : Fin (min m l)} (T : TieStructure sigma a)
    (j : Fin T.tied) :
    matrixEnergy (B - projectMatrix
      (directionSubspace U (tieSelection T.above T.tied T.fits T.take j)) B) =
        tailEnergy sigma (a.val + 1) := by
  rw [← T.rank_eq]
  exact validSVD_tieSelection_error h T.fits T.take T.take_le j (sigma a) T.equal_embedding

theorem TieStructure.frame_rank {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)} (T : TieStructure sigma a)
    (j : Fin T.tied) :
    Matrix.rank (selectedFrame U (fun k =>
      k ∈ tieSelection T.above T.tied T.fits T.take j)) = a.val + 1 := by
  rw [rank_tieSelectionFrame hU T.fits T.take T.take_le j, T.rank_eq]

theorem TieStructure.equality_above_residual_zero {m l : ℕ}
    {B : Matrix (Fin m) (Fin l) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {sigma : Fin (min m l) → ℝ} {V : Matrix (Fin l) (Fin l) ℝ}
    (h : ValidSVD B U sigma V) {a : Fin (min m l)} (T : TieStructure sigma a)
    (ha : 0 < sigma a) (Y : Matrix (Fin m) (Fin l) ℝ)
    (hY : Matrix.rank Y ≤ a.val + 1)
    (heq : matrixEnergy (B - Y) = tailEnergy sigma (a.val + 1)) :
    projectMatrix (directionSubspace U (prefixDirections T.above T.tied T.fits)) (B - Y) = 0 := by
  rw [T.above_subspace]
  exact (validSVD_equality_above_span_residual h a ha Y hY heq).2

theorem TieStructure.equality_average_residual {m l : ℕ}
    {B : Matrix (Fin m) (Fin l) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {sigma : Fin (min m l) → ℝ} {V : Matrix (Fin l) (Fin l) ℝ}
    (h : ValidSVD B U sigma V) {a : Fin (min m l)} (T : TieStructure sigma a)
    (ha : 0 < sigma a) (Y : Matrix (Fin m) (Fin l) ℝ)
    (hY : Matrix.rank Y ≤ a.val + 1)
    (heq : matrixEnergy (B - Y) = tailEnergy sigma (a.val + 1)) :
    (∑ j : Fin T.tied, matrixEnergy (projectMatrix
      (directionSubspace U (tieSelection T.above T.tied T.fits T.take j)) (B - Y))) / T.tied =
        ((T.take : ℝ) / T.tied) * matrixEnergy
          (projectMatrix (directionSubspace U (tieDirections T.above T.tied T.fits)) (B - Y)) :=
  average_tieSelection_project_energy h.1 T.fits T.take T.take_le (B - Y)
    (T.equality_above_residual_zero h ha Y hY heq)

theorem TieStructure.equality_exists_small_residual {m l : ℕ}
    {B : Matrix (Fin m) (Fin l) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {sigma : Fin (min m l) → ℝ} {V : Matrix (Fin l) (Fin l) ℝ}
    (h : ValidSVD B U sigma V) {a : Fin (min m l)} (T : TieStructure sigma a)
    (ha : 0 < sigma a) (Y : Matrix (Fin m) (Fin l) ℝ)
    (hY : Matrix.rank Y ≤ a.val + 1)
    (heq : matrixEnergy (B - Y) = tailEnergy sigma (a.val + 1)) :
    ∃ j : Fin T.tied, matrixEnergy (projectMatrix
      (directionSubspace U (tieSelection T.above T.tied T.fits T.take j)) (B - Y)) ≤
        ((T.take : ℝ) / T.tied) * matrixEnergy (B - Y) :=
  exists_tieSelection_project_energy_le h.1 T.fits T.take T.take_le (B - Y)
    (T.equality_above_residual_zero h ha Y hY heq)

#assert_trust kernel TieStructure.first_error
#assert_trust kernel TieStructure.frame_rank
#assert_trust kernel TieStructure.equality_average_residual
#assert_trust kernel TieStructure.equality_exists_small_residual
#print axioms TieStructure.equality_exists_small_residual
end NLA.Proofs.TR04.SVD
