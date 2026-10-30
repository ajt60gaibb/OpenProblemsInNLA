import NLA.Proofs.TR04.TensorCompressionMerge
import NLA.Proofs.TR04.SVDFrameProjection

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Matrix

namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine

abbrev suffixSize (ns : List ℕ) := Fintype.card (Index ns)

def suffixEquiv (ns : List ℕ) : Fin (suffixSize ns) ≃ Index ns :=
  (Fintype.equivFin (Index ns)).symm

/-- A full finite real matrix containing every actual first-unfolding entry. -/
def denseFirst {m : ℕ} {ns : List ℕ} (A : Tensor (m :: ns)) :
    Matrix (Fin m) (Fin (suffixSize ns)) ℝ :=
  (firstMatrix A).submatrix (Equiv.refl _) (suffixEquiv ns)

theorem rank_denseFirst {m : ℕ} {ns : List ℕ} (A : Tensor (m :: ns)) :
    Matrix.rank (denseFirst A) = Matrix.rank (firstMatrix A) :=
  Matrix.rank_submatrix _ (Equiv.refl _) (suffixEquiv ns)

theorem energy_denseFirst {m : ℕ} {ns : List ℕ} (A : Tensor (m :: ns)) :
    SVD.matrixEnergy (denseFirst A) = energy (m :: ns) A := by
  rw [energy_firstMatrix]
  unfold SVD.matrixEnergy
  apply Finset.sum_congr rfl
  intro i _
  exact (suffixEquiv ns).sum_comp (fun x => (firstMatrix A i x)^2)

@[simp] theorem denseFirst_sub {m : ℕ} {ns : List ℕ} (A B : Tensor (m :: ns)) :
    denseFirst (A - B) = denseFirst A - denseFirst B := rfl

def cappedRank (m l r : ℕ) : ℕ := min r (min m l)

def prefixFrame {m l : ℕ} (U : Matrix (Fin m) (Fin m) ℝ) (r : ℕ) :
    Matrix (Fin m) (Fin (cappedRank m l r)) ℝ :=
  U.submatrix id (Fin.castLE ((Nat.min_le_right r (min m l)).trans (Nat.min_le_left m l)))

theorem prefixFrame_orthonormal {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V) (r : ℕ) :
    SVD.OrthonormalColumns (prefixFrame (l := l) U r) :=
  SVD.orthonormalColumns_submatrix h.1 _ (fun _ _ h => Fin.ext (congrArg (fun i : Fin m => i.val) h))

theorem denseFirst_actFirst {m k : ℕ} {ns : List ℕ}
    (M : Matrix (Fin k) (Fin m) ℝ) (A : Tensor (m :: ns)) :
    denseFirst (actFirst M A) = M * denseFirst A := rfl

/-- Actual tensor contraction/lifting through the SVD's capped prefix frame
is exactly that tuple's truncated reconstruction. -/
theorem denseFirst_prefix_projection {m : ℕ} {ns : List ℕ} {A : Tensor (m :: ns)}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m (suffixSize ns)) → ℝ}
    {V : Matrix (Fin (suffixSize ns)) (Fin (suffixSize ns)) ℝ}
    (h : ValidSVD (denseFirst A) U sigma V) (r : ℕ) :
    denseFirst (lift (prefixFrame (l := suffixSize ns) U r)
      (contract (prefixFrame (l := suffixSize ns) U r) A)) = SVD.truncate U sigma V r := by
  change (prefixFrame (l := suffixSize ns) U r) *
    ((prefixFrame (l := suffixSize ns) U r).transpose * denseFirst A) = _
  exact SVD.validSVD_prefix_projection h r

/-- Every legal SVD response supplies the first-step best-rank error bound. -/
theorem error_prefix_projection_le {m : ℕ} {ns : List ℕ} {A : Tensor (m :: ns)}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m (suffixSize ns)) → ℝ}
    {V : Matrix (Fin (suffixSize ns)) (Fin (suffixSize ns)) ℝ}
    (h : ValidSVD (denseFirst A) U sigma V) (r : ℕ) (Y : Tensor (m :: ns))
    (hY : Matrix.rank (firstMatrix Y) ≤ r) :
    error (m :: ns) A (lift (prefixFrame (l := suffixSize ns) U r)
      (contract (prefixFrame (l := suffixSize ns) U r) A)) ≤ error (m :: ns) A Y := by
  have hbest := (SVD.validSVD_truncate_best h r).2 (denseFirst Y) (by rwa [rank_denseFirst])
  unfold error
  rw [← energy_denseFirst, denseFirst_sub, denseFirst_prefix_projection h r]
  simpa only [← denseFirst_sub, energy_denseFirst] using hbest

#assert_trust kernel rank_denseFirst
#assert_trust kernel energy_denseFirst
#assert_trust kernel prefixFrame_orthonormal
#assert_trust kernel denseFirst_prefix_projection
#assert_trust kernel error_prefix_projection_le
#print axioms error_prefix_projection_le
end NLA.Proofs.TR04.TensorFormat
