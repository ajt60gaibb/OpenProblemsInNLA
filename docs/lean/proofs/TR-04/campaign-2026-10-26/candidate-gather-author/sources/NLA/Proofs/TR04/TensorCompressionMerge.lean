import NLA.Proofs.TR04.TensorCompressionRanks
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Matrix

namespace NLA.Proofs.TR04.TensorFormat

/-- Reindex every entry along a specified genuine index bijection. -/
def reindexLinearEquiv {ns ms : List ℕ} (e : Index ms ≃ Index ns) :
    Tensor ns ≃ₗ[ℝ] Tensor ms where
  toFun A x := A (e x)
  invFun A x := A (e.symm x)
  left_inv A := by funext x; simp
  right_inv A := by funext x; simp
  map_add' A B := rfl
  map_smul' c A := rfl

theorem energy_reindex {ns ms : List ℕ} (e : Index ms ≃ Index ns) (A : Tensor ns) :
    energy ms (reindexLinearEquiv e A) = energy ns A :=
  e.sum_comp (fun x => (A x)^2)

theorem error_reindex {ns ms : List ℕ} (e : Index ms ≃ Index ns) (A B : Tensor ns) :
    error ms (reindexLinearEquiv e A) (reindexLinearEquiv e B) = error ns A B :=
  e.sum_comp (fun x => (A x - B x)^2)

/-- Merge two leading coordinates by their exact finite product bijection. -/
def mergeIndexEquiv (k m : ℕ) (ns : List ℕ) :
    Index ((k * m) :: ns) ≃ Index (k :: m :: ns) :=
  (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl (Index ns))).trans
    (Equiv.prodAssoc (Fin k) (Fin m) (Index ns))

def merge (k m : ℕ) (ns : List ℕ) :
    Tensor (k :: m :: ns) ≃ₗ[ℝ] Tensor ((k * m) :: ns) :=
  reindexLinearEquiv (mergeIndexEquiv k m ns)

@[simp] theorem merge_apply (k m : ℕ) (ns : List ℕ)
    (A : Tensor (k :: m :: ns)) (i : Fin k) (j : Fin m) (x : Index ns) :
    merge k m ns A (finProdFinEquiv (i, j), x) = A (i, j, x) := by
  change A ((finProdFinEquiv.symm (finProdFinEquiv (i, j))).1,
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2, x) = A (i, j, x)
  rw [Equiv.symm_apply_apply]

theorem energy_merge (k m : ℕ) (ns : List ℕ) (A : Tensor (k :: m :: ns)) :
    energy ((k * m) :: ns) (merge k m ns A) = energy (k :: m :: ns) A :=
  energy_reindex (mergeIndexEquiv k m ns) A

theorem error_merge (k m : ℕ) (ns : List ℕ) (A B : Tensor (k :: m :: ns)) :
    error ((k * m) :: ns) (merge k m ns A) (merge k m ns B) =
      error (k :: m :: ns) A B :=
  error_reindex (mergeIndexEquiv k m ns) A B

theorem unfold_merge (k m : ℕ) (ns : List ℕ) (A : Tensor (k :: m :: ns)) (j : ℕ) :
    unfold ((k * m) :: ns) (merge k m ns A) (j + 1) =
      (unfold (k :: m :: ns) A (j + 2)).submatrix
        (show Index (((k * m) :: ns).take (j + 1)) ≃
          Index ((k :: m :: ns).take (j + 2)) from
            mergeIndexEquiv k m (ns.take j)) (Equiv.refl _) := by
  ext x y
  rfl

theorem rank_unfold_merge (k m : ℕ) (ns : List ℕ) (A : Tensor (k :: m :: ns)) (j : ℕ) :
    Matrix.rank (unfold ((k * m) :: ns) (merge k m ns A) (j + 1)) =
      Matrix.rank (unfold (k :: m :: ns) A (j + 2)) := by
  rw [unfold_merge]
  exact Matrix.rank_submatrix _ (mergeIndexEquiv k m (ns.take j)) (Equiv.refl _)

/-- The full projected-comparator norm is exactly the compressed error. -/
theorem projected_error_eq {m k : ℕ} {ns : List ℕ}
    {U : Matrix (Fin m) (Fin k) ℝ} (hU : SVD.OrthonormalColumns U)
    (A B : Tensor (m :: ns)) :
    energy (m :: ns) (lift U (contract U (A - B))) =
      error (k :: ns) (contract U A) (contract U B) := by
  rw [energy_lift hU]
  change energy (k :: ns) (actFirst U.transpose (A - B)) =
    energy (k :: ns) (actFirst U.transpose A - actFirst U.transpose B)
  rw [actFirst_sub]

#assert_trust kernel reindexLinearEquiv
#assert_trust kernel energy_reindex
#assert_trust kernel error_reindex
#assert_trust kernel mergeIndexEquiv
#assert_trust kernel energy_merge
#assert_trust kernel error_merge
#assert_trust kernel unfold_merge
#assert_trust kernel rank_unfold_merge
#assert_trust kernel projected_error_eq
#print axioms rank_unfold_merge
end NLA.Proofs.TR04.TensorFormat
