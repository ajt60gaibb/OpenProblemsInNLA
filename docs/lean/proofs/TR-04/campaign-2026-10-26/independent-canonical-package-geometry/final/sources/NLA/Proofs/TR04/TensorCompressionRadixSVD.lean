import NLA.Proofs.TR04.TensorCompressionRadix

/-! Exact right-column transport between explicit mixed-radix data layout
and the frozen mathematical suffix enumeration. U and sigma are unchanged. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Matrix

namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine

/-- Every real SVD response transports through a right-column permutation. -/
theorem validSVD_reindex_columns {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (e : Fin l ≃ Fin l) :
    ValidSVD (B.submatrix id e) U sigma (V.submatrix e id) := by
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2.1, ?_⟩
  · intro i j
    calc
      (∑ a, (V.submatrix e id) a i * (V.submatrix e id) a j) =
          ∑ a, V a i * V a j := e.sum_comp (fun a => V a i * V a j)
      _ = if i = j then 1 else 0 := h.2.1 i j
  · intro i j
    exact h.2.2.2.2 i (e j)

def radixDenseFirst {m : ℕ} {ns : List ℕ} (A : Tensor (m :: ns)) :
    Matrix (Fin m) (Fin (suffixSize ns)) ℝ :=
  (firstMatrix A).submatrix (Equiv.refl _) (radixSuffixEquiv ns)

def suffixPermutation (ns : List ℕ) : Fin (suffixSize ns) ≃ Fin (suffixSize ns) :=
  (radixSuffixEquiv ns).trans (suffixEquiv ns).symm

theorem radixDenseFirst_eq_reindex {m : ℕ} {ns : List ℕ} (A : Tensor (m :: ns)) :
    radixDenseFirst A = (denseFirst A).submatrix id (suffixPermutation ns) := by
  ext i j
  change A (i, radixSuffixEquiv ns j) =
    A (i, suffixEquiv ns ((suffixEquiv ns).symm (radixSuffixEquiv ns j)))
  rw [Equiv.apply_symm_apply]

theorem denseFirst_eq_reindex_radix {m : ℕ} {ns : List ℕ} (A : Tensor (m :: ns)) :
    denseFirst A = (radixDenseFirst A).submatrix id (suffixPermutation ns).symm := by
  ext i j
  change A (i, suffixEquiv ns j) =
    A (i, radixSuffixEquiv ns ((radixSuffixEquiv ns).symm (suffixEquiv ns j)))
  rw [Equiv.apply_symm_apply]

theorem rank_radixDenseFirst {m : ℕ} {ns : List ℕ} (A : Tensor (m :: ns)) :
    Matrix.rank (radixDenseFirst A) = Matrix.rank (firstMatrix A) :=
  Matrix.rank_submatrix _ (Equiv.refl _) (radixSuffixEquiv ns)

theorem energy_radixDenseFirst {m : ℕ} {ns : List ℕ} (A : Tensor (m :: ns)) :
    SVD.matrixEnergy (radixDenseFirst A) = energy (m :: ns) A := by
  rw [energy_firstMatrix]
  unfold SVD.matrixEnergy
  apply Finset.sum_congr rfl
  intro i _
  exact (radixSuffixEquiv ns).sum_comp (fun x => (firstMatrix A i x)^2)

/-- A literal legal response of the machine's explicit dense layout supplies
exactly the frozen mathematical response with the same U and sigma. -/
theorem radix_validSVD_to_denseFirst {m : ℕ} {ns : List ℕ} {A : Tensor (m :: ns)}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m (suffixSize ns)) → ℝ}
    {V : Matrix (Fin (suffixSize ns)) (Fin (suffixSize ns)) ℝ}
    (h : ValidSVD (radixDenseFirst A) U sigma V) :
    ValidSVD (denseFirst A) U sigma (V.submatrix (suffixPermutation ns).symm id) := by
  rw [denseFirst_eq_reindex_radix]
  exact validSVD_reindex_columns h (suffixPermutation ns).symm

/-- The concrete recursive relation accepts every explicit-layout SVD reply,
with identical contraction/lifting and without computing a choice enumeration. -/
theorem completion_step_radix {m n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    {A : Tensor (m :: n :: ns)} {U : Matrix (Fin m) (Fin m) ℝ}
    {sigma : Fin (min m (suffixSize (n :: ns))) → ℝ}
    {V : Matrix (Fin (suffixSize (n :: ns))) (Fin (suffixSize (n :: ns))) ℝ}
    (hSVD : ValidSVD (radixDenseFirst A) U sigma V)
    {Z : Tensor ((stepRank m (n :: ns) r * n) :: ns)}
    (hchild : Completion ((stepRank m (n :: ns) r * n) :: ns) (fun j => r (j + 1))
      (stepInput r U A) Z) :
    Completion (m :: n :: ns) r A (stepOutput r U Z) :=
  Completion.step (radix_validSVD_to_denseFirst hSVD) hchild

#assert_trust kernel validSVD_reindex_columns
#assert_trust kernel radixDenseFirst_eq_reindex
#assert_trust kernel denseFirst_eq_reindex_radix
#assert_trust kernel rank_radixDenseFirst
#assert_trust kernel energy_radixDenseFirst
#assert_trust kernel radix_validSVD_to_denseFirst
#assert_trust kernel completion_step_radix
#print axioms completion_step_radix
end NLA.Proofs.TR04.TensorFormat
