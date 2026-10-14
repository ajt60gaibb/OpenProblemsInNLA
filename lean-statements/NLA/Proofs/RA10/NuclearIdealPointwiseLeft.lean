import NLA.Proofs.RA10.NuclearIdealGramIndex
import NLA.Proofs.RA10.NuclearIdealGramOrder

/-! RA-10: exact coefficient-one bound for every zero-based singular value
of a left matrix product. The summed nuclear ideal and Eq. (14) remain
separate gates. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace NLA.Proofs.RA10

private theorem orderedPSD_smul {n : ℕ}
    {G : Matrix (Fin n) (Fin n) ℝ}
    {g : Fin n → ℝ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hG : NLA.Statements.RA10.OrderedPSDSpectralDecomposition G g Q)
    (s : ℝ) (hs : 0 ≤ s) :
    NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (s • G) (fun i => s * g i) Q := by
  refine ⟨?_, ?_, hG.2.2.1, ?_⟩
  · intro i
    exact mul_nonneg hs (hG.1 i)
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (hG.2.1 hij) hs
  · rw [hG.2.2.2]
    ext i j
    simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring

private theorem gram_possemidef {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.PosSemidef (Y.transpose * Y) := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self Y

theorem singularValues_left_mul_le {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (Matrix.toEuclideanLin (X * Y)).singularValues i.val ≤
      ‖X‖ * (Matrix.toEuclideanLin Y).singularValues i.val := by
  let G := Y.transpose * Y
  let H := (X * Y).transpose * (X * Y)
  obtain ⟨g, QG, hG⟩ :=
    mathlibPosSemidef_exists_orderedPSD (gram_possemidef Y)
  obtain ⟨h, QH, hH⟩ :=
    mathlibPosSemidef_exists_orderedPSD (gram_possemidef (X * Y))
  let s : ℝ := ‖X‖ ^ 2
  have hs : 0 ≤ s := sq_nonneg _
  have hScaled := orderedPSD_smul hG s hs
  have hOrder : NLA.Statements.RA10.PositiveSemidefinite (s • G - H) :=
    nuclearIdeal_left_gram_order X Y
  have heig := orderedPSDSpectral_eigenvalues_le_of_psd_sub
    hScaled hH hOrder i
  have hY := orderedPSD_gram_eigenvalue_eq_singular_sq Y hG i
  have hXY := orderedPSD_gram_eigenvalue_eq_singular_sq (X * Y) hH i
  rw [hY, hXY] at heig
  have hsq :
      (Matrix.toEuclideanLin (X * Y)).singularValues i.val ^ 2 ≤
        (‖X‖ * (Matrix.toEuclideanLin Y).singularValues i.val) ^ 2 := by
    simpa [s, mul_pow] using heig
  exact le_of_sq_le_sq hsq
    (mul_nonneg (norm_nonneg _) ((Matrix.toEuclideanLin Y).singularValues_nonneg i.val))

#assert_trust kernel orderedPSD_smul
#assert_trust kernel gram_possemidef
#assert_trust kernel singularValues_left_mul_le
#print axioms singularValues_left_mul_le

end NLA.Proofs.RA10
