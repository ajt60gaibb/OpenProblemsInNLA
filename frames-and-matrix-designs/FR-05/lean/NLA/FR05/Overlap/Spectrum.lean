import NLA.FR05.Gaussian.GaussianQuadraticIntegral
import NLA.FR05.Likelihood.KernelMatrixAlgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Spectral geometry and latent factors of two-frame overlaps

The sections develop `Spectrum`, `OverlapLatentFactors`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section Spectrum

/-!
## Spectral geometry of two-frame overlaps

Squared singular values control the determinant and the open operator-norm ball.
Positive square roots of the left and right Gram matrices give the block
factorisation used by the Gaussian overlap coupling. No reference-law parameters
or paper-specific scalar estimates enter this module.
-/

open Complex Real Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

section SingularValues

/-- The eigenvalues of the right Gram matrix of an overlap. -/
def overlapSquaredSingularValues (K : SourceOverlapMatrix) : Fin 2 → ℝ :=
  (isHermitian_conjTranspose_mul_self K).eigenvalues

/-- Squared singular values are nonnegative. -/
theorem overlapSquaredSingularValues_nonneg (K : SourceOverlapMatrix) (i : Fin 2) :
    0 ≤ overlapSquaredSingularValues K i :=
  (posSemidef_conjTranspose_mul_self K).eigenvalues_nonneg i

/-- Every squared singular value is bounded by the squared operator norm. -/
theorem overlapSquaredSingularValues_le (K : SourceOverlapMatrix) (i : Fin 2) :
    overlapSquaredSingularValues K i ≤ overlapOperatorNorm K ^ 2 := by
  have hm : (overlapSquaredSingularValues K i : ℂ) ∈ spectrum ℂ (Kᴴ * K) := by
    rw [(isHermitian_conjTranspose_mul_self K).spectrum_eq_image_range]
    exact ⟨_, ⟨i, rfl⟩, rfl⟩
  have h := spectrum.norm_le_norm_of_mem hm
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (overlapSquaredSingularValues_nonneg K i)] at h
  simpa only [← Matrix.star_eq_conjTranspose, CStarRing.norm_star_mul_self,
    overlapOperatorNorm, Matrix.cstar_norm_def, pow_two] using h

/-- The squared singular values sum to the squared Frobenius norm. -/
theorem overlapSquaredSingularValues_sum (K : SourceOverlapMatrix) :
    ∑ i, overlapSquaredSingularValues K i = overlapFrobeniusSq K := by
  have h := congrArg Complex.re (isHermitian_conjTranspose_mul_self K).trace_eq_sum_eigenvalues
  change (Kᴴ * K).trace.re = (∑ i, (overlapSquaredSingularValues K i : ℂ)).re at h
  simp only [Complex.re_sum, Complex.ofReal_re] at h
  rw [← h]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    overlapFrobeniusSq, Fin.sum_univ_two, Complex.normSq_apply, Complex.mul_re]
  ring

/-- The determinant of a real scalar perturbation of a Hermitian matrix. -/
theorem det_one_sub_smul_eigenvalues {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (q : ℝ) :
    det (1 - (q : ℂ) • A) = ((∏ i, (1 - q * hA.eigenvalues i) : ℝ) : ℂ) := by
  simpa [sub_eq_add_neg, neg_smul] using hA.det_one_add_smul_eq_prod (-q)

/-- Express the overlap determinant through squared singular values. -/
theorem overlapDeterminant_singularValues (K : SourceOverlapMatrix) :
    overlapDeterminant K = ∏ i, (1 - overlapSquaredSingularValues K i) := by
  unfold overlapDeterminant
  rw [det_one_sub_mul_comm]
  have h := det_one_sub_smul_eigenvalues (isHermitian_conjTranspose_mul_self K) 1
  simpa [overlapSquaredSingularValues] using congrArg Complex.re h

/-- Express a real-scaled overlap determinant through the original singular values. -/
theorem overlapDeterminant_smul_singularValues (K : SourceOverlapMatrix) (b : ℝ) :
    overlapDeterminant ((b : ℂ) • K) =
      ∏ i, (1 - b^2 * overlapSquaredSingularValues K i) := by
  unfold overlapDeterminant
  rw [det_one_sub_mul_comm]
  have he : ((b : ℂ) • K)ᴴ * ((b : ℂ) • K) = ((b^2 : ℝ) : ℂ) • (Kᴴ * K) := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, smul_eq_mul,
      pow_two]
    ring
  rw [he, det_one_sub_smul_eigenvalues (isHermitian_conjTranspose_mul_self K)]
  rfl

end SingularValues

section OperatorBall

/-- The squared operator norm is the maximum squared singular value. -/
theorem overlapOperatorNorm_sq_eq_spectrum_norm (K : SourceOverlapMatrix) :
    overlapOperatorNorm K ^ 2 = ‖fun i ↦ (overlapSquaredSingularValues K i : ℂ)‖ := by
  have hA := isHermitian_conjTranspose_mul_self K
  calc
    _ = ‖Kᴴ * K‖ := by
      simp [← Matrix.star_eq_conjTranspose, CStarRing.norm_star_mul_self,
        overlapOperatorNorm, Matrix.cstar_norm_def, pow_two]
    _ = ‖diagonal (fun i ↦ (overlapSquaredSingularValues K i : ℂ))‖ := by
      rw [hA.spectral_theorem]
      simp only [Unitary.conjStarAlgAut_apply]
      rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
      rfl
    _ = _ := Matrix.l2_opNorm_diagonal _

/-- For two-dimensional overlaps, trace and determinant characterise the open unit ball. -/
theorem overlapOperatorNorm_lt_one_iff (K : SourceOverlapMatrix) :
    overlapOperatorNorm K < 1 ↔ overlapFrobeniusSq K < 2 ∧ 0 < overlapDeterminant K := by
  constructor
  · intro h
    refine ⟨?_, overlapDeterminant_pos h⟩
    have hF := overlapFrobeniusSq_le K
    nlinarith [overlapOperatorNorm_nonneg K]
  · rintro ⟨hF, hd⟩
    have hs := overlapSquaredSingularValues_sum K
    rw [Fin.sum_univ_two] at hs
    rw [overlapDeterminant_singularValues, Fin.prod_univ_two] at hd
    have heig : ∀ i, overlapSquaredSingularValues K i < 1 := by
      intro i
      rcases (mul_pos_iff.mp hd) with h | h
      · fin_cases i
        · exact sub_pos.mp h.1
        · exact sub_pos.mp h.2
      · linarith [h.1, h.2]
    have hn : ‖fun i ↦ (overlapSquaredSingularValues K i : ℂ)‖ < 1 := by
      apply (pi_norm_lt_iff zero_lt_one).mpr
      intro i
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (overlapSquaredSingularValues_nonneg K i)] using heig i
    rw [← overlapOperatorNorm_sq_eq_spectrum_norm] at hn
    nlinarith [overlapOperatorNorm_nonneg K]

end OperatorBall

section SquareRoots

/-- The positive square root of the left Gram matrix. -/
def overlapLeftRoot (K : SourceOverlapMatrix) : SourceOverlapMatrix := CFC.sqrt (K * Kᴴ)
/-- The positive square root of the right Gram matrix. -/
def overlapRightRoot (K : SourceOverlapMatrix) : SourceOverlapMatrix := CFC.sqrt (Kᴴ * K)

/-- The left Gram square root is positive semidefinite. -/
theorem overlapLeftRoot_nonneg (K : SourceOverlapMatrix) : 0 ≤ overlapLeftRoot K :=
  CFC.sqrt_nonneg _
/-- The right Gram square root is positive semidefinite. -/
theorem overlapRightRoot_nonneg (K : SourceOverlapMatrix) : 0 ≤ overlapRightRoot K :=
  CFC.sqrt_nonneg _

/-- The left Gram square root is Hermitian. -/
theorem overlapLeftRoot_hermitian (K : SourceOverlapMatrix) :
    (overlapLeftRoot K)ᴴ = overlapLeftRoot K := (overlapLeftRoot_nonneg K).star_eq

/-- The right Gram square root is Hermitian. -/
theorem overlapRightRoot_hermitian (K : SourceOverlapMatrix) :
    (overlapRightRoot K)ᴴ = overlapRightRoot K := (overlapRightRoot_nonneg K).star_eq

/-- Squaring the left Gram square root recovers the left Gram matrix. -/
theorem overlapLeftRoot_sq (K : SourceOverlapMatrix) :
    overlapLeftRoot K * overlapLeftRoot K = K * Kᴴ :=
  CFC.sqrt_mul_sqrt_self _ (posSemidef_self_mul_conjTranspose K).nonneg

/-- Squaring the right Gram square root recovers the right Gram matrix. -/
theorem overlapRightRoot_sq (K : SourceOverlapMatrix) :
    overlapRightRoot K * overlapRightRoot K = Kᴴ * K :=
  CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self K).nonneg

/-- The left Gram square root has the same operator norm as the overlap. -/
theorem overlapLeftRoot_norm (K : SourceOverlapMatrix) :
    overlapOperatorNorm (overlapLeftRoot K) = overlapOperatorNorm K := by
  change ‖overlapLeftRoot K‖ = ‖K‖
  rw [overlapLeftRoot, CFC.norm_sqrt _ (posSemidef_self_mul_conjTranspose K).nonneg,
    ← Matrix.star_eq_conjTranspose, CStarRing.norm_self_mul_star,
    Real.sqrt_mul_self (norm_nonneg K)]

/-- The right Gram square root has the same operator norm as the overlap. -/
theorem overlapRightRoot_norm (K : SourceOverlapMatrix) :
    overlapOperatorNorm (overlapRightRoot K) = overlapOperatorNorm K := by
  change ‖overlapRightRoot K‖ = ‖K‖
  rw [overlapRightRoot, CFC.norm_sqrt _ (posSemidef_conjTranspose_mul_self K).nonneg,
    ← Matrix.star_eq_conjTranspose, CStarRing.norm_star_mul_self,
    Real.sqrt_mul_self (norm_nonneg K)]

/-- Passing to the left Gram square root preserves the overlap determinant. -/
theorem overlapLeftRoot_determinant (K : SourceOverlapMatrix) :
    overlapDeterminant (overlapLeftRoot K) = overlapDeterminant K := by
  rw [overlapDeterminant, overlapLeftRoot_hermitian, overlapLeftRoot_sq]
  rfl

/-- Passing to the right Gram square root preserves the overlap determinant. -/
theorem overlapRightRoot_determinant (K : SourceOverlapMatrix) :
    overlapDeterminant (overlapRightRoot K) = overlapDeterminant K := by
  rw [overlapDeterminant, overlapRightRoot_hermitian, overlapRightRoot_sq,
    det_one_sub_mul_comm]
  rfl

/-- The left Gram square root of a strict contraction is bounded by the identity. -/
theorem overlapLeftRoot_le_one {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    overlapLeftRoot K ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (overlapLeftRoot_nonneg K)).mp
    (show overlapOperatorNorm (overlapLeftRoot K) ≤ 1 by rw [overlapLeftRoot_norm]; exact hK.le)

/-- The right Gram square root of a strict contraction is bounded by the identity. -/
theorem overlapRightRoot_le_one {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    overlapRightRoot K ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (overlapRightRoot_nonneg K)).mp
    (show overlapOperatorNorm (overlapRightRoot K) ≤ 1 by rw [overlapRightRoot_norm]; exact hK.le)

/-- The Hermitian off-diagonal block matrix associated with an overlap. -/
def overlapHermitianBlock (K : SourceOverlapMatrix) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := fromBlocks 0 K Kᴴ 0

/-- The diagonal block matrix of the two positive Gram square roots. -/
def overlapRootBlock (K : SourceOverlapMatrix) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  fromBlocks (overlapLeftRoot K) 0 0 (overlapRightRoot K)

/-- The diagonal block of Gram square roots is positive semidefinite. -/
theorem overlapRootBlock_nonneg (K : SourceOverlapMatrix) : 0 ≤ overlapRootBlock K := by
  apply Matrix.PosSemidef.nonneg
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (overlapRootBlock K)ᴴ = _
    simp [overlapRootBlock, fromBlocks_conjTranspose, overlapLeftRoot_hermitian,
      overlapRightRoot_hermitian]
  · intro z
    simpa [overlapRootBlock, Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
      using add_nonneg
        ((overlapLeftRoot_nonneg K).posSemidef.dotProduct_mulVec_nonneg (z ∘ Sum.inl))
        ((overlapRightRoot_nonneg K).posSemidef.dotProduct_mulVec_nonneg (z ∘ Sum.inr))

/-- The off-diagonal overlap block is self-adjoint. -/
theorem overlapHermitianBlock_selfAdjoint (K : SourceOverlapMatrix) :
    IsSelfAdjoint (overlapHermitianBlock K) := by
  change (overlapHermitianBlock K)ᴴ = _
  simp [overlapHermitianBlock, fromBlocks_conjTranspose]

/-- The absolute value of the overlap block is the block of Gram square roots. -/
theorem overlapHermitianBlock_abs (K : SourceOverlapMatrix) :
    CFC.abs (overlapHermitianBlock K) = overlapRootBlock K := by
  rw [CFC.abs, (overlapHermitianBlock_selfAdjoint K).star_eq]
  have hn := star_mul_self_nonneg (overlapHermitianBlock K)
  rw [(overlapHermitianBlock_selfAdjoint K).star_eq] at hn
  apply (CFC.sqrt_eq_iff _ _ hn (overlapRootBlock_nonneg K)).mpr
  simp [overlapRootBlock, overlapHermitianBlock, fromBlocks_multiply,
    overlapLeftRoot_sq, overlapRightRoot_sq]

/-- The block covariance used for the latent Gaussian coupling is positive semidefinite. -/
theorem overlapLatentBlock_nonneg (K : SourceOverlapMatrix) :
    0 ≤ fromBlocks (overlapLeftRoot K) K Kᴴ (overlapRightRoot K) := by
  have h : 0 ≤ CFC.abs (overlapHermitianBlock K) + overlapHermitianBlock K := by
    rw [CFC.abs_add_self _ (overlapHermitianBlock_selfAdjoint K)]
    exact smul_nonneg (by norm_num : (0 : ℕ) ≤ 2) (CFC.posPart_nonneg _)
  rw [overlapHermitianBlock_abs] at h
  convert h using 1
  ext i j
  cases i <;> cases j <;> simp [overlapRootBlock, overlapHermitianBlock]

end SquareRoots

end Spectrum

section OverlapLatentFactors

open Complex Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Realise an overlap and its complementary Gram matrices by common latent factors. -/
theorem exists_overlap_latent_factors {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) :
    ∃ (L R : Matrix (Fin 4) (Fin 2) ℂ) (N P : SourceOverlapMatrix),
      Lᴴ * L = overlapLeftRoot K ∧ Rᴴ * R = overlapRightRoot K ∧
      Lᴴ * R = K ∧ Lᴴ * L + Nᴴ * N = 1 ∧ Rᴴ * R + Pᴴ * P = 1 := by
  let G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
    fromBlocks (overlapLeftRoot K) K Kᴴ (overlapRightRoot K)
  have hG : 0 ≤ G := overlapLatentBlock_nonneg K
  let C : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) ℂ :=
    (CFC.sqrt G).submatrix (finSumFinEquiv (m := 2) (n := 2)).symm id
  have hC : Cᴴ * C = G := by
    dsimp [C]
    rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_id_id]
    rw [← Matrix.star_eq_conjTranspose, (CFC.sqrt_nonneg G).star_eq, CFC.sqrt_mul_sqrt_self G hG]
  let L := C.submatrix id Sum.inl
  let R := C.submatrix id Sum.inr
  have hgram (i j : Fin 2 → Fin 2 ⊕ Fin 2) :
      (C.submatrix id i)ᴴ * C.submatrix id j = G.submatrix i j := by
    rw [conjTranspose_submatrix]
    have h := Matrix.submatrix_mul_equiv Cᴴ C i (Equiv.refl (Fin 4)) j
    simpa only [Equiv.coe_refl, hC] using h
  have hL : Lᴴ * L = overlapLeftRoot K := hgram Sum.inl Sum.inl
  have hR : Rᴴ * R = overlapRightRoot K := hgram Sum.inr Sum.inr
  have hLR : Lᴴ * R = K := hgram Sum.inl Sum.inr
  let N := CFC.sqrt (1 - overlapLeftRoot K)
  let P := CFC.sqrt (1 - overlapRightRoot K)
  have hN : Nᴴ * N = 1 - overlapLeftRoot K := by
    rw [show Nᴴ = N from (CFC.sqrt_nonneg _).star_eq]
    exact CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr (overlapLeftRoot_le_one hK))
  have hP : Pᴴ * P = 1 - overlapRightRoot K := by
    rw [show Pᴴ = P from (CFC.sqrt_nonneg _).star_eq]
    exact CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr (overlapRightRoot_le_one hK))
  exact ⟨L, R, N, P, hL, hR, hLR, by rw [hL, hN, add_sub_cancel],
    by rw [hR, hP, add_sub_cancel]⟩

end OverlapLatentFactors

end NLA.FR05
