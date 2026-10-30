import NLA.Proofs.RE06.GaussianFlatten
import NLA.Proofs.RE06.GaussianOrthogonal
import NLA.Proofs.RE06.GaussianWarmStartTails
import NLA.Proofs.RE06.PseudoInverseCore

/-! Exact fixed-residual SVD energy transport for the actual unscaled
Gaussian block. No SVD measurability or full-rank hypothesis is needed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Matrix
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

/-- Actual singular values, reindexed from the literally square SVD result. -/
def residualSingularValue {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  (exactSVD B).sigma ⟨i.val, by simpa only [Nat.min_self] using i.isLt⟩

theorem residualSingularValue_nonneg {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    0 ≤ residualSingularValue B i :=
  (svd_total n n B).2.2.1 _

theorem residualSingularValue_antitone {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    Antitone (residualSingularValue B) := by
  intro i j hij
  exact (svd_total n n B).2.2.2.1 _ _ hij

/-- Literal square reconstruction with the actual chosen SVD factors. -/
theorem residual_svd_reconstruction {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    B = (exactSVD B).U * Matrix.diagonal (residualSingularValue B) * (exactSVD B).V.transpose := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.mul_diagonal, Matrix.transpose_apply]
  have h := (svd_total n n B).2.2.2.2 i j
  simpa only [Nat.min_self, residualSingularValue] using h

/-- The actual right singular-vector coordinate map. -/
def residualGaussianRotation {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    GaussianEuclid n ≃ₗᵢ[ℝ] GaussianEuclid n :=
  orthogonalEuclidean n (exactSVD B).V.transpose (by
    simpa only [Matrix.transpose_transpose] using Pseudo.svd_V_cogram B)

def residualGaussianCoordinates {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (q offset : ℕ) (ω : ℕ → ℝ) : Fin n × Fin q → ℝ :=
  fun p => ((exactSVD B).V.transpose * gaussianBlock n q offset ω) p.1 p.2

/-- Fixed orthogonal SVD coordinates have their actual full scalar product law. -/
theorem residualGaussianCoordinates_hasLaw {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (q offset : ℕ) :
    HasLaw (residualGaussianCoordinates B q offset)
      (Measure.pi (fun _ : Fin n × Fin q => gaussianReal 0 1)) GaussianLaw := by
  have h := gaussianBlock_rotated_entries_hasLaw n q offset
    (fun _ => residualGaussianRotation B)
  convert h using 1
  funext ω p
  have he := congrFun (orthogonalEuclidean_apply n (exactSVD B).V.transpose
    (by simpa only [Matrix.transpose_transpose] using Pseudo.svd_V_cogram B)
    (WithLp.toLp 2 (fun i : Fin n => gaussianBlock n q offset ω i p.2))) p.1
  exact he.symm

/-- Pointwise energy identity, including zero singular values and zero dimensions. -/
theorem residualGaussian_energy {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (q offset : ℕ) (ω : ℕ → ℝ) :
    squaredFrobenius (B * gaussianBlock n q offset ω) 0 =
      gaussianQuadratic (fun p : Fin n × Fin q => (residualSingularValue B p.1) ^ 2)
        (residualGaussianCoordinates B q offset ω) := by
  let G := gaussianBlock n q offset ω
  have he : B * G = (exactSVD B).U *
      (Matrix.diagonal (residualSingularValue B) * ((exactSVD B).V.transpose * G)) := by
    conv_lhs => rw [residual_svd_reconstruction B]
    simp only [Matrix.mul_assoc]
  rw [he, squaredFrobenius_left_isometry _ (Pseudo.svd_U_gram B)]
  simp only [squaredFrobenius, Matrix.zero_apply, sub_zero, Matrix.diagonal_mul,
    gaussianQuadratic, Fintype.sum_prod_type, residualGaussianCoordinates]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

#assert_trust kernel residualSingularValue_nonneg
#assert_trust kernel residualSingularValue_antitone
#assert_trust kernel residual_svd_reconstruction
#assert_trust kernel residualGaussianRotation
#assert_trust kernel residualGaussianCoordinates_hasLaw
#assert_trust kernel residualGaussian_energy
#print axioms residualSingularValue_nonneg
#print axioms residualSingularValue_antitone
#print axioms residual_svd_reconstruction
#print axioms residualGaussianRotation
#print axioms residualGaussianCoordinates_hasLaw
#print axioms residualGaussian_energy
end NLA.Proofs.RE06
