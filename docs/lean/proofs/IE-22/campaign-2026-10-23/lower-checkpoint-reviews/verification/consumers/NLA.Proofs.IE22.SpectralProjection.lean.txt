import NLA.Proofs.IE22.EnergyBounds
import NLA.Proofs.IE22.GaussianBasics
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Trace

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.IE22

/-- Frobenius square is an actual matrix trace, with the coordinate sums explicit. -/
theorem matrix_entry_square_sum {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) :
    ∑ i, ∑ j, B i j ^ 2 = Matrix.trace (B.transpose * B) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    pow_two]
  exact Finset.sum_comm

/-- An exact diagonal retained covariance bounds the L1 Gram sum. -/
theorem gram_abs_sum_le_of_diagonal {m d r : ℕ}
    (B : Matrix (Fin m) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hdiag : B.transpose * B = Matrix.diagonal lam)
    (hnonneg : ∀ j, 0 ≤ lam j)
    (hcap : ∀ j, lam j ≤ (m : ℝ)/(r+1 : ℕ))
    (htrace : ∑ j, lam j ≤ (m : ℝ)) :
    (∑ i, ∑ j, |(B * B.transpose) i j|) ≤ (m : ℝ)^2/Real.sqrt (r+1 : ℕ) := by
  let G := B * B.transpose
  have hG : G.transpose = G := by simp [G, Matrix.transpose_mul]
  have hsq : ∑ i, ∑ j, G i j ^ 2 = ∑ j, (lam j)^2 := by
    rw [matrix_entry_square_sum, hG]
    have hcycle : Matrix.trace ((B*B.transpose)*(B*B.transpose)) =
        Matrix.trace ((B.transpose*B)*(B.transpose*B)) := by
      calc
        _ = Matrix.trace (B * (B.transpose * B * B.transpose)) := by
          congr 1; simp only [Matrix.mul_assoc]
        _ = Matrix.trace ((B.transpose * B * B.transpose) * B) := Matrix.trace_mul_comm _ _
        _ = _ := by congr 1; simp only [Matrix.mul_assoc]
    change Matrix.trace ((B*B.transpose)*(B*B.transpose)) = _
    rw [hcycle, hdiag]
    simp [Matrix.diagonal_mul_diagonal, pow_two]
  have hD : (0 : ℝ) < (r+1 : ℕ) := by positivity
  have hsum : ∑ j, (lam j)^2 ≤ (m : ℝ)^2/(r+1 : ℕ) := by
    calc
      _ ≤ ∑ j, ((m : ℝ)/(r+1 : ℕ)) * lam j := by
        apply Finset.sum_le_sum
        intro j _
        nlinarith [mul_le_mul_of_nonneg_right (hcap j) (hnonneg j)]
      _ = ((m : ℝ)/(r+1 : ℕ)) * ∑ j, lam j := by rw [Finset.mul_sum]
      _ ≤ ((m : ℝ)/(r+1 : ℕ)) * m :=
        mul_le_mul_of_nonneg_left htrace (by positivity)
      _ = _ := by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (Fin m × Fin m)))
    (f := fun _ => (1 : ℝ)) (g := fun ij => |G ij.1 ij.2|)
  have hcs' : (∑ i, ∑ j, |G i j|)^2 ≤ (m : ℝ)^2 * (∑ i, ∑ j, G i j ^ 2) := by
    simpa only [one_mul, one_pow, sq_abs, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, nsmul_eq_mul, mul_one,
      Fintype.sum_prod_type, ← pow_two, sq_abs, Nat.cast_pow] using hcs
  have hfinal : (∑ i, ∑ j, |G i j|)^2 ≤ (m : ℝ)^4/(r+1 : ℕ) := by
    rw [hsq] at hcs'
    calc
      _ ≤ (m : ℝ)^2 * (∑ j, (lam j)^2) := hcs'
      _ ≤ (m : ℝ)^2 * ((m : ℝ)^2/(r+1 : ℕ)) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = _ := by ring
  have hsqrt : (Real.sqrt (r+1 : ℕ))^2 = (r+1 : ℕ) := Real.sq_sqrt hD.le
  apply (sq_le_sq₀ (by positivity : 0 ≤ ∑ i, ∑ j, |G i j|)
    (by positivity : 0 ≤ (m : ℝ)^2/Real.sqrt (r+1 : ℕ))).1
  calc
    _ ≤ (m : ℝ)^4/(r+1 : ℕ) := hfinal
    _ = _ := by rw [div_pow, hsqrt]; ring

/-- An actual covariance matrix has an ordered orthonormal eigenbasis,
with nonnegative eigenvalues summing to the unit-row trace. -/
theorem ordered_covariance_basis {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : NLA.Statements.RowDeletion.UnitRows A) :
    ∃ b : OrthonormalBasis (Fin n) ℝ (Euclid n), ∃ lam : Fin n → ℝ,
      Antitone lam ∧ (∀ j, 0 ≤ lam j) ∧ (∑ j, lam j = (m : ℝ)) ∧
      ∀ j, Matrix.toEuclideanLin (A.transpose*A) (b j) = lam j • b j := by
  let C := A.transpose*A
  let T := Matrix.toEuclideanLin C
  have hC : C.IsHermitian := by
    simpa only [C, Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.isHermitian_conjTranspose_mul_self A
  have hCp : C.PosSemidef := by
    simpa only [C, Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self A
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hC
  have hn : Module.finrank ℝ (Euclid n) = n := by simp [Euclid]
  let b := hT.eigenvectorBasis hn
  let lam := hT.eigenvalues hn
  refine ⟨b,lam,hT.eigenvalues_antitone hn,?_,?_,hT.apply_eigenvectorBasis hn⟩
  · intro j
    apply eigenvalue_nonneg_of_nonneg (hT.hasEigenvalue_eigenvalues hn j)
    intro x
    simpa only [T, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
      RCLike.re_to_real, dotProduct_comm] using hCp.re_dotProduct_nonneg (WithLp.ofLp x)
  · have htrace := hT.trace_eq_sum_eigenvalues hn
    have heq : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis T = C := by
      ext i j
      simp [LinearMap.toMatrix_apply, T, Matrix.toLpLin_apply]
    have htraceT : LinearMap.trace ℝ (Euclid n) T = Matrix.trace C := by
      rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis, heq]
    rw [htraceT] at htrace
    change Matrix.trace C = ∑ j, lam j at htrace
    change ∑ j, lam j = _
    rw [← htrace]
    change Matrix.trace (A.transpose*A) = _
    rw [← matrix_entry_square_sum]
    calc
      _ = ∑ _i : Fin m, (1 : ℝ) := Finset.sum_congr rfl (fun i _ => hA i)
      _ = _ := by simp

#assert_trust kernel ordered_covariance_basis
#assert_trust kernel gram_abs_sum_le_of_diagonal
#print axioms gram_abs_sum_le_of_diagonal
end NLA.Proofs.IE22
