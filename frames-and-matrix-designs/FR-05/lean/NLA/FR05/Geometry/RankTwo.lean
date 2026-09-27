import NLA.FR05.Definitions
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Rank

/-! ## RankTwoChart -/

section

/-
The rank-two Hermitian chart of equation (3.19) in the frozen source.
The source uses this chart to turn a small residual into an exact ambiguity.
This module verifies its finite-dimensional geometry independently of the
subsequent probability estimates.
-/


set_option autoImplicit false
open scoped Matrix ComplexConjugate BigOperators
open Matrix
noncomputable section

namespace NLA.FR05

abbrev ChartIndex (n : ℕ) := Fin 2 ⊕ Fin n

/-- The block-coordinate identification used to transport the source chart
back to the original `Fin M` ambient signal space. -/
def chartEquiv (M : ℕ) (hM : 2 ≤ M) : ChartIndex (M - 2) ≃ Fin M :=
  finSumFinEquiv.trans (Fin.castOrderIso (by lia)).toEquiv

/-! ### Generic graph construction -/

def qThetaOf {n : ℕ} (D : Matrix (Fin 2) (Fin 2) ℂ)
    (C : Matrix (Fin n) (Fin 2) ℂ) : Matrix (ChartIndex n) (ChartIndex n) ℂ :=
  Matrix.fromBlocks D Cᴴ C (C * D⁻¹ * Cᴴ)

def qThetaLeftFactor {n : ℕ} (D : Matrix (Fin 2) (Fin 2) ℂ)
    (C : Matrix (Fin n) (Fin 2) ℂ) : Matrix (ChartIndex n) (Fin 2) ℂ :=
  Matrix.fromRows 1 (C * D⁻¹)

def qThetaRightFactor {n : ℕ} (D : Matrix (Fin 2) (Fin 2) ℂ)
    (C : Matrix (Fin n) (Fin 2) ℂ) : Matrix (Fin 2) (ChartIndex n) ℂ :=
  Matrix.fromCols 1 (D⁻¹ * Cᴴ)

theorem qThetaOf_rectangular_factorization {n : ℕ}
    (D : Matrix (Fin 2) (Fin 2) ℂ) (C : Matrix (Fin n) (Fin 2) ℂ)
    (hD : IsUnit D.det) :
    qThetaOf D C = qThetaLeftFactor D C * D * qThetaRightFactor D C := by
  unfold qThetaOf qThetaLeftFactor qThetaRightFactor
  rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
  simp only [Matrix.one_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc D D⁻¹ Cᴴ, Matrix.mul_nonsing_inv D hD]
  rw [Matrix.mul_assoc C D⁻¹ D, Matrix.nonsing_inv_mul D hD]
  simp [Matrix.mul_assoc]

theorem qThetaOf_isHermitian {n : ℕ} (D : Matrix (Fin 2) (Fin 2) ℂ)
    (C : Matrix (Fin n) (Fin 2) ℂ) (hD : D.IsHermitian) :
    (qThetaOf D C).IsHermitian := by
  unfold qThetaOf
  exact Matrix.IsHermitian.fromBlocks hD (conjTranspose_conjTranspose C)
    (Matrix.isHermitian_mul_mul_conjTranspose C hD.inv)

theorem qThetaOf_rank_two {n : ℕ} (D : Matrix (Fin 2) (Fin 2) ℂ)
    (C : Matrix (Fin n) (Fin 2) ℂ) (hD : D.det ≠ 0) :
    (qThetaOf D C).rank = 2 := by
  have hunit : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  have hD_rank : D.rank = 2 := by
    simpa using (Matrix.rank_of_det_ne_zero hD)
  apply le_antisymm
  · rw [qThetaOf_rectangular_factorization D C hunit]
    calc
      (qThetaLeftFactor D C * D * qThetaRightFactor D C).rank ≤
          (qThetaLeftFactor D C * D).rank := Matrix.rank_mul_le_left _ _
      _ ≤ D.rank := Matrix.rank_mul_le_right _ _
      _ = 2 := hD_rank
  · calc
      2 = D.rank := hD_rank.symm
      _ = ((qThetaOf D C).submatrix Sum.inl Sum.inl).rank := by rfl
      _ ≤ (qThetaOf D C).rank := Matrix.rank_submatrix_le _ Sum.inl Sum.inl

/-! ### The Section 3.4 coordinates -/

def chartD (s : ℝ) (b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ) + (s / 2 : ℝ), b;
    star b, (-1 : ℂ) + (s / 2 : ℝ)]

def chartC {n : ℕ} (z t : Fin n → ℂ) : Matrix (Fin n) (Fin 2) ℂ :=
  fun i => ![z i, t i]

/-- Li's source chart (3.19), retained in its original block form. -/
def qTheta {n : ℕ} (s : ℝ) (b : ℂ) (z t : Fin n → ℂ) :
    Matrix (ChartIndex n) (ChartIndex n) ℂ :=
  qThetaOf (chartD s b) (chartC z t)

theorem chartD_isHermitian (s : ℝ) (b : ℂ) : (chartD s b).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [chartD]

theorem chartD_zero : chartD 0 0 = !![(1 : ℂ), 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [chartD]

theorem chartC_zero {n : ℕ} : chartC (0 : Fin n → ℂ) 0 = 0 := by
  ext i j
  fin_cases j <;> simp [chartC]

theorem chartD_det (s : ℝ) (b : ℂ) :
    (chartD s b).det = ((s ^ 2 / 4 - 1 - Complex.normSq b : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp [chartD, Complex.normSq_eq_conj_mul_self]
  ring

theorem chartD_det_ne_zero_of_abs_le_one (s : ℝ) (b : ℂ) (hs : |s| ≤ 1) :
    (chartD s b).det ≠ 0 := by
  have hs' : -1 ≤ s ∧ s ≤ 1 := (abs_le).mp hs
  have hsq : s ^ 2 ≤ 1 := by
    have hprod : (s - 1) * (s + 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs'.2) (by
        simpa using sub_nonneg.mpr hs'.1)
    nlinarith
  have hb : 0 ≤ Complex.normSq b := Complex.normSq_nonneg b
  have hneg : s ^ 2 / 4 - 1 - Complex.normSq b < 0 := by
    nlinarith
  rw [chartD_det]
  exact_mod_cast hneg.ne

theorem qTheta_zero {n : ℕ} : qTheta (n := n) 0 0 0 0 =
    Matrix.fromBlocks (!![(1 : ℂ), 0; 0, -1]) 0 0 0 := by
  unfold qTheta qThetaOf
  rw [chartD_zero, chartC_zero]
  simp

theorem qTheta_isHermitian {n : ℕ} (s : ℝ) (b : ℂ) (z t : Fin n → ℂ) :
    (qTheta s b z t).IsHermitian :=
  qThetaOf_isHermitian _ _ (chartD_isHermitian s b)

/-- On the source's fixed local ball, the chart matrix has rank exactly two. -/
theorem qTheta_rank_two_of_abs_le_one {n : ℕ} (s : ℝ) (b : ℂ)
    (z t : Fin n → ℂ) (hs : |s| ≤ 1) :
    (qTheta s b z t).rank = 2 :=
  qThetaOf_rank_two _ _ (chartD_det_ne_zero_of_abs_le_one s b hs)

/-- The same local domain gives explicit positive and negative quadratic
directions, a direct certificate of the source's indefinite-chart claim. -/
theorem qTheta_opposite_diagonal_of_abs_le_one {n : ℕ} (s : ℝ) (b : ℂ)
    (z t : Fin n → ℂ) (hs : |s| ≤ 1) :
    0 < (qTheta s b z t (Sum.inl (0 : Fin 2)) (Sum.inl (0 : Fin 2))).re ∧
      (qTheta s b z t (Sum.inl (1 : Fin 2)) (Sum.inl (1 : Fin 2))).re < 0 := by
  have hs' : -1 ≤ s ∧ s ≤ 1 := (abs_le).mp hs
  constructor
  · change 0 < (1 + s / 2 : ℝ)
    linarith
  · change (-1 + s / 2 : ℝ) < 0
    linarith

end NLA.FR05

end
end

/-! ## RankTwoSeed -/

section

/-
The concrete Hermitian seed at the beginning of Li's construction.  This file
contains only finite-dimensional exact identities; the later local chart and
probability estimates are intentionally separate.
-/


set_option autoImplicit false
open scoped BigOperators ComplexConjugate Matrix
noncomputable section

namespace NLA.FR05

private theorem firstCoordinate_ne_secondCoordinate' (d : ℕ) (hd : 2 ≤ d) :
    firstCoordinate d hd ≠ secondCoordinate d hd := by
  simp [firstCoordinate, secondCoordinate]

/-- The constant-one test vector.  It is the conjugated row of `flatFrame`. -/
def allOnesSignal (d : ℕ) : Signal d := fun _ => 1

/-- Li's diagonal seed is Hermitian. -/
theorem qZero_isHermitian (d : ℕ) (hd : 2 ≤ d) :
    (qZero d hd).IsHermitian := by
  rw [qZero, Matrix.isHermitian_diagonal_iff]
  intro k
  rw [isSelfAdjoint_iff]
  by_cases hk₀ : k = firstCoordinate d hd
  · simp [hk₀]
  · by_cases hk₁ : k = secondCoordinate d hd
    · have hne : secondCoordinate d hd ≠ firstCoordinate d hd :=
        Ne.symm (firstCoordinate_ne_secondCoordinate' d hd)
      simp [hk₁, hne]
    · simp [hk₀, hk₁]

/-- Acting on the constant-one vector, the seed produces the difference of
the first two coordinate vectors. -/
theorem qZero_mulVec_allOnes (d : ℕ) (hd : 2 ≤ d) :
    qZero d hd *ᵥ allOnesSignal d =
      standardBasis (firstCoordinate d hd) - standardBasis (secondCoordinate d hd) := by
  funext k
  rw [qZero, Matrix.mulVec_diagonal]
  by_cases hk₀ : k = firstCoordinate d hd
  · subst k
    simp [allOnesSignal, standardBasis,
      firstCoordinate_ne_secondCoordinate' d hd]
  · by_cases hk₁ : k = secondCoordinate d hd
    · subst k
      have hne : secondCoordinate d hd ≠ firstCoordinate d hd :=
        Ne.symm (firstCoordinate_ne_secondCoordinate' d hd)
      simp [allOnesSignal, standardBasis, hne]
    · simp [allOnesSignal, standardBasis, hk₀, hk₁]

/-- The Hermitian seed is invisible to the constant-one row.  This is the
finite exact identity underlying the planted ambiguity before any stability
or distributional estimate is introduced. -/
theorem quadraticForm_qZero_allOnes (d : ℕ) (hd : 2 ≤ d) :
    quadraticForm (qZero d hd) (allOnesSignal d) = 0 := by
  rw [quadraticForm, qZero_mulVec_allOnes]
  simp [allOnesSignal, standardBasis, dotProduct, Finset.sum_sub_distrib]

end NLA.FR05

end

end
