import NLA.FR05.Geometry.FactorChart
import Mathlib.Analysis.Complex.Trigonometric

/-!
# The planted chart and its quadratic expansion

The sections develop `Planted`, `PlantedTaylor`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section Planted

/-
The deterministic row parametrization in equation (3.18) of the frozen
source.  The probability law on these parameters and its quantitative tails
are deliberately kept in later analytic modules.
-/

open scoped BigOperators ComplexConjugate Matrix

theorem normSq_polar (r α : ℝ) (hr : 0 ≤ r) :
    Complex.normSq ((Real.sqrt r : ℂ) * Complex.exp (α * Complex.I)) = r := by
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  have hphase : Complex.normSq (Complex.exp (α * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  rw [hphase, mul_one]
  nlinarith [Real.sq_sqrt hr]

/-- One deterministic row in the planted parametrization.  The inequalities
are exactly what is needed for the two square roots in (3.18). -/
structure PlantedRow (n : ℕ) where
  radial : ℝ
  imbalance : ℝ
  phaseOne : ℝ
  phaseTwo : ℝ
  tail : Signal n
  radial_pos : 0 < radial
  imbalance_le_one : |imbalance| ≤ 1

/-- The planted column vector from (3.18), for a fixed realization of its
parameters. -/
def plantedColumn {n : ℕ} (r : PlantedRow n) : Signal (n + 2) :=
  joinTwo
    ((Real.sqrt (r.radial * (1 + r.imbalance) / 2) : ℂ) *
      Complex.exp (r.phaseOne * Complex.I))
    ((Real.sqrt (r.radial * (1 - r.imbalance) / 2) : ℂ) *
      Complex.exp (r.phaseTwo * Complex.I))
    r.tail

theorem plantedColumn_first_normSq {n : ℕ} (r : PlantedRow n) :
    Complex.normSq (plantedColumn r ⟨0, Nat.zero_lt_succ _⟩) =
      r.radial * (1 + r.imbalance) / 2 := by
  have hξ := abs_le.mp r.imbalance_le_one
  have hradial : 0 ≤ r.radial * (1 + r.imbalance) / 2 := by
    exact div_nonneg (mul_nonneg r.radial_pos.le (by linarith [hξ.1])) (by norm_num)
  exact normSq_polar _ _ hradial

theorem plantedColumn_second_normSq {n : ℕ} (r : PlantedRow n) :
    Complex.normSq (plantedColumn r ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) =
      r.radial * (1 - r.imbalance) / 2 := by
  have hξ := abs_le.mp r.imbalance_le_one
  have hradial : 0 ≤ r.radial * (1 - r.imbalance) / 2 := by
    exact div_nonneg (mul_nonneg r.radial_pos.le (by linarith [hξ.2])) (by norm_num)
  exact normSq_polar _ _ hradial

theorem normSq_star_dotProduct_standardBasis {d : ℕ}
    (a : Signal d) (j : Fin d) :
    Complex.normSq (star a ⬝ᵥ standardBasis j) = Complex.normSq (a j) := by
  have hsingle : standardBasis j = Pi.single j 1 := by
    funext k
    simp [standardBasis, Pi.single_apply, eq_comm]
  rw [hsingle, dotProduct_single_one]
  rw [Pi.star_apply]
  exact Complex.normSq_conj _

/-- The actual frame convention used by the source: rows are adjoints of the
planted columns. -/
def plantedFrame {m n : ℕ} (rows : Fin m → PlantedRow n) : Frame m (n + 2) :=
  fun i => star (plantedColumn (rows i))

theorem conjugateRow_plantedFrame {m n : ℕ} (rows : Fin m → PlantedRow n)
    (i : Fin m) :
    conjugateRow (plantedFrame rows) i = plantedColumn (rows i) := by
  simp [conjugateRow, plantedFrame]

/-- The source's initial identity `Fᵋ(0) = ξ`, before the normalization by
the positive radial variable. -/
theorem factorChart_zero_quadraticForm_plantedColumn {n : ℕ}
    (r : PlantedRow n) :
    quadraticForm (factorChart (n := n) 0 0 0 0) (plantedColumn r) =
      (r.radial * r.imbalance : ℂ) := by
  rw [factorChart, factorPlus_zero, factorMinus_zero,
    quadraticForm_rankOneDifference]
  rw [normSq_star_dotProduct_standardBasis,
    normSq_star_dotProduct_standardBasis]
  have hfirst : firstCoordinate (n + 2) (by lia) =
      ⟨0, Nat.zero_lt_succ _⟩ := by
    apply Fin.ext
    rfl
  have hsecond : secondCoordinate (n + 2) (by lia) =
      ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩ := by
    apply Fin.ext
    rfl
  rw [hfirst, hsecond, plantedColumn_first_normSq, plantedColumn_second_normSq]
  push_cast
  ring

theorem factorChart_zero_quadraticForm_plantedFrame {m n : ℕ}
    (rows : Fin m → PlantedRow n) (i : Fin m) :
    quadraticForm (factorChart (n := n) 0 0 0 0)
      (conjugateRow (plantedFrame rows) i) =
      ((rows i).radial * (rows i).imbalance : ℂ) := by
  rw [conjugateRow_plantedFrame]
  exact factorChart_zero_quadraticForm_plantedColumn (rows i)

/-- The real normalized equation `F_i` used in the planted construction,
written in the factor chart. -/
def plantedEquation {n : ℕ} (r : PlantedRow n)
    (s : ℝ) (b : ℂ) (z t : Signal n) : ℝ :=
  (quadraticForm (factorChart s b z t) (plantedColumn r)).re / r.radial

/-- Equation (3.18) yields the exact seed value `F_i^ε(0) = ξ_i`. -/
@[simp]
theorem plantedEquation_zero {n : ℕ} (r : PlantedRow n) :
    plantedEquation r 0 0 0 0 = r.imbalance := by
  unfold plantedEquation
  rw [factorChart_zero_quadraticForm_plantedColumn]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  field_simp [r.radial_pos.ne']

theorem plantedFrame_equation_zero {m n : ℕ}
    (rows : Fin m → PlantedRow n) (i : Fin m) :
    plantedEquation (rows i) 0 0 0 0 = (rows i).imbalance :=
  plantedEquation_zero (rows i)

theorem quadraticForm_factorChart {n : ℕ}
    (a : Signal (n + 2)) (s : ℝ) (b : ℂ) (z t : Signal n) :
    quadraticForm (factorChart s b z t) a =
      (Complex.normSq (star a ⬝ᵥ factorPlus s b z) -
        Complex.normSq (star a ⬝ᵥ factorMinus s t) : ℂ) := by
  rw [factorChart, quadraticForm_rankOneDifference]

/-- A zero of the normalized real equation is an exact complex quadratic
kernel equation, because the chart is Hermitian by construction. -/
theorem quadraticForm_eq_zero_of_plantedEquation_eq_zero {n : ℕ}
    (r : PlantedRow n) (s : ℝ) (b : ℂ) (z t : Signal n)
    (hzero : plantedEquation r s b z t = 0) :
    quadraticForm (factorChart s b z t) (plantedColumn r) = 0 := by
  let Δ : ℝ :=
    Complex.normSq (star (plantedColumn r) ⬝ᵥ factorPlus s b z) -
      Complex.normSq (star (plantedColumn r) ⬝ᵥ factorMinus s t)
  have hquadratic : quadraticForm (factorChart s b z t) (plantedColumn r) =
      (Δ : ℂ) := by
    simpa [Δ] using quadraticForm_factorChart (plantedColumn r) s b z t
  have hdivision : Δ / r.radial = 0 := by
    unfold plantedEquation at hzero
    rw [hquadratic] at hzero
    simpa [Δ] using hzero
  have hdelta : Δ = 0 := by
    rcases div_eq_zero_iff.mp hdivision with h | h
    · exact h
    · exact False.elim (r.radial_pos.ne' h)
  rw [hquadratic, hdelta]
  norm_num

/-- The source's fixed-point conclusion, now with every deterministic link
to noninjectivity checked for the actual planted row parametrization. -/
theorem plantedFrame_not_phaseRetrievalInjective_of_equations_eq_zero
    {m n : ℕ} (rows : Fin m → PlantedRow n)
    (s : ℝ) (b : ℂ) (z t : Signal n)
    (hs : |s| ≤ 1)
    (hzero : ∀ i, plantedEquation (rows i) s b z t = 0) :
    ¬ PhaseRetrievalInjective (plantedFrame rows) := by
  apply factorChart_not_phaseRetrievalInjective_of_quadraticForm_zero
    (plantedFrame rows) s b z t hs
  intro i
  rw [conjugateRow_plantedFrame]
  exact quadraticForm_eq_zero_of_plantedEquation_eq_zero
    (rows i) s b z t (hzero i)

/-- Squared Euclidean norm of a finite complex signal, written directly as a
sum so it is independent of the ambient function-space norm convention. -/
def squaredEuclideanNorm {d : ℕ} (x : Signal d) : ℝ :=
  ∑ j, Complex.normSq (x j)

theorem squaredEuclideanNorm_joinTwo {n : ℕ} (u v : ℂ) (w : Signal n) :
    squaredEuclideanNorm (joinTwo u v w) =
      Complex.normSq u + Complex.normSq v + squaredEuclideanNorm w := by
  unfold squaredEuclideanNorm
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [joinTwo]
  ring

/-- The exact norm identity used in the planted-law tail estimate (3.22). -/
theorem squaredEuclideanNorm_plantedColumn {n : ℕ} (r : PlantedRow n) :
    squaredEuclideanNorm (plantedColumn r) =
      r.radial + squaredEuclideanNorm r.tail := by
  have hξ := abs_le.mp r.imbalance_le_one
  have hplus : 0 ≤ r.radial * (1 + r.imbalance) / 2 := by
    exact div_nonneg (mul_nonneg r.radial_pos.le (by linarith [hξ.1])) (by norm_num)
  have hminus : 0 ≤ r.radial * (1 - r.imbalance) / 2 := by
    exact div_nonneg (mul_nonneg r.radial_pos.le (by linarith [hξ.2])) (by norm_num)
  unfold plantedColumn
  rw [squaredEuclideanNorm_joinTwo, normSq_polar _ _ hplus,
    normSq_polar _ _ hminus]
  ring

/-- The source's coupled reference row `a_i^0`, obtained by replacing only
the imbalance coordinate by zero. -/
def PlantedRow.zeroImbalance {n : ℕ} (r : PlantedRow n) : PlantedRow n :=
  { r with imbalance := 0, imbalance_le_one := by norm_num }

/-- The $epsilon$ and zero-imbalance coupled rows have exactly the same
squared Euclidean norm, as used in (3.22). -/
theorem squaredEuclideanNorm_plantedColumn_zeroImbalance {n : ℕ}
    (r : PlantedRow n) :
    squaredEuclideanNorm (plantedColumn r) =
      squaredEuclideanNorm (plantedColumn r.zeroImbalance) := by
  rw [squaredEuclideanNorm_plantedColumn,
    squaredEuclideanNorm_plantedColumn]
  rfl

end Planted

section PlantedTaylor

/-
The exact Taylor expansion of the source's normalized measurement equations
in the polynomial factor chart.
-/

open scoped BigOperators ComplexConjugate Matrix

theorem quadraticForm_add {d : ℕ} (a : Signal d)
    (Q R : Matrix (Fin d) (Fin d) ℂ) :
    quadraticForm (Q + R) a = quadraticForm Q a + quadraticForm R a := by
  simp [quadraticForm, Matrix.add_mulVec, dotProduct_add]

theorem quadraticForm_real_smul {d : ℕ} (a : Signal d)
    (r : ℝ) (Q : Matrix (Fin d) (Fin d) ℂ) :
    quadraticForm (r • Q) a = r • quadraticForm Q a := by
  simp [quadraticForm, Matrix.smul_mulVec, dotProduct_smul]

/-- The directional linear term of a planted measurement equation. -/
def plantedEquationLinear {n : ℕ} (row : PlantedRow n)
    (s : ℝ) (b : ℂ) (z t : Signal n) : ℝ :=
  (quadraticForm (factorChartLinear s b z t) (plantedColumn row)).re / row.radial

/-- The exact directional quadratic remainder of a planted measurement
equation. -/
def plantedEquationQuadratic {n : ℕ} (row : PlantedRow n)
    (s : ℝ) (b : ℂ) (z t : Signal n) : ℝ :=
  (quadraticForm (factorChartQuadratic s b z t) (plantedColumn row)).re / row.radial

/-- The planted measurement equations are exactly quadratic along every
parameter ray.  This is a source-specific, checked replacement for an
informal first-derivative calculation at the seed. -/
theorem plantedEquation_scaled_expansion {n : ℕ} (u : ℝ) (row : PlantedRow n)
    (s : ℝ) (b : ℂ) (z t : Signal n) :
    plantedEquation row (u * s) (u • b) (u • z) (u • t) =
      plantedEquation row 0 0 0 0 + u * plantedEquationLinear row s b z t +
        u ^ 2 * plantedEquationQuadratic row s b z t := by
  unfold plantedEquation plantedEquationLinear plantedEquationQuadratic
  rw [factorChart_scaled_expansion]
  rw [quadraticForm_add, quadraticForm_add,
    quadraticForm_real_smul, quadraticForm_real_smul]
  simp only [Complex.add_re, Complex.smul_re]
  ring

end PlantedTaylor

end NLA.FR05
