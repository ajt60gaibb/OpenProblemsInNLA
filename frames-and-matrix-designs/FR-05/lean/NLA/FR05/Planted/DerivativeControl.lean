/-
Exact finite-dimensional derivative control for the polynomial factor chart.

In §3.4, after the Jacobian small-ball estimate, the frozen source bounds the
first two derivatives of its local chart to obtain the Jacobian-Lipschitz
estimate (3.23).  The repository uses `factorChart` as its polynomial local
replacement for that chart.  This file proves its exact degree-two identities:
the directional derivative changes bilinearly with the base point and the
second directional difference is constant.  A quantitative Euclidean-to-
operator-norm estimate remains a later analytic layer.
-/
import NLA.FR05.Planted.Newton

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate Matrix RealInnerProductSpace

namespace NLA.FR05

/-- The positive polynomial factor is affine in the chart coordinates, at
every base point (not only at the seed). -/
theorem factorPlus_add_smul {n : ℕ} (s σ u : ℝ) (b c : ℂ)
    (z p : Signal n) :
    factorPlus (s + u * σ) (b + u • c) (z + u • p) =
      factorPlus s b z + u • plusDirection σ c p := by
  funext i
  by_cases hi0 : i.1 = 0
  · simp [factorPlus, plusDirection, joinTwo, hi0]
    ring
  · by_cases hi1 : i.1 = 1
    · simp [factorPlus, plusDirection, joinTwo, hi1]
    · simp [factorPlus, plusDirection, joinTwo, hi0, hi1]

/-- The negative polynomial factor is affine in the chart coordinates, at
every base point. -/
theorem factorMinus_add_smul {n : ℕ} (s σ u : ℝ)
    (t q : Signal n) :
    factorMinus (s + u * σ) (t + u • q) =
      factorMinus s t + u • minusDirection σ q := by
  funext i
  by_cases hi0 : i.1 = 0
  · simp [factorMinus, minusDirection, joinTwo, hi0]
  · by_cases hi1 : i.1 = 1
    · simp [factorMinus, minusDirection, joinTwo, hi1]
      ring
    · simp [factorMinus, minusDirection, joinTwo, hi0, hi1]
      ring

theorem factorPlus_eq_seed_add_direction {n : ℕ}
    (s : ℝ) (b : ℂ) (z : Signal n) :
    factorPlus s b z = factorPlus (n := n) 0 0 0 + plusDirection s b z := by
  simpa using factorPlus_add_smul (n := n) 0 s 1 0 b 0 z

theorem factorMinus_eq_seed_add_direction {n : ℕ}
    (s : ℝ) (t : Signal n) :
    factorMinus s t = factorMinus (n := n) 0 0 + minusDirection s t := by
  simpa using factorMinus_add_smul (n := n) 0 s 1 0 t

/-- The exact directional first-order term of the polynomial factor chart at
an arbitrary base point.  This is its derivative in the indicated real
direction, expressed without invoking an analytic derivative API. -/
def factorChartDirectional {n : ℕ}
    (s : ℝ) (b : ℂ) (z t : Signal n)
    (σ : ℝ) (c : ℂ) (p q : Signal n) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
  Matrix.vecMulVec (plusDirection σ c p) (star (factorPlus s b z)) +
    Matrix.vecMulVec (factorPlus s b z) (star (plusDirection σ c p)) -
      Matrix.vecMulVec (minusDirection σ q) (star (factorMinus s t)) -
        Matrix.vecMulVec (factorMinus s t) (star (minusDirection σ q))

/-- The bilinear change of the chart derivative between the seed and a base
point.  It is symmetric in the two parameter directions. -/
def factorChartDerivativeVariation {n : ℕ}
    (s : ℝ) (b : ℂ) (z t : Signal n)
    (σ : ℝ) (c : ℂ) (p q : Signal n) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
  Matrix.vecMulVec (plusDirection σ c p) (star (plusDirection s b z)) +
    Matrix.vecMulVec (plusDirection s b z) (star (plusDirection σ c p)) -
      Matrix.vecMulVec (minusDirection σ q) (star (minusDirection s t)) -
        Matrix.vecMulVec (minusDirection s t) (star (minusDirection σ q))

/-- Exact second-order expansion around an arbitrary point of the polynomial
factor chart.  The `u²` coefficient is independent of the base point, so it
is the finite-dimensional source of the Jacobian-Lipschitz estimate in
(3.23). -/
theorem factorChart_add_smul_expansion {n : ℕ}
    (u s σ : ℝ) (b c : ℂ) (z t p q : Signal n) :
    factorChart (s + u * σ) (b + u • c) (z + u • p) (t + u • q) =
      factorChart s b z t + u • factorChartDirectional s b z t σ c p q +
        u ^ 2 • factorChartQuadratic σ c p q := by
  rw [factorChart, factorPlus_add_smul, factorMinus_add_smul]
  ext i j
  simp [factorChart, rankOneDifference, factorChartDirectional, factorChartQuadratic,
    Matrix.vecMulVec, Pi.star_apply]
  ring

/-- At the seed, the arbitrary-base directional term is the linear chart
already used for the Jacobian formula (3.21). -/
theorem factorChartDirectional_zero {n : ℕ}
    (σ : ℝ) (c : ℂ) (p q : Signal n) :
    factorChartDirectional (n := n) 0 0 0 0 σ c p q =
      factorChartLinear σ c p q := rfl

/-- The derivative variation is exactly bilinear: no higher-order
remainders occur in the polynomial factor chart. -/
theorem factorChartDirectional_eq_linear_add_variation {n : ℕ}
    (s σ : ℝ) (b c : ℂ) (z t p q : Signal n) :
    factorChartDirectional s b z t σ c p q =
      factorChartLinear σ c p q +
        factorChartDerivativeVariation s b z t σ c p q := by
  unfold factorChartDirectional factorChartLinear factorChartDerivativeVariation
  rw [factorPlus_eq_seed_add_direction, factorMinus_eq_seed_add_direction]
  ext i j
  simp [Matrix.vecMulVec, Pi.star_apply]
  ring

/-- The directional first-order term of one normalized planted equation at
an arbitrary chart point. -/
def plantedEquationDirectional {n : ℕ} (row : PlantedRow n)
    (s : ℝ) (b : ℂ) (z t : Signal n)
    (σ : ℝ) (c : ℂ) (p q : Signal n) : ℝ :=
  (quadraticForm (factorChartDirectional s b z t σ c p q)
    (plantedColumn row)).re / row.radial

/-- The scalar bilinear variation of a planted-equation derivative. -/
def plantedEquationDerivativeVariation {n : ℕ} (row : PlantedRow n)
    (s : ℝ) (b : ℂ) (z t : Signal n)
    (σ : ℝ) (c : ℂ) (p q : Signal n) : ℝ :=
  (quadraticForm (factorChartDerivativeVariation s b z t σ c p q)
    (plantedColumn row)).re / row.radial

theorem plantedEquationDirectional_eq_linear_add_variation {n : ℕ}
    (row : PlantedRow n) (s σ : ℝ) (b c : ℂ) (z t p q : Signal n) :
    plantedEquationDirectional row s b z t σ c p q =
      plantedEquationLinear row σ c p q +
        plantedEquationDerivativeVariation row s b z t σ c p q := by
  unfold plantedEquationDirectional plantedEquationLinear
    plantedEquationDerivativeVariation
  rw [factorChartDirectional_eq_linear_add_variation]
  rw [quadraticForm_add]
  simp only [Complex.add_re]
  ring

/-- Exact second-order finite-difference formula for one planted equation.
The constant `u²` coefficient is the same quadratic term as at the seed;
this is the algebraic core of the source's Jacobian-Lipschitz step (3.23). -/
theorem plantedEquation_add_smul_expansion {n : ℕ} (u : ℝ)
    (row : PlantedRow n) (s σ : ℝ) (b c : ℂ)
    (z t p q : Signal n) :
    plantedEquation row (s + u * σ) (b + u • c) (z + u • p) (t + u • q) =
      plantedEquation row s b z t +
        u * plantedEquationDirectional row s b z t σ c p q +
          u ^ 2 * plantedEquationQuadratic row σ c p q := by
  unfold plantedEquation plantedEquationDirectional plantedEquationQuadratic
  rw [factorChart_add_smul_expansion]
  rw [quadraticForm_add, quadraticForm_add,
    quadraticForm_real_smul, quadraticForm_real_smul]
  simp only [Complex.add_re, Complex.smul_re]
  ring

/-- The central second difference is exactly twice the fixed quadratic
coefficient.  This is an algebraic, source-faithful second-derivative
certificate for the polynomial local chart. -/
theorem plantedEquation_central_second_difference {n : ℕ}
    (row : PlantedRow n) (s σ : ℝ) (b c : ℂ) (z t p q : Signal n) :
    plantedEquation row (s + σ) (b + c) (z + p) (t + q) +
      plantedEquation row (s - σ) (b - c) (z - p) (t - q) -
        2 * plantedEquation row s b z t =
      2 * plantedEquationQuadratic row σ c p q := by
  have hplus := plantedEquation_add_smul_expansion (1 : ℝ)
    row s σ b c z t p q
  have hminus := plantedEquation_add_smul_expansion (-1 : ℝ)
    row s σ b c z t p q
  norm_num [smul_eq_mul] at hplus hminus
  simp only [sub_eq_add_neg] at hminus ⊢
  linarith

/-- The arbitrary-base directional term reduces to the checked Jacobian
linear term at the seed. -/
theorem plantedEquationDirectional_zero {n : ℕ} (row : PlantedRow n)
    (σ : ℝ) (c : ℂ) (p q : Signal n) :
    plantedEquationDirectional row 0 0 0 0 σ c p q =
      plantedEquationLinear row σ c p q := by
  unfold plantedEquationDirectional plantedEquationLinear
  rw [factorChartDirectional_zero]

/-- The directional term coordinatewise assembled into the full planted
equation map. -/
def plantedEquationMapDirectional {m n : ℕ} (rows : Fin m → PlantedRow n)
    (θ η : FactorParameters n) : Fin m → ℝ :=
  fun i ↦ plantedEquationDirectional (rows i)
    θ.1 θ.2.1 θ.2.2.1 θ.2.2.2
    η.1 η.2.1 η.2.2.1 η.2.2.2

/-- The base-independent quadratic coefficient of the full polynomial
equation map. -/
def plantedEquationMapQuadratic {m n : ℕ} (rows : Fin m → PlantedRow n)
    (η : FactorParameters n) : Fin m → ℝ :=
  fun i ↦ plantedEquationQuadratic (rows i)
    η.1 η.2.1 η.2.2.1 η.2.2.2

/-- The seed Jacobian applied to a parameter direction, in the explicit
polynomial-chart representation. -/
def plantedEquationMapLinear {m n : ℕ} (rows : Fin m → PlantedRow n)
    (η : FactorParameters n) : Fin m → ℝ :=
  fun i ↦ plantedEquationLinear (rows i)
    η.1 η.2.1 η.2.2.1 η.2.2.2

/-- The exact bilinear change in the directional derivative from the seed. -/
def plantedEquationMapDerivativeVariation {m n : ℕ}
    (rows : Fin m → PlantedRow n) (θ η : FactorParameters n) : Fin m → ℝ :=
  fun i ↦ plantedEquationDerivativeVariation (rows i)
    θ.1 θ.2.1 θ.2.2.1 θ.2.2.2
    η.1 η.2.1 η.2.2.1 η.2.2.2

/-- Exact derivative-variation identity for the polynomial planted map.  In
particular, all variation of the Jacobian away from zero is bilinear in the
base point and direction. -/
theorem plantedEquationMapDirectional_eq_linear_add_variation {m n : ℕ}
    (rows : Fin m → PlantedRow n) (θ η : FactorParameters n) :
    plantedEquationMapDirectional rows θ η =
      plantedEquationMapLinear rows η +
        plantedEquationMapDerivativeVariation rows θ η := by
  funext i
  exact plantedEquationDirectional_eq_linear_add_variation
    (rows i) θ.1 η.1 θ.2.1 η.2.1 θ.2.2.1 θ.2.2.2 η.2.2.1 η.2.2.2

/-- Exact finite-dimensional Taylor identity for the entire normalized
planted equation map. -/
theorem plantedEquationMap_add_smul_expansion {m n : ℕ}
    (rows : Fin m → PlantedRow n) (θ η : FactorParameters n) (u : ℝ) :
    plantedEquationMap rows (θ + u • η) =
      plantedEquationMap rows θ + u • plantedEquationMapDirectional rows θ η +
        u ^ 2 • plantedEquationMapQuadratic rows η := by
  rcases θ with ⟨s, b, z, t⟩
  rcases η with ⟨σ, c, p, q⟩
  funext i
  simpa [plantedEquationMap, plantedEquationMapDirectional,
    plantedEquationMapQuadratic, smul_eq_mul] using
    plantedEquation_add_smul_expansion u (rows i) s σ b c z t p q

end NLA.FR05
