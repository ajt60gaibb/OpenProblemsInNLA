/-
Deterministic comparison between the actual planted linearization and the
zero-imbalance Jacobian used in the source's equation (3.21).

The small source imbalance changes only the first two entries of a planted
column.  This file isolates that perturbation before it is assembled with the
matrix-level least-singular-value argument.
-/
import NLA.FR05.Planted.SourceJacobianMatrix
import NLA.FR05.Planted.DerivativeNorm

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate Matrix RealInnerProductSpace

namespace NLA.FR05

/-- The bilinear cross term occurring in the raw planted linearization. -/
def plantedLinearCross {d : ℕ} (a u v : Signal d) : ℂ :=
  (star a ⬝ᵥ u) * star (star a ⬝ᵥ v)

theorem plantedLinearCross_sub_expansion {d : ℕ}
    (a a0 u v : Signal d) :
    plantedLinearCross a u v - plantedLinearCross a0 u v =
      (star (a - a0) ⬝ᵥ u) * star (star a ⬝ᵥ v) +
        (star a0 ⬝ᵥ u) * star (star (a - a0) ⬝ᵥ v) := by
  unfold plantedLinearCross
  have hstar : star (a - a0) = star a - star a0 := by
    ext i
    simp
  have hdotu : star (a - a0) ⬝ᵥ u =
      star a ⬝ᵥ u - star a0 ⬝ᵥ u := by
    rw [hstar, sub_dotProduct]
  have hdotv : star (a - a0) ⬝ᵥ v =
      star a ⬝ᵥ v - star a0 ⬝ᵥ v := by
    rw [hstar, sub_dotProduct]
  rw [hdotu, hdotv, star_sub]
  ring

/-- A finite-dimensional perturbation bound for one cross term. -/
theorem norm_plantedLinearCross_sub_le {d : ℕ}
    (a a0 u v : Signal d) :
    ‖plantedLinearCross a u v - plantedLinearCross a0 u v‖ ≤
      (d : ℝ) ^ 2 * ‖a - a0‖ * (‖a‖ + ‖a0‖) * ‖u‖ * ‖v‖ := by
  rw [plantedLinearCross_sub_expansion]
  calc
    ‖(star (a - a0) ⬝ᵥ u) * star (star a ⬝ᵥ v) +
        (star a0 ⬝ᵥ u) * star (star (a - a0) ⬝ᵥ v)‖ ≤
        ‖(star (a - a0) ⬝ᵥ u) * star (star a ⬝ᵥ v)‖ +
          ‖(star a0 ⬝ᵥ u) * star (star (a - a0) ⬝ᵥ v)‖ :=
      norm_add_le _ _
    _ = ‖star (a - a0) ⬝ᵥ u‖ * ‖star a ⬝ᵥ v‖ +
          ‖star a0 ⬝ᵥ u‖ * ‖star (a - a0) ⬝ᵥ v‖ := by
      simp only [norm_mul, norm_star]
    _ ≤ ((d : ℝ) * ‖a - a0‖ * ‖u‖) * ((d : ℝ) * ‖a‖ * ‖v‖) +
          ((d : ℝ) * ‖a0‖ * ‖u‖) * ((d : ℝ) * ‖a - a0‖ * ‖v‖) := by
      gcongr
      · exact norm_star_dotProduct_le (a - a0) u
      · exact norm_star_dotProduct_le a v
      · exact norm_star_dotProduct_le a0 u
      · exact norm_star_dotProduct_le (a - a0) v
    _ = (d : ℝ) ^ 2 * ‖a - a0‖ * (‖a‖ + ‖a0‖) * ‖u‖ * ‖v‖ := by
      ring

/-- The two-cross-term expression in the raw planted linearization is stable
under a perturbation of the planted column. -/
theorem abs_normalized_plantedLinearCross_sub_le {d : ℕ} (S : ℝ)
    (hS : 0 < S) (a a0 uPlus vPlus uMinus vMinus : Signal d) :
    |((2 * (plantedLinearCross a uPlus vPlus).re -
        2 * (plantedLinearCross a uMinus vMinus).re) / S) -
      ((2 * (plantedLinearCross a0 uPlus vPlus).re -
        2 * (plantedLinearCross a0 uMinus vMinus).re) / S)| ≤
      2 * (d : ℝ) ^ 2 * ‖a - a0‖ * (‖a‖ + ‖a0‖) / S *
        (‖uPlus‖ * ‖vPlus‖ + ‖uMinus‖ * ‖vMinus‖) := by
  let ΔPlus : ℂ := plantedLinearCross a uPlus vPlus -
    plantedLinearCross a0 uPlus vPlus
  let ΔMinus : ℂ := plantedLinearCross a uMinus vMinus -
    plantedLinearCross a0 uMinus vMinus
  have hrewrite :
      ((2 * (plantedLinearCross a uPlus vPlus).re -
          2 * (plantedLinearCross a uMinus vMinus).re) / S) -
        ((2 * (plantedLinearCross a0 uPlus vPlus).re -
          2 * (plantedLinearCross a0 uMinus vMinus).re) / S) =
        (2 * ΔPlus.re - 2 * ΔMinus.re) / S := by
    dsimp [ΔPlus, ΔMinus]
    ring
  rw [hrewrite, abs_div, abs_of_pos hS]
  have hnumerator :
      |2 * ΔPlus.re - 2 * ΔMinus.re| ≤ 2 * ‖ΔPlus‖ + 2 * ‖ΔMinus‖ := by
    calc
      |2 * ΔPlus.re - 2 * ΔMinus.re| ≤
          |2 * ΔPlus.re| + |2 * ΔMinus.re| := abs_sub _ _
      _ = 2 * |ΔPlus.re| + 2 * |ΔMinus.re| := by
        norm_num [abs_mul]
      _ ≤ 2 * ‖ΔPlus‖ + 2 * ‖ΔMinus‖ := by
        gcongr
        · exact Complex.abs_re_le_norm _
        · exact Complex.abs_re_le_norm _
  calc
    |2 * ΔPlus.re - 2 * ΔMinus.re| / S ≤
        (2 * ‖ΔPlus‖ + 2 * ‖ΔMinus‖) / S :=
      div_le_div_of_nonneg_right hnumerator hS.le
    _ ≤ (2 *
          ((d : ℝ) ^ 2 * ‖a - a0‖ * (‖a‖ + ‖a0‖) *
            ‖uPlus‖ * ‖vPlus‖) +
        2 * ((d : ℝ) ^ 2 * ‖a - a0‖ * (‖a‖ + ‖a0‖) *
          ‖uMinus‖ * ‖vMinus‖)) / S := by
      apply div_le_div_of_nonneg_right _ hS.le
      gcongr
      · exact norm_plantedLinearCross_sub_le a a0 uPlus vPlus
      · exact norm_plantedLinearCross_sub_le a a0 uMinus vMinus
    _ = 2 * (d : ℝ) ^ 2 * ‖a - a0‖ * (‖a‖ + ‖a0‖) / S *
        (‖uPlus‖ * ‖vPlus‖ + ‖uMinus‖ * ‖vMinus‖) := by
      ring

/-- The raw seed linearization is precisely the normalized difference of the
two cross terms controlled above. -/
theorem plantedEquationLinear_eq_normalized_crosses {n : ℕ}
    (r : PlantedRow n) (s : ℝ) (b : ℂ) (z t : Signal n) :
    plantedEquationLinear r s b z t =
      (2 * (plantedLinearCross (plantedColumn r)
        (factorPlus (n := n) 0 0 0) (plusDirection s b z)).re -
        2 * (plantedLinearCross (plantedColumn r)
          (factorMinus (n := n) 0 0) (minusDirection s t)).re) / r.radial := by
  rw [plantedEquationLinear_raw]
  rfl

/-- Deterministic rowwise stability of the seed linearization under replacing
the actual planted row by its coupled zero-imbalance reference row. -/
theorem abs_plantedEquationLinear_sub_zeroImbalance_le {n : ℕ}
    (r : PlantedRow n) (s : ℝ) (b : ℂ) (z t : Signal n) :
    |plantedEquationLinear r s b z t -
        plantedEquationLinear r.zeroImbalance s b z t| ≤
      2 * ((n + 2 : ℕ) : ℝ) ^ 2 *
        ‖plantedColumn r - plantedColumn r.zeroImbalance‖ *
          (‖plantedColumn r‖ + ‖plantedColumn r.zeroImbalance‖) / r.radial *
        (‖factorPlus (n := n) 0 0 0‖ * ‖plusDirection s b z‖ +
          ‖factorMinus (n := n) 0 0‖ * ‖minusDirection s t‖) := by
  rw [plantedEquationLinear_eq_normalized_crosses,
    plantedEquationLinear_eq_normalized_crosses]
  change
    |((2 * (plantedLinearCross (plantedColumn r)
        (factorPlus (n := n) 0 0 0) (plusDirection s b z)).re -
        2 * (plantedLinearCross (plantedColumn r)
          (factorMinus (n := n) 0 0) (minusDirection s t)).re) / r.radial) -
      ((2 * (plantedLinearCross (plantedColumn r.zeroImbalance)
        (factorPlus (n := n) 0 0 0) (plusDirection s b z)).re -
        2 * (plantedLinearCross (plantedColumn r.zeroImbalance)
          (factorMinus (n := n) 0 0) (minusDirection s t)).re) / r.radial)| ≤ _
  exact abs_normalized_plantedLinearCross_sub_le r.radial r.radial_pos
    (plantedColumn r) (plantedColumn r.zeroImbalance)
    (factorPlus (n := n) 0 0 0) (plusDirection s b z)
    (factorMinus (n := n) 0 0) (minusDirection s t)

/-- A source-specific square-root comparison.  The hard constraint
`|xi| ≤ 1` makes the two perturbed first-coordinate amplitudes Lipschitz in
the imbalance relative to their balanced amplitude. -/
theorem abs_sqrt_radial_one_add_sub_le {S ξ : ℝ}
    (hS : 0 < S) (hξ : |ξ| ≤ 1) :
    |Real.sqrt (S * (1 + ξ) / 2) - Real.sqrt (S / 2)| ≤
      Real.sqrt (S / 2) * |ξ| := by
  have hξ0 : 0 ≤ 1 + ξ := by linarith [neg_abs_le ξ]
  have hunit : |Real.sqrt (1 + ξ) - 1| ≤ |ξ| := by
    apply abs_le.mpr
    constructor
    · have h := (Real.le_sqrt (by linarith : 0 ≤ 1 - |ξ|) hξ0).mpr
        (show (1 - |ξ|) ^ 2 ≤ 1 + ξ by
          nlinarith [abs_nonneg ξ, neg_abs_le ξ, mul_nonneg (abs_nonneg ξ) (sub_nonneg.mpr hξ)])
      linarith
    · have h := (Real.sqrt_le_iff).mpr
        ⟨(by positivity : 0 ≤ 1 + |ξ|), show 1 + ξ ≤ (1 + |ξ|) ^ 2 by
          nlinarith [le_abs_self ξ, abs_nonneg ξ]⟩
      linarith
  rw [show S * (1 + ξ) / 2 = (S / 2) * (1 + ξ) by ring,
    Real.sqrt_mul (by positivity),
    show Real.sqrt (S / 2) * Real.sqrt (1 + ξ) - Real.sqrt (S / 2) =
      Real.sqrt (S / 2) * (Real.sqrt (1 + ξ) - 1) by ring,
    abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left hunit (Real.sqrt_nonneg _)

/-- The corresponding comparison for the second planted amplitude. -/
theorem abs_sqrt_radial_one_sub_sub_le {S ξ : ℝ}
    (hS : 0 < S) (hξ : |ξ| ≤ 1) :
    |Real.sqrt (S * (1 - ξ) / 2) - Real.sqrt (S / 2)| ≤
      Real.sqrt (S / 2) * |ξ| := by
  have h := abs_sqrt_radial_one_add_sub_le (S := S) (ξ := -ξ) hS
    (by simpa using hξ)
  simpa [sub_eq_add_neg, abs_neg] using h

/-- Multiplication by a common planted phase is an isometry on the real
amplitude difference. -/
theorem norm_real_phase_mul_sub (x y α : ℝ) :
    ‖((x : ℂ) * Complex.exp (α * Complex.I)) -
        ((y : ℂ) * Complex.exp (α * Complex.I))‖ = |x - y| := by
  have hrewrite :
      ((x : ℂ) * Complex.exp (α * Complex.I)) -
          ((y : ℂ) * Complex.exp (α * Complex.I)) =
        ((x - y : ℝ) : ℂ) * Complex.exp (α * Complex.I) := by
    push_cast
    ring
  rw [hrewrite, norm_mul, Complex.norm_real,
    Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs]

/-- The coupled planted columns differ only in their first two entries, and
their ambient finite-coordinate norm is linearly controlled by the source
imbalance. -/
theorem norm_plantedColumn_sub_zeroImbalance_le {n : ℕ}
    (r : PlantedRow n) :
    ‖plantedColumn r - plantedColumn r.zeroImbalance‖ ≤
      Real.sqrt (r.radial / 2) * |r.imbalance| := by
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))).2 ?_
  intro i
  by_cases hi0 : i.1 = 0
  · have hindex : i = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext hi0
    subst i
    simp only [Pi.sub_apply, plantedColumn, PlantedRow.zeroImbalance]
    simp only [add_zero, mul_one]
    change ‖((Real.sqrt (r.radial * (1 + r.imbalance) / 2) : ℂ) *
        Complex.exp (r.phaseOne * Complex.I)) -
        ((Real.sqrt (r.radial / 2) : ℂ) *
          Complex.exp (r.phaseOne * Complex.I))‖ ≤ _
    rw [norm_real_phase_mul_sub]
    exact abs_sqrt_radial_one_add_sub_le r.radial_pos r.imbalance_le_one
  · by_cases hi1 : i.1 = 1
    · have hindex : i = ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩ :=
        Fin.ext hi1
      subst i
      simp only [Pi.sub_apply, plantedColumn, PlantedRow.zeroImbalance]
      simp only [sub_zero, mul_one]
      change ‖((Real.sqrt (r.radial * (1 - r.imbalance) / 2) : ℂ) *
          Complex.exp (r.phaseTwo * Complex.I)) -
          ((Real.sqrt (r.radial / 2) : ℂ) *
            Complex.exp (r.phaseTwo * Complex.I))‖ ≤ _
      rw [norm_real_phase_mul_sub]
      exact abs_sqrt_radial_one_sub_sub_le r.radial_pos r.imbalance_le_one
    · simp [plantedColumn, PlantedRow.zeroImbalance, joinTwo, hi0, hi1]
      positivity

/-- The ambient finite-coordinate norm of a planted column is controlled by
the explicit radial-plus-tail energy that appears in the source good event. -/
theorem norm_plantedColumn_le_sqrt_radial_tail {n : ℕ}
    (r : PlantedRow n) :
    ‖plantedColumn r‖ ≤
      Real.sqrt (r.radial + squaredEuclideanNorm r.tail) := by
  have henergy : 0 ≤ r.radial + squaredEuclideanNorm r.tail := by
    exact add_nonneg r.radial_pos.le (squaredEuclideanNorm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  calc
    ‖plantedColumn r‖ ^ 2 ≤ squaredEuclideanNorm (plantedColumn r) :=
      norm_sq_le_squaredEuclideanNorm _
    _ = r.radial + squaredEuclideanNorm r.tail :=
      squaredEuclideanNorm_plantedColumn r
    _ = (Real.sqrt (r.radial + squaredEuclideanNorm r.tail)) ^ 2 :=
      (Real.sq_sqrt henergy).symm

/-- The same energy bound holds for the zero-imbalance reference column. -/
theorem norm_plantedColumn_zeroImbalance_le_sqrt_radial_tail {n : ℕ}
    (r : PlantedRow n) :
    ‖plantedColumn r.zeroImbalance‖ ≤
      Real.sqrt (r.radial + squaredEuclideanNorm r.tail) := by
  exact norm_plantedColumn_le_sqrt_radial_tail r.zeroImbalance

/-- On the radial-plus-tail-energy event used in (3.22), the row factor
appearing in the imbalance comparison has a simple explicit bound. -/
theorem plantedImbalanceCoefficient_le_of_radial_tail_bound {n : ℕ}
    (r : PlantedRow n) {δ B : ℝ} (hδ : 0 < δ)
    (hradial : δ ≤ r.radial)
    (henergy : r.radial + squaredEuclideanNorm r.tail ≤ B) :
    Real.sqrt (r.radial / 2) *
        (‖plantedColumn r‖ + ‖plantedColumn r.zeroImbalance‖) / r.radial ≤
      2 * B / δ := by
  have htail : 0 ≤ squaredEuclideanNorm r.tail :=
    squaredEuclideanNorm_nonneg _
  have hE : 0 ≤ r.radial + squaredEuclideanNorm r.tail :=
    add_nonneg r.radial_pos.le htail
  have hB : 0 ≤ B := le_trans hE henergy
  have hradial_le_B : r.radial ≤ B := by linarith
  have hhalf_radial_le_B : r.radial / 2 ≤ B := by linarith
  have hsqrt_half : Real.sqrt (r.radial / 2) ≤ Real.sqrt B :=
    Real.sqrt_le_sqrt hhalf_radial_le_B
  have hsqrt_energy :
      Real.sqrt (r.radial + squaredEuclideanNorm r.tail) ≤ Real.sqrt B :=
    Real.sqrt_le_sqrt henergy
  have hcol : ‖plantedColumn r‖ ≤ Real.sqrt B :=
    (norm_plantedColumn_le_sqrt_radial_tail r).trans hsqrt_energy
  have hcol0 : ‖plantedColumn r.zeroImbalance‖ ≤ Real.sqrt B :=
    (norm_plantedColumn_zeroImbalance_le_sqrt_radial_tail r).trans hsqrt_energy
  have hsum :
      ‖plantedColumn r‖ + ‖plantedColumn r.zeroImbalance‖ ≤
        2 * Real.sqrt B := by
    linarith
  have hnum :
      Real.sqrt (r.radial / 2) *
          (‖plantedColumn r‖ + ‖plantedColumn r.zeroImbalance‖) ≤ 2 * B := by
    calc
      Real.sqrt (r.radial / 2) *
          (‖plantedColumn r‖ + ‖plantedColumn r.zeroImbalance‖) ≤
          Real.sqrt B * (2 * Real.sqrt B) := by
        exact mul_le_mul hsqrt_half hsum
          (by positivity) (Real.sqrt_nonneg _)
      _ = 2 * B := by
        nlinarith [Real.sq_sqrt hB]
  calc
    Real.sqrt (r.radial / 2) *
        (‖plantedColumn r‖ + ‖plantedColumn r.zeroImbalance‖) / r.radial ≤
        (2 * B) / r.radial :=
      div_le_div_of_nonneg_right hnum r.radial_pos.le
    _ ≤ 2 * B / δ :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hB) hδ hradial

/-- The previous rowwise comparison with the coupled-column estimate
inserted.  This is the requested explicit `|xi|` perturbation scale. -/
theorem abs_plantedEquationLinear_sub_zeroImbalance_le_imbalance {n : ℕ}
    (r : PlantedRow n) (s : ℝ) (b : ℂ) (z t : Signal n) :
    |plantedEquationLinear r s b z t -
        plantedEquationLinear r.zeroImbalance s b z t| ≤
      2 * ((n + 2 : ℕ) : ℝ) ^ 2 *
        (Real.sqrt (r.radial / 2) * |r.imbalance|) *
          (‖plantedColumn r‖ + ‖plantedColumn r.zeroImbalance‖) / r.radial *
        (‖factorPlus (n := n) 0 0 0‖ * ‖plusDirection s b z‖ +
          ‖factorMinus (n := n) 0 0‖ * ‖minusDirection s t‖) := by
  apply (abs_plantedEquationLinear_sub_zeroImbalance_le r s b z t).trans
  gcongr
  · exact r.radial_pos.le
  · exact norm_plantedColumn_sub_zeroImbalance_le r

/-- Comparison with Li's frozen form (3.21): the actual planted-equation
linearization differs from it by an explicitly `|xi|`-proportional rowwise
quantity. -/
theorem abs_plantedEquationLinear_sub_sourceRowJacobianForm_le {n : ℕ}
    (r : PlantedRow n) (σ β γ : ℝ) (p q : Signal n) :
    |plantedEquationLinear r σ ((β : ℂ) + γ * Complex.I) p q -
        sourceRowJacobianForm r σ β γ p q| ≤
      2 * ((n + 2 : ℕ) : ℝ) ^ 2 *
        (Real.sqrt (r.radial / 2) * |r.imbalance|) *
          (‖plantedColumn r‖ + ‖plantedColumn r.zeroImbalance‖) / r.radial *
        (‖factorPlus (n := n) 0 0 0‖ *
            ‖plusDirection σ ((β : ℂ) + γ * Complex.I) p‖ +
          ‖factorMinus (n := n) 0 0‖ * ‖minusDirection σ q‖) := by
  rw [← plantedEquationLinear_zeroImbalance_source_formula r σ β γ p q]
  exact abs_plantedEquationLinear_sub_zeroImbalance_le_imbalance r σ
    ((β : ℂ) + γ * Complex.I) p q

/-- Source-good-event form of the `J_epsilon - J_0` row comparison.  The
assumptions are exactly the radial/tail-energy and imbalance parts of the
source construction; the final direction factor is left explicit so it can
be assembled into the matrix norm in a later step. -/
theorem abs_plantedEquationLinear_sub_sourceRowJacobianForm_le_of_radial_tail
    {n : ℕ} (r : PlantedRow n) (σ β γ : ℝ) (p q : Signal n)
    {δ B ε : ℝ} (hδ : 0 < δ) (hradial : δ ≤ r.radial)
    (henergy : r.radial + squaredEuclideanNorm r.tail ≤ B)
    (himbalance : |r.imbalance| ≤ ε) :
    |plantedEquationLinear r σ ((β : ℂ) + γ * Complex.I) p q -
        sourceRowJacobianForm r σ β γ p q| ≤
      4 * ((n + 2 : ℕ) : ℝ) ^ 2 * B / δ * ε *
        (‖factorPlus (n := n) 0 0 0‖ *
            ‖plusDirection σ ((β : ℂ) + γ * Complex.I) p‖ +
          ‖factorMinus (n := n) 0 0‖ * ‖minusDirection σ q‖) := by
  let C := Real.sqrt (r.radial / 2) *
    (‖plantedColumn r‖ + ‖plantedColumn r.zeroImbalance‖) / r.radial
  let V := ‖factorPlus (n := n) 0 0 0‖ *
      ‖plusDirection σ ((β : ℂ) + γ * Complex.I) p‖ +
    ‖factorMinus (n := n) 0 0‖ * ‖minusDirection σ q‖
  have hC : C ≤ 2 * B / δ :=
    plantedImbalanceCoefficient_le_of_radial_tail_bound r hδ hradial henergy
  have hr := r.radial_pos
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hCbound : 0 ≤ 2 * B / δ := hC0.trans hC
  have hV : 0 ≤ V := by dsimp [V]; positivity
  calc
    _ ≤ 2 * ((n + 2 : ℕ) : ℝ) ^ 2 *
        (Real.sqrt (r.radial / 2) * |r.imbalance|) *
          (‖plantedColumn r‖ + ‖plantedColumn r.zeroImbalance‖) / r.radial * V :=
      abs_plantedEquationLinear_sub_sourceRowJacobianForm_le r σ β γ p q
    _ = 2 * ((n + 2 : ℕ) : ℝ) ^ 2 * C * |r.imbalance| * V := by dsimp [C]; ring
    _ ≤ 2 * ((n + 2 : ℕ) : ℝ) ^ 2 * (2 * B / δ) * ε * V := by gcongr
    _ = _ := by ring

end NLA.FR05
