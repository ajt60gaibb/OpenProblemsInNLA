/-
The explicit Jacobian row formula from equation (3.21) of the frozen source.

The polynomial factor chart is used for the local coordinates, but this file
checks that its linearized normalized planted equation has exactly the
phase/Gaussian form used in Lemmas 3.6 and 3.7.
-/
import NLA.FR05.Geometry.Planted

set_option autoImplicit false
open scoped BigOperators ComplexConjugate Matrix
noncomputable section

namespace NLA.FR05

theorem quadraticForm_vecMulVec_cross {d : ℕ} (a u v : Signal d) :
    quadraticForm (Matrix.vecMulVec u (star v)) a =
      (star a ⬝ᵥ u) * star (star a ⬝ᵥ v) := by
  rw [quadraticForm, Matrix.vecMulVec_mulVec]
  rw [op_smul_eq_smul, dotProduct_smul, Matrix.star_dotProduct]
  ring

theorem factorChartLinear_quadraticForm_re {n : ℕ}
    (a : Signal (n + 2)) (s : ℝ) (b : ℂ) (z t : Signal n) :
    (quadraticForm (factorChartLinear s b z t) a).re =
      2 * ((star a ⬝ᵥ factorPlus (n := n) 0 0 0) *
        star (star a ⬝ᵥ plusDirection s b z)).re -
      2 * ((star a ⬝ᵥ factorMinus (n := n) 0 0) *
        star (star a ⬝ᵥ minusDirection s t)).re := by
  unfold factorChartLinear
  rw [quadraticForm_sub, quadraticForm_sub, quadraticForm_add]
  rw [quadraticForm_vecMulVec_cross, quadraticForm_vecMulVec_cross,
    quadraticForm_vecMulVec_cross, quadraticForm_vecMulVec_cross]
  have hplus :
      (star a ⬝ᵥ plusDirection s b z) *
          star (star a ⬝ᵥ factorPlus (n := n) 0 0 0) =
        star ((star a ⬝ᵥ factorPlus (n := n) 0 0 0) *
          star (star a ⬝ᵥ plusDirection s b z)) := by
    rw [star_mul, star_star]
  have hminus :
      (star a ⬝ᵥ minusDirection s t) *
          star (star a ⬝ᵥ factorMinus (n := n) 0 0) =
        star ((star a ⬝ᵥ factorMinus (n := n) 0 0) *
          star (star a ⬝ᵥ minusDirection s t)) := by
    rw [star_mul, star_star]
  rw [hplus, hminus]
  simp
  ring

/-- The coordinates after the two planted entries. -/
def tailPart {n : ℕ} (a : Signal (n + 2)) : Signal n :=
  fun j ↦ a ⟨j.1 + 2, by lia⟩

theorem star_dotProduct_joinTwo {n : ℕ}
    (u v U V : ℂ) (w W : Signal n) :
    star (joinTwo u v w) ⬝ᵥ joinTwo U V W =
      star u * U + star v * V + star w ⬝ᵥ W := by
  simp only [dotProduct, Pi.star_apply]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, joinTwo]
  rw [Fin.sum_univ_succ]
  simp
  ring

theorem joinTwo_expand {n : ℕ} (a : Signal (n + 2)) :
    a = joinTwo (a ⟨0, Nat.zero_lt_succ _⟩)
      (a ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (tailPart a) := by
  funext i
  by_cases hi0 : i.1 = 0
  · have h : i = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext hi0
    subst i
    simp [joinTwo]
  · by_cases hi1 : i.1 = 1
    · have h : i = ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩ := Fin.ext hi1
      subst i
      simp [joinTwo]
    · have hi2 : 2 ≤ i.1 := by lia
      simp only [joinTwo, dite_false, hi0, hi1, tailPart]
      apply congrArg a
      apply Fin.ext
      exact (Nat.sub_add_cancel hi2).symm

theorem star_dotProduct_factorPlus_zero {n : ℕ}
    (a : Signal (n + 2)) :
    star a ⬝ᵥ factorPlus (n := n) 0 0 0 =
      star (a ⟨0, Nat.zero_lt_succ _⟩) := by
  have h := star_dotProduct_joinTwo
      (a ⟨0, Nat.zero_lt_succ _⟩)
      (a ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)
      (1 : ℂ) 0 (tailPart a) (0 : Signal n)
  rw [← joinTwo_expand a] at h
  simpa [factorPlus] using h

theorem star_dotProduct_factorMinus_zero {n : ℕ}
    (a : Signal (n + 2)) :
    star a ⬝ᵥ factorMinus (n := n) 0 0 =
      star (a ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) := by
  have h := star_dotProduct_joinTwo
      (a ⟨0, Nat.zero_lt_succ _⟩)
      (a ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)
      (0 : ℂ) 1 (tailPart a) (0 : Signal n)
  rw [← joinTwo_expand a] at h
  simpa [factorMinus] using h

theorem star_dotProduct_plusDirection {n : ℕ}
    (a : Signal (n + 2)) (s : ℝ) (b : ℂ) (z : Signal n) :
    star a ⬝ᵥ plusDirection s b z =
      star (a ⟨0, Nat.zero_lt_succ _⟩) * (s / 4 : ℂ) +
        star (a ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) * star b +
          star (tailPart a) ⬝ᵥ z := by
  have h := star_dotProduct_joinTwo
      (a ⟨0, Nat.zero_lt_succ _⟩)
      (a ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)
      (s / 4 : ℂ) (star b) (tailPart a) z
  rw [← joinTwo_expand a] at h
  simpa [plusDirection] using h

theorem star_dotProduct_minusDirection {n : ℕ}
    (a : Signal (n + 2)) (s : ℝ) (t : Signal n) :
    star a ⬝ᵥ minusDirection s t =
      star (a ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) * (-s / 4 : ℂ) -
        star (tailPart a) ⬝ᵥ t := by
  have h := star_dotProduct_joinTwo
      (a ⟨0, Nat.zero_lt_succ _⟩)
      (a ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)
      (0 : ℂ) (-s / 4 : ℂ) (tailPart a) (-t)
  rw [← joinTwo_expand a] at h
  simpa [minusDirection, sub_eq_add_neg] using h

theorem tailPart_plantedColumn {n : ℕ} (r : PlantedRow n) :
    tailPart (plantedColumn r) = r.tail := by
  funext j
  simp [tailPart, plantedColumn, joinTwo]

theorem plantedColumn_first_balanced {n : ℕ} (r : PlantedRow n)
    (hbalanced : r.imbalance = 0) :
    plantedColumn r ⟨0, Nat.zero_lt_succ _⟩ =
      (Real.sqrt (r.radial / 2) : ℂ) * Complex.exp (r.phaseOne * Complex.I) := by
  simp [plantedColumn, hbalanced]

theorem plantedColumn_second_balanced {n : ℕ} (r : PlantedRow n)
    (hbalanced : r.imbalance = 0) :
    plantedColumn r ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩ =
      (Real.sqrt (r.radial / 2) : ℂ) * Complex.exp (r.phaseTwo * Complex.I) := by
  simp [plantedColumn, hbalanced]

theorem sqrt_scale {S : ℝ} (hS : 0 < S) :
    2 * (Real.sqrt S / Real.sqrt 2) / S = Real.sqrt 2 / Real.sqrt S := by
  have hS0 : 0 ≤ S := hS.le
  have hsqrtS : Real.sqrt S ≠ 0 := by positivity
  have hsqrt2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith [Real.sq_sqrt hS0, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem exp_neg_real_mul_I (α : ℝ) :
    Complex.exp (-((α : ℂ) * Complex.I)) =
      (Real.cos α : ℂ) - (Real.sin α : ℂ) * Complex.I := by
  rw [show -((α : ℂ) * Complex.I) = ((-α : ℝ) : ℂ) * Complex.I by
      push_cast
      ring,
    Complex.exp_ofReal_mul_I]
  simp [Real.cos_neg, Real.sin_neg]
  ring

theorem exp_real_mul_I (α : ℝ) :
    Complex.exp ((α : ℂ) * Complex.I) =
      (Real.cos α : ℂ) + (Real.sin α : ℂ) * Complex.I := by
  rw [Complex.exp_ofReal_mul_I]

/-- The phase difference used to express the random Jacobian row. -/
def phaseGap {n : ℕ} (r : PlantedRow n) : ℝ :=
  r.phaseTwo - r.phaseOne

/-- Rotate the complex Gaussian tail by the first planted phase. -/
def phaseNormalizedTail {n : ℕ} (r : PlantedRow n) : Signal n :=
  (Complex.exp ((-r.phaseOne : ℂ) * Complex.I)) • r.tail

/-- The row expression on the right-hand side of equation (3.21). -/
def sourceRowJacobianForm {n : ℕ} (r : PlantedRow n)
    (σ β γ : ℝ) (p q : Signal n) : ℝ :=
  σ / 2 + β * Real.cos (phaseGap r) - γ * Real.sin (phaseGap r) +
    Real.sqrt (2 / r.radial) *
      (star (phaseNormalizedTail r) ⬝ᵥ
        (p + Complex.exp ((phaseGap r : ℂ) * Complex.I) • q)).re

theorem plantedEquationLinear_raw {n : ℕ} (r : PlantedRow n)
    (s : ℝ) (b : ℂ) (z t : Signal n) :
    plantedEquationLinear r s b z t =
      (2 * ((star (plantedColumn r) ⬝ᵥ factorPlus (n := n) 0 0 0) *
        star (star (plantedColumn r) ⬝ᵥ plusDirection s b z)).re -
      2 * ((star (plantedColumn r) ⬝ᵥ factorMinus (n := n) 0 0) *
        star (star (plantedColumn r) ⬝ᵥ minusDirection s t)).re) / r.radial := by
  unfold plantedEquationLinear
  rw [factorChartLinear_quadraticForm_re]

/-- At zero imbalance, the linearization of one planted equation is exactly
Li's phase/Gaussian formula (3.21). -/
theorem plantedEquationLinear_source_formula {n : ℕ} (r : PlantedRow n)
    (hbalanced : r.imbalance = 0) (σ β γ : ℝ) (p q : Signal n) :
    plantedEquationLinear r σ ((β : ℂ) + γ * Complex.I) p q =
      sourceRowJacobianForm r σ β γ p q := by
  rw [plantedEquationLinear_raw,
    star_dotProduct_factorPlus_zero,
    star_dotProduct_factorMinus_zero,
    star_dotProduct_plusDirection,
    star_dotProduct_minusDirection,
    tailPart_plantedColumn,
    plantedColumn_first_balanced r hbalanced,
    plantedColumn_second_balanced r hbalanced]
  simp [phaseGap, phaseNormalizedTail, sourceRowJacobianForm]
  rw [exp_neg_real_mul_I r.phaseOne]
  have hgap : ((r.phaseTwo - r.phaseOne : ℝ) : ℂ) =
      (r.phaseTwo : ℂ) - (r.phaseOne : ℂ) := by
    push_cast
    ring
  rw [← hgap, exp_real_mul_I]
  norm_num
  rw [← hgap]
  simp only [Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  rw [Real.cos_sub, Real.sin_sub]
  rw [← sqrt_scale r.radial_pos]
  set c : ℝ := Real.sqrt r.radial / Real.sqrt 2 with hc
  have hc_sq : c ^ 2 = r.radial / 2 := by
    rw [hc]
    field_simp
    nlinarith [Real.sq_sqrt r.radial_pos.le,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have htrigOne := Real.cos_sq_add_sin_sq r.phaseOne
  have htrigTwo := Real.cos_sq_add_sin_sq r.phaseTwo
  ring_nf
  have hcosOne : Real.cos r.phaseOne ^ 2 = 1 - Real.sin r.phaseOne ^ 2 := by
    linarith [htrigOne]
  have hcosTwo : Real.cos r.phaseTwo ^ 2 = 1 - Real.sin r.phaseTwo ^ 2 := by
    linarith [htrigTwo]
  rw [hcosOne, hcosTwo, hc_sq]
  field_simp [r.radial_pos.ne']
  ring

end NLA.FR05
