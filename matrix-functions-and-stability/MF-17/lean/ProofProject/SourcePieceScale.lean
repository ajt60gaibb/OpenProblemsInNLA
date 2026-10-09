import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The source's doubly exponential piece scales

The definitions retain the exact base and exponent of the source. Elementary
geometric bounds are consequences of the exact recurrence.
-/

noncomputable section

namespace ProofProject

def sourcePieceScale (q : ℕ) : ℝ := (16 : ℝ) ^ ((4 / 3 : ℝ) ^ q)

def sourcePieceLambda (q : ℕ) : ℝ := sourcePieceScale q ^ (-1 / 2 : ℝ)

@[simp] theorem sourcePieceScale_zero : sourcePieceScale 0 = 16 := by
  simp [sourcePieceScale]

theorem sourcePieceScale_pos (q : ℕ) : 0 < sourcePieceScale q :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem sourcePieceScale_ge_sixteen (q : ℕ) : 16 ≤ sourcePieceScale q := by
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 16)
    (one_le_pow₀ (n := q) (by norm_num : (1 : ℝ) ≤ 4 / 3))
  simpa only [Real.rpow_one, sourcePieceScale] using h

theorem sourcePieceScale_succ (q : ℕ) :
    sourcePieceScale (q + 1) = sourcePieceScale q ^ (4 / 3 : ℝ) := by
  simp only [sourcePieceScale, pow_succ, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 16)]

theorem sourcePieceScale_monotone : Monotone sourcePieceScale := by
  intro q r hqr
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4 / 3) hqr)

/-- Even the coarse doubling bound is uniform from the first source piece. -/
theorem sourcePieceScale_double_le (q : ℕ) :
    2 * sourcePieceScale q ≤ sourcePieceScale (q + 1) := by
  have hthird : (2 : ℝ) ≤ (16 : ℝ) ^ (1 / 3 : ℝ) := by
    rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by ring,
      Real.le_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  calc
    _ ≤ (16 : ℝ) ^ (1 / 3 : ℝ) * sourcePieceScale q :=
      mul_le_mul_of_nonneg_right hthird (sourcePieceScale_pos q).le
    _ ≤ sourcePieceScale (q + 1) := by
      rw [sourcePieceScale, sourcePieceScale, ← Real.rpow_add (by norm_num : (0 : ℝ) < 16)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h := one_le_pow₀ (n := q) (by norm_num : (1 : ℝ) ≤ 4 / 3)
      rw [pow_succ]
      nlinarith

theorem sourcePieceScale_strictMono : StrictMono sourcePieceScale := by
  apply strictMono_nat_of_lt_succ
  intro q
  have h := sourcePieceScale_double_le q
  have hp := sourcePieceScale_pos q
  linarith

theorem sourcePieceScale_geometric_lower (q : ℕ) :
    16 * (2 : ℝ) ^ q ≤ sourcePieceScale q := by
  induction q with
  | zero => simp
  | succ q ih =>
      have h := sourcePieceScale_double_le q
      rw [pow_succ]
      nlinarith

theorem log_sourcePieceScale (q : ℕ) :
    Real.log (sourcePieceScale q) = (4 / 3 : ℝ) ^ q * Real.log 16 :=
  Real.log_rpow (by norm_num) _

theorem sourcePieceLambda_pos (q : ℕ) : 0 < sourcePieceLambda q :=
  Real.rpow_pos_of_pos (sourcePieceScale_pos q) _

theorem sourcePieceLambda_eq_inv_sqrt (q : ℕ) :
    sourcePieceLambda q = 1 / Real.sqrt (sourcePieceScale q) := by
  rw [sourcePieceLambda, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg (sourcePieceScale_pos q).le, ← Real.sqrt_eq_rpow, one_div]

theorem sourcePieceLambda_antitone : Antitone sourcePieceLambda := by
  intro q r hqr
  exact Real.rpow_le_rpow_of_nonpos (sourcePieceScale_pos q)
    (sourcePieceScale_monotone hqr) (by norm_num)

theorem sourcePieceLambda_le_quarter (q : ℕ) : sourcePieceLambda q ≤ 1 / 4 := by
  calc
    _ ≤ sourcePieceLambda 0 := sourcePieceLambda_antitone (Nat.zero_le q)
    _ = 1 / 4 := by rw [sourcePieceLambda_eq_inv_sqrt, sourcePieceScale_zero]; norm_num

end ProofProject
