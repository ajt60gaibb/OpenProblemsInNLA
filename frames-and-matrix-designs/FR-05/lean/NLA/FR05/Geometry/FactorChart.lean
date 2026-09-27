import NLA.FR05.Geometry.Obstruction
import Mathlib.Analysis.InnerProductSpace.Basic

/-! ## FactorChart -/

section

/-
An alternative local rank-two chart for the planted-law argument in §3.4.

The source uses a Schur-complement chart.  Near its seed, the polynomial
factor chart below has the same real coordinates and the same first-order derivatives,
but writes every matrix directly as `xxᴴ - yyᴴ`.  This removes a separate
spectral/inertia conversion at the end of the proof: a zero of the
measurement equations immediately gives two inequivalent signals with equal
measurements.
-/


set_option autoImplicit false
open scoped BigOperators ComplexConjugate Matrix
noncomputable section

namespace NLA.FR05

/-- Assemble two distinguished coordinates and an `n`-coordinate tail into a
signal of ambient dimension `n + 2`. -/
def joinTwo {n : ℕ} (u v : ℂ) (w : Signal n) : Signal (n + 2) :=
  fun i =>
    if h0 : i.1 = 0 then u
    else if h1 : i.1 = 1 then v
    else w ⟨i.1 - 2, by lia⟩

@[simp]
theorem joinTwo_zero {n : ℕ} (u v : ℂ) (w : Signal n) :
    joinTwo u v w 0 = u := by
  simp [joinTwo]

@[simp]
theorem joinTwo_one {n : ℕ} (u v : ℂ) (w : Signal n) :
    joinTwo u v w 1 = v := by
  simp [joinTwo]

/-- Positive factor in the local polynomial chart.  The `s/4` choice makes
the differential at the seed agree coordinate-for-coordinate with (3.19),
while avoiding a transcendental coordinate change. -/
def factorPlus {n : ℕ} (s : ℝ) (b : ℂ) (z : Signal n) : Signal (n + 2) :=
  joinTwo (1 + s / 4) (star b) z

/-- Negative factor in the local polynomial chart. -/
def factorMinus {n : ℕ} (s : ℝ) (t : Signal n) : Signal (n + 2) :=
  joinTwo 0 (1 - s / 4) (-t)

/-- A factorized rank-at-most-two Hermitian chart through
`diag(1,-1,0,...)`. -/
def factorChart {n : ℕ} (s : ℝ) (b : ℂ) (z t : Signal n) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
  rankOneDifference (factorPlus s b z) (factorMinus s t)

/-- The two factors in the chart are never related by a global phase: their
first coordinates are respectively nonzero and zero. -/
theorem factorPlus_not_globallyPhased_factorMinus {n : ℕ}
    (s : ℝ) (b : ℂ) (z t : Signal n) (hs : |s| ≤ 1) :
    ¬ GloballyPhased (factorPlus s b z) (factorMinus s t) := by
  intro hphase
  obtain ⟨θ, hθ⟩ := hphase
  have hzero := congrFun hθ ⟨0, Nat.zero_lt_succ _⟩
  have hs' : -1 ≤ s ∧ s ≤ 1 := abs_le.mp hs
  have hpositive : 0 < 1 + s / 4 := by
    linarith
  have hnonzero :
      Complex.exp (θ * Complex.I) * (1 + s / 4 : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact Complex.exp_ne_zero _
    · exact_mod_cast hpositive.ne'
  apply hnonzero
  simpa [factorPlus, factorMinus, joinTwo] using hzero.symm

/-- The exact deterministic endpoint of the planted argument for the factor
chart.  A simultaneous zero of the real quadratic equations refutes the
original all-signal phase-retrieval predicate. -/
theorem factorChart_not_phaseRetrievalInjective_of_quadraticForm_zero
    {m n : ℕ} (A : Frame m (n + 2))
    (s : ℝ) (b : ℂ) (z t : Signal n)
    (hs : |s| ≤ 1)
    (hzero : ∀ i, quadraticForm (factorChart s b z t) (conjugateRow A i) = 0) :
    ¬ PhaseRetrievalInjective A := by
  apply not_phaseRetrievalInjective_of_rankOneDifference_quadraticForm_eq_zero
    A (factorPlus s b z) (factorMinus s t)
  · simpa [factorChart] using hzero
  · exact factorPlus_not_globallyPhased_factorMinus s b z t hs

@[simp]
theorem factorPlus_zero {n : ℕ} :
    factorPlus (n := n) 0 0 0 =
      standardBasis (firstCoordinate (n + 2) (by lia)) := by
  funext i
  unfold factorPlus joinTwo standardBasis firstCoordinate
  norm_num
  grind [Fin.ext_iff]

@[simp]
theorem factorMinus_zero {n : ℕ} :
    factorMinus (n := n) 0 0 =
      standardBasis (secondCoordinate (n + 2) (by lia)) := by
  funext i
  simp only [factorMinus, joinTwo, standardBasis, secondCoordinate, Complex.ofReal_zero,
    zero_div, sub_zero, neg_zero, Pi.zero_apply, Fin.ext_iff]
  split_ifs <;> simp_all

end NLA.FR05

end

end

/-! ## FactorTaylor -/

section

/-
Exact first- and second-order algebra for the polynomial factor chart.
This provides the Jacobian layer of the planted proof without introducing an
unnecessary transcendental coordinate change.
-/


set_option autoImplicit false
open scoped BigOperators ComplexConjugate Matrix
noncomputable section

namespace NLA.FR05

/-- The positive factor's tangent vector at the seed. -/
def plusDirection {n : ℕ} (s : ℝ) (b : ℂ) (z : Signal n) : Signal (n + 2) :=
  joinTwo (s / 4) (star b) z

/-- The negative factor's tangent vector at the seed. -/
def minusDirection {n : ℕ} (s : ℝ) (t : Signal n) : Signal (n + 2) :=
  joinTwo 0 (-s / 4) (-t)

/-- Along every real ray of chart parameters, the positive factor is exactly
affine. -/
theorem factorPlus_scaled {n : ℕ} (r s : ℝ) (b : ℂ) (z : Signal n) :
    factorPlus (r * s) (r • b) (r • z) =
      factorPlus (n := n) 0 0 0 + r • plusDirection s b z := by
  funext i
  by_cases hi0 : i.1 = 0
  · simp [factorPlus, plusDirection, joinTwo, hi0]
    ring
  · by_cases hi1 : i.1 = 1
    · simp [factorPlus, plusDirection, joinTwo, hi1]
    · simp [factorPlus, plusDirection, joinTwo, hi0, hi1]

/-- Along every real ray of chart parameters, the negative factor is exactly
affine. -/
theorem factorMinus_scaled {n : ℕ} (r s : ℝ) (t : Signal n) :
    factorMinus (r * s) (r • t) =
      factorMinus (n := n) 0 0 + r • minusDirection s t := by
  funext i
  by_cases hi0 : i.1 = 0
  · simp [factorMinus, minusDirection, joinTwo, hi0]
  · by_cases hi1 : i.1 = 1
    · simp [factorMinus, minusDirection, joinTwo, hi1]
      ring
    · simp [factorMinus, minusDirection, joinTwo, hi0, hi1]

/-- The linear part of the factor chart along a parameter ray. -/
def factorChartLinear {n : ℕ} (s : ℝ) (b : ℂ) (z t : Signal n) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
  Matrix.vecMulVec (plusDirection s b z) (star (factorPlus (n := n) 0 0 0)) +
    Matrix.vecMulVec (factorPlus (n := n) 0 0 0) (star (plusDirection s b z)) -
      Matrix.vecMulVec (minusDirection s t) (star (factorMinus (n := n) 0 0)) -
        Matrix.vecMulVec (factorMinus (n := n) 0 0) (star (minusDirection s t))

/-- The quadratic remainder of the factor chart along a parameter ray. -/
def factorChartQuadratic {n : ℕ} (s : ℝ) (b : ℂ) (z t : Signal n) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
  rankOneDifference (plusDirection s b z) (minusDirection s t)

/-- An exact Taylor identity for the chart.  In particular, its first
derivative at the seed is `factorChartLinear`, and all remaining terms are
quadratic. -/
theorem factorChart_scaled_expansion {n : ℕ} (r s : ℝ) (b : ℂ) (z t : Signal n) :
    factorChart (r * s) (r • b) (r • z) (r • t) =
      factorChart (n := n) 0 0 0 0 + r • factorChartLinear s b z t +
        r ^ 2 • factorChartQuadratic s b z t := by
  rw [factorChart, factorPlus_scaled, factorMinus_scaled]
  ext i j
  simp [factorChart, rankOneDifference, factorChartLinear, factorChartQuadratic,
    Matrix.vecMulVec, Pi.star_apply]
  ring

end NLA.FR05

end

end
