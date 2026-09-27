/-
Finite-sample aggregation of the source-row `J_epsilon - J_0` estimate.

The frozen matrix `sourceJacobianMatrixFromCoordinates` represents `J_0`.
This file defines the corresponding actual seed-linearization map and
aggregates the rowwise imbalance bound on the source good event.
-/
import NLA.FR05.Planted.ImbalancePerturbation
import NLA.FR05.Planted.SourceGoodEvent

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

open scoped BigOperators ComplexConjugate Matrix RealInnerProductSpace

/-- The actual seed-linearization map `J_epsilon` in the real source
coordinates.  Its `i`th output is the normalized planted equation
linearization for the actual (possibly imbalanced) row. -/
def sourceEpsilonJacobianApply {m n : ℕ}
    (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (x : SourceJacobianVector n) : SourceJacobianVector n :=
  fun i => plantedEquationLinear (sourceRowsFromCoordinates sample (e i))
    (x .sigma) ((x .beta : ℂ) + (x .gamma) * Complex.I)
    (sourceJacobianP x) (sourceJacobianQ x)

/-- The direction factor left by the conservative rowwise comparison. -/
def sourceJacobianDirectionFactor {n : ℕ}
    (x : SourceJacobianVector n) : ℝ :=
  ‖factorPlus (n := n) 0 0 0‖ *
      ‖plusDirection (x .sigma) ((x .beta : ℂ) + (x .gamma) * Complex.I)
        (sourceJacobianP x)‖ +
    ‖factorMinus (n := n) 0 0‖ *
      ‖minusDirection (x .sigma) (sourceJacobianQ x)‖

theorem sourceJacobianDirectionFactor_nonneg {n : ℕ}
    (x : SourceJacobianVector n) : 0 ≤ sourceJacobianDirectionFactor x := by
  unfold sourceJacobianDirectionFactor
  positivity

/-- Every real source-chart coordinate is bounded by the Euclidean norm of
the decoded coordinate vector. -/
theorem abs_sourceJacobianCoordinate_le_euclideanNorm {n : ℕ}
    (x : SourceJacobianVector n) (j : SourceJacobianCoordinate n) :
    |x j| ≤ ‖WithLp.toLp 2 x‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (WithLp.toLp 2 x) j

/-- Each decoded complex tail coordinate is bounded, conservatively, by two
times the real-coordinate Euclidean norm. -/
theorem norm_sourceJacobianP_apply_le_two_mul_euclideanNorm {n : ℕ}
    (x : SourceJacobianVector n) (j : Fin n) :
    ‖sourceJacobianP x j‖ ≤ 2 * ‖WithLp.toLp 2 x‖ := by
  unfold sourceJacobianP
  calc
    ‖(x (.pRe j) : ℂ) + (x (.pIm j) : ℂ) * Complex.I‖ ≤
        ‖(x (.pRe j) : ℂ)‖ + ‖(x (.pIm j) : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = |x (.pRe j)| + |x (.pIm j)| := by
      simp [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 x‖ := by
      gcongr
      · exact abs_sourceJacobianCoordinate_le_euclideanNorm x (.pRe j)
      · exact abs_sourceJacobianCoordinate_le_euclideanNorm x (.pIm j)
    _ = 2 * ‖WithLp.toLp 2 x‖ := by ring

theorem norm_sourceJacobianQ_apply_le_two_mul_euclideanNorm {n : ℕ}
    (x : SourceJacobianVector n) (j : Fin n) :
    ‖sourceJacobianQ x j‖ ≤ 2 * ‖WithLp.toLp 2 x‖ := by
  unfold sourceJacobianQ
  calc
    ‖(x (.qRe j) : ℂ) + (x (.qIm j) : ℂ) * Complex.I‖ ≤
        ‖(x (.qRe j) : ℂ)‖ + ‖(x (.qIm j) : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = |x (.qRe j)| + |x (.qIm j)| := by
      simp [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 x‖ := by
      gcongr
      · exact abs_sourceJacobianCoordinate_le_euclideanNorm x (.qRe j)
      · exact abs_sourceJacobianCoordinate_le_euclideanNorm x (.qIm j)
    _ = 2 * ‖WithLp.toLp 2 x‖ := by ring

/-- The complex scalar chart coordinate obeys the same conservative bound. -/
theorem norm_sourceJacobian_beta_gamma_le_two_mul_euclideanNorm {n : ℕ}
    (x : SourceJacobianVector n) :
    ‖((x .beta : ℂ) + (x .gamma : ℂ) * Complex.I)‖ ≤
      2 * ‖WithLp.toLp 2 x‖ := by
  calc
    ‖((x .beta : ℂ) + (x .gamma : ℂ) * Complex.I)‖ ≤
        ‖(x .beta : ℂ)‖ + ‖(x .gamma : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = |x .beta| + |x .gamma| := by
      simp [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 x‖ := by
      gcongr
      · exact abs_sourceJacobianCoordinate_le_euclideanNorm x .beta
      · exact abs_sourceJacobianCoordinate_le_euclideanNorm x .gamma
    _ = 2 * ‖WithLp.toLp 2 x‖ := by ring

/-- A coordinatewise bound on the two distinguished coordinates and the tail
controls the ambient (sup-coordinate) norm of `joinTwo`. -/
theorem norm_joinTwo_le_of_coordinate_bounds {n : ℕ}
    (u v : ℂ) (w : Signal n) {R : ℝ} (hR : 0 ≤ R)
    (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) (hw : ∀ j, ‖w j‖ ≤ R) :
    ‖joinTwo u v w‖ ≤ R := by
  refine (pi_norm_le_iff_of_nonneg hR).2 ?_
  intro i
  by_cases hi0 : i.1 = 0
  · have hindex : i = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext hi0
    subst i
    simpa [joinTwo] using hu
  · by_cases hi1 : i.1 = 1
    · have hindex : i = ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩ :=
        Fin.ext hi1
      subst i
      simpa [joinTwo] using hv
    · simp only [joinTwo, dif_neg hi0, dif_neg hi1]
      exact hw ⟨i.1 - 2, by lia⟩

/-- The two seed factors appearing in the frozen Jacobian have ambient norm
one. -/
theorem norm_factorPlus_zero_le_one {n : ℕ} :
    ‖factorPlus (n := n) 0 0 0‖ ≤ 1 := by
  simpa [factorPlus] using
    (norm_joinTwo_le_of_coordinate_bounds (n := n) (1 : ℂ) 0 0
      (by norm_num) (by norm_num) (by norm_num) (by intro j; simp))

theorem norm_factorMinus_zero_le_one {n : ℕ} :
    ‖factorMinus (n := n) 0 0‖ ≤ 1 := by
  simpa [factorMinus] using
    (norm_joinTwo_le_of_coordinate_bounds (n := n) (0 : ℂ) 1 0
      (by norm_num) (by norm_num) (by norm_num) (by intro j; simp))

/-- The plus tangent direction is bounded by twice the Euclidean norm of its
decoded real coordinate vector. -/
theorem norm_plusDirection_sourceJacobian_le_two_mul_euclideanNorm {n : ℕ}
    (x : SourceJacobianVector n) :
    ‖plusDirection (x .sigma) ((x .beta : ℂ) + (x .gamma) * Complex.I)
        (sourceJacobianP x)‖ ≤ 2 * ‖WithLp.toLp 2 x‖ := by
  unfold plusDirection
  refine norm_joinTwo_le_of_coordinate_bounds
    ((x .sigma : ℂ) / 4)
    (star ((x .beta : ℂ) + (x .gamma) * Complex.I))
    (sourceJacobianP x) (by positivity) ?_ ?_ ?_
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    norm_num
    calc
      |x .sigma| / 4 ≤ ‖WithLp.toLp 2 x‖ / 4 :=
        div_le_div_of_nonneg_right
          (abs_sourceJacobianCoordinate_le_euclideanNorm x .sigma) (by norm_num)
      _ ≤ 2 * ‖WithLp.toLp 2 x‖ := by
        nlinarith [norm_nonneg (WithLp.toLp 2 x)]
  · simpa only [norm_star] using
      norm_sourceJacobian_beta_gamma_le_two_mul_euclideanNorm x
  · intro j
    exact norm_sourceJacobianP_apply_le_two_mul_euclideanNorm x j

/-- The minus tangent direction is bounded by twice the Euclidean norm of
its decoded real coordinate vector. -/
theorem norm_minusDirection_sourceJacobian_le_two_mul_euclideanNorm {n : ℕ}
    (x : SourceJacobianVector n) :
    ‖minusDirection (x .sigma) (sourceJacobianQ x)‖ ≤
      2 * ‖WithLp.toLp 2 x‖ := by
  unfold minusDirection
  refine norm_joinTwo_le_of_coordinate_bounds
    (0 : ℂ) (-(x .sigma : ℂ) / 4) (-(sourceJacobianQ x))
    (by positivity) ?_ ?_ ?_
  · norm_num
  · rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    norm_num
    calc
      |x .sigma| / 4 ≤ ‖WithLp.toLp 2 x‖ / 4 :=
        div_le_div_of_nonneg_right
          (abs_sourceJacobianCoordinate_le_euclideanNorm x .sigma) (by norm_num)
      _ ≤ 2 * ‖WithLp.toLp 2 x‖ := by
        nlinarith [norm_nonneg (WithLp.toLp 2 x)]
  · intro j
    simpa using
      norm_sourceJacobianQ_apply_le_two_mul_euclideanNorm x j

/-- The source Jacobian direction factor is controlled by four times the
Euclidean norm of the decoded coordinate vector. -/
theorem sourceJacobianDirectionFactor_le_four_mul_euclideanNorm {n : ℕ}
    (x : SourceJacobianVector n) :
    sourceJacobianDirectionFactor x ≤ 4 * ‖WithLp.toLp 2 x‖ := by
  unfold sourceJacobianDirectionFactor
  have hplus := norm_plusDirection_sourceJacobian_le_two_mul_euclideanNorm x
  have hminus := norm_minusDirection_sourceJacobian_le_two_mul_euclideanNorm x
  have hfactorPlus := norm_factorPlus_zero_le_one (n := n)
  have hfactorMinus := norm_factorMinus_zero_le_one (n := n)
  calc
    ‖factorPlus (n := n) 0 0 0‖ *
        ‖plusDirection (x .sigma) ((x .beta : ℂ) + (x .gamma) * Complex.I)
          (sourceJacobianP x)‖ +
      ‖factorMinus (n := n) 0 0‖ *
        ‖minusDirection (x .sigma) (sourceJacobianQ x)‖ ≤
      1 * (2 * ‖WithLp.toLp 2 x‖) +
        1 * (2 * ‖WithLp.toLp 2 x‖) := by
      gcongr
    _ = 4 * ‖WithLp.toLp 2 x‖ := by ring

/-- The `J_epsilon` output is compared coordinatewise with the frozen
matrix action. -/
theorem abs_sourceEpsilonJacobianApply_sub_sourceJacobianMatrix_apply_le
    {m n : ℕ} (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (x : SourceJacobianVector n) (i : SourceJacobianCoordinate n) :
    |sourceEpsilonJacobianApply e sample x i -
        (sourceJacobianMatrixFromCoordinates e sample *ᵥ x) i| ≤
      2 * ((n + 2 : ℕ) : ℝ) ^ 2 *
        (Real.sqrt ((sourceRowsFromCoordinates sample (e i)).radial / 2) *
          |(sourceRowsFromCoordinates sample (e i)).imbalance|) *
        (‖plantedColumn (sourceRowsFromCoordinates sample (e i))‖ +
          ‖plantedColumn (sourceRowsFromCoordinates sample (e i)).zeroImbalance‖) /
            (sourceRowsFromCoordinates sample (e i)).radial *
        sourceJacobianDirectionFactor x := by
  unfold sourceEpsilonJacobianApply
  rw [sourceJacobianMatrixFromCoordinates_mulVec_apply]
  simpa [sourceRowsFromCoordinates, sourceJacobianDirectionFactor] using
    (abs_plantedEquationLinear_sub_sourceRowJacobianForm_le
      (sourceRowsFromCoordinates sample (e i)) (x .sigma) (x .beta) (x .gamma)
      (sourceJacobianP x) (sourceJacobianQ x))

/-- A finite Euclidean vector with all coordinates bounded by `C` has norm
at most `sqrt(card) C`. -/
theorem euclideanNorm_le_sqrt_card_mul_of_abs_le
    {ι : Type*} [Fintype ι] (v : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ i, |v i| ≤ C) :
    ‖WithLp.toLp 2 v‖ ≤ Real.sqrt (Fintype.card ι) * C := by
  rw [PiLp.norm_eq_of_L2]
  calc
    Real.sqrt (∑ i, ‖v i‖ ^ 2) ≤ Real.sqrt (∑ _i : ι, C ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hv i) 2
    _ = _ := by simp [Real.sqrt_mul, Real.sqrt_sq hC]

/-- On the finite source good event, each coordinate of `J_epsilon x-J_0 x`
has the explicit source-scale bound supplied by the rowwise comparison.
The separate imbalance hypothesis is the almost-sure support fact with the
sharper width `sourceEpsilon M`; `SourceCoordinateSampleGood` itself stores
only the weaker `|xi| ≤ 1` needed to construct rows. -/
theorem abs_sourceEpsilonJacobianApply_sub_sourceJacobianMatrix_apply_le_good
    {M m n : ℕ} (hM : 2 ≤ M)
    (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (hgood : SourceCoordinateSampleGood M sample)
    (himbalance : ∀ j, |(sample j).1.2.1| ≤ sourceEpsilon M)
    (x : SourceJacobianVector n) (i : SourceJacobianCoordinate n) :
    |sourceEpsilonJacobianApply e sample x i -
        (sourceJacobianMatrixFromCoordinates e sample *ᵥ x) i| ≤
      4 * ((n + 2 : ℕ) : ℝ) ^ 2 * (16 * (M : ℝ)) /
        sourceDelta M * sourceEpsilon M * sourceJacobianDirectionFactor x := by
  have hi := hgood (e i)
  have hrow := sourceCoordinatesToPlantedRowOrDefault_eq_of_good hM
    (sample (e i)) hi
  let r : PlantedRow n := sourceCoordinatesToPlantedRow (sample (e i))
    (lt_of_lt_of_le (sourceDelta_pos M (by lia)) hi.1) hi.2.1
  have hradial : sourceDelta M ≤ r.radial := by
    exact hi.1
  have henergy : r.radial + squaredEuclideanNorm r.tail ≤ 16 * (M : ℝ) := by
    change (sample (e i)).1.1 + squaredEuclideanNorm (sample (e i)).2 ≤
      16 * (M : ℝ)
    simpa [signalEnergy] using hi.2.2
  have hsmall : |r.imbalance| ≤ sourceEpsilon M := by
    exact himbalance (e i)
  unfold sourceEpsilonJacobianApply
  rw [sourceJacobianMatrixFromCoordinates_mulVec_apply]
  change |plantedEquationLinear (sourceRowsFromCoordinates sample (e i))
      (x .sigma) ((x .beta : ℂ) + (x .gamma) * Complex.I)
      (sourceJacobianP x) (sourceJacobianQ x) -
      sourceRowJacobianForm (sourceRowsFromCoordinates sample (e i))
        (x .sigma) (x .beta) (x .gamma)
        (sourceJacobianP x) (sourceJacobianQ x)| ≤ _
  rw [sourceRowsFromCoordinates, hrow]
  simpa [r, sourceJacobianDirectionFactor] using
    (abs_plantedEquationLinear_sub_sourceRowJacobianForm_le_of_radial_tail
      r
      (x .sigma) (x .beta) (x .gamma) (sourceJacobianP x) (sourceJacobianQ x)
      (sourceDelta_pos M (by lia)) hradial henergy hsmall)

/-- Euclidean aggregation of the source-good-event row bound.  This is the
finite-sample `J_epsilon - J_0` estimate before bounding the chart-direction
factor by the Euclidean norm of the input. -/
theorem euclideanNorm_sourceEpsilonJacobianError_le_good
    {M m n : ℕ} (hM : 2 ≤ M)
    (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (hgood : SourceCoordinateSampleGood M sample)
    (himbalance : ∀ j, |(sample j).1.2.1| ≤ sourceEpsilon M)
    (x : SourceJacobianVector n) :
    ‖WithLp.toLp 2 (fun i : SourceJacobianCoordinate n =>
        sourceEpsilonJacobianApply e sample x i -
          (sourceJacobianMatrixFromCoordinates e sample *ᵥ x) i)‖ ≤
      Real.sqrt (Fintype.card (SourceJacobianCoordinate n)) *
        (4 * ((n + 2 : ℕ) : ℝ) ^ 2 * (16 * (M : ℝ)) /
          sourceDelta M * sourceEpsilon M * sourceJacobianDirectionFactor x) := by
  apply euclideanNorm_le_sqrt_card_mul_of_abs_le
  · have hdelta : 0 < sourceDelta M := sourceDelta_pos M (by lia)
    have hepsilon : 0 ≤ sourceEpsilon M :=
      (sourceEpsilon_pos M (by lia)).le
    have hMreal : 0 ≤ (M : ℝ) := by positivity
    have hnum : 0 ≤ 4 * ((n + 2 : ℕ) : ℝ) ^ 2 * (16 * (M : ℝ)) := by
      positivity
    have hfrac : 0 ≤
        4 * ((n + 2 : ℕ) : ℝ) ^ 2 * (16 * (M : ℝ)) / sourceDelta M :=
      div_nonneg hnum hdelta.le
    exact mul_nonneg (mul_nonneg hfrac hepsilon)
      (sourceJacobianDirectionFactor_nonneg x)
  · intro i
    exact abs_sourceEpsilonJacobianApply_sub_sourceJacobianMatrix_apply_le_good
      hM e sample hgood himbalance x i

/-- The actual `J_epsilon` map on the Euclidean coordinate space used by the
least-gain formulation. -/
def sourceEpsilonJacobianEuclideanApply {m n : ℕ}
    (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (x : EuclideanSpace ℝ (SourceJacobianCoordinate n)) :
    EuclideanSpace ℝ (SourceJacobianCoordinate n) :=
  WithLp.toLp 2 (sourceEpsilonJacobianApply e sample (WithLp.ofLp x))

/-- Exact identification of the Euclidean-map error with the coordinatewise
error vector aggregated above. -/
theorem sourceEpsilonJacobianEuclideanApply_sub_frozen_eq
    {m n : ℕ} (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (x : EuclideanSpace ℝ (SourceJacobianCoordinate n)) :
    sourceEpsilonJacobianEuclideanApply e sample x -
        euclideanMap (sourceJacobianMatrixFromCoordinates e sample) x =
      WithLp.toLp 2 (fun i : SourceJacobianCoordinate n =>
        sourceEpsilonJacobianApply e sample (WithLp.ofLp x) i -
          (sourceJacobianMatrixFromCoordinates e sample *ᵥ WithLp.ofLp x) i) := by
  rfl

/-- Euclidean-map form of the finite-sample perturbation estimate. -/
theorem norm_sourceEpsilonJacobianEuclideanApply_sub_frozen_le_good
    {M m n : ℕ} (hM : 2 ≤ M)
    (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (hgood : SourceCoordinateSampleGood M sample)
    (himbalance : ∀ j, |(sample j).1.2.1| ≤ sourceEpsilon M)
    (x : EuclideanSpace ℝ (SourceJacobianCoordinate n)) :
    ‖sourceEpsilonJacobianEuclideanApply e sample x -
        euclideanMap (sourceJacobianMatrixFromCoordinates e sample) x‖ ≤
      Real.sqrt (Fintype.card (SourceJacobianCoordinate n)) *
        (4 * ((n + 2 : ℕ) : ℝ) ^ 2 * (16 * (M : ℝ)) /
          sourceDelta M * sourceEpsilon M *
            sourceJacobianDirectionFactor (WithLp.ofLp x)) := by
  rw [sourceEpsilonJacobianEuclideanApply_sub_frozen_eq]
  exact euclideanNorm_sourceEpsilonJacobianError_le_good
    hM e sample hgood himbalance (WithLp.ofLp x)

/-- The explicit finite-sample Euclidean perturbation scale obtained from
the source good event.  It is intentionally conservative: the factor `16`
combines the rowwise constant `4` with the chart-direction estimate `4`. -/
def sourceJacobianPerturbationScale (M n : ℕ) : ℝ :=
  Real.sqrt (Fintype.card (SourceJacobianCoordinate n)) *
    (16 * ((n + 2 : ℕ) : ℝ) ^ 2 * (16 * (M : ℝ)) /
      sourceDelta M * sourceEpsilon M)

/-- The finite-sample source-good-event estimate as a Euclidean operator
bound for the actual imbalance-dependent seed linearization. -/
theorem norm_sourceEpsilonJacobianEuclideanApply_sub_frozen_le_good_operator
    {M m n : ℕ} (hM : 2 ≤ M)
    (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (hgood : SourceCoordinateSampleGood M sample)
    (himbalance : ∀ j, |(sample j).1.2.1| ≤ sourceEpsilon M)
    (x : EuclideanSpace ℝ (SourceJacobianCoordinate n)) :
    ‖sourceEpsilonJacobianEuclideanApply e sample x -
        euclideanMap (sourceJacobianMatrixFromCoordinates e sample) x‖ ≤
      sourceJacobianPerturbationScale M n * ‖x‖ := by
  have hdelta : 0 < sourceDelta M := sourceDelta_pos M (by lia)
  have hepsilon : 0 ≤ sourceEpsilon M :=
    (sourceEpsilon_pos M (by lia)).le
  have hMreal : 0 ≤ (M : ℝ) := by positivity
  have hcoefficient : 0 ≤
      4 * ((n + 2 : ℕ) : ℝ) ^ 2 * (16 * (M : ℝ)) /
        sourceDelta M * sourceEpsilon M := by
    apply mul_nonneg
    · apply div_nonneg
      · positivity
      · exact hdelta.le
    · exact hepsilon
  have hdirection :=
    sourceJacobianDirectionFactor_le_four_mul_euclideanNorm (WithLp.ofLp x)
  have hdirection' :
      sourceJacobianDirectionFactor (WithLp.ofLp x) ≤ 4 * ‖x‖ := by
    simpa using hdirection
  calc
    ‖sourceEpsilonJacobianEuclideanApply e sample x -
        euclideanMap (sourceJacobianMatrixFromCoordinates e sample) x‖ ≤
      Real.sqrt (Fintype.card (SourceJacobianCoordinate n)) *
        (4 * ((n + 2 : ℕ) : ℝ) ^ 2 * (16 * (M : ℝ)) /
          sourceDelta M * sourceEpsilon M *
            sourceJacobianDirectionFactor (WithLp.ofLp x)) :=
      norm_sourceEpsilonJacobianEuclideanApply_sub_frozen_le_good
        hM e sample hgood himbalance x
    _ ≤ Real.sqrt (Fintype.card (SourceJacobianCoordinate n)) *
        (4 * ((n + 2 : ℕ) : ℝ) ^ 2 * (16 * (M : ℝ)) /
          sourceDelta M * sourceEpsilon M * (4 * ‖x‖)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hdirection' hcoefficient
      · exact Real.sqrt_nonneg _
    _ = sourceJacobianPerturbationScale M n * ‖x‖ := by
      unfold sourceJacobianPerturbationScale
      ring

/-- Deterministic lower-gain transfer across a `kappa / 2` Euclidean map
perturbation. -/
theorem euclidean_lower_bound_transfer_of_half_perturbation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    {κ : ℝ} (hzero : HasEuclideanLowerBound A κ)
    (hperturb : ∀ x, ‖G x - euclideanMap A x‖ ≤ (κ / 2) * ‖x‖) :
    ∀ x, (κ / 2) * ‖x‖ ≤ ‖G x‖ := by
  intro x
  have hzero_x := hzero x
  have hperturb_x := hperturb x
  have htriangle :
      ‖euclideanMap A x‖ ≤ ‖G x‖ + ‖G x - euclideanMap A x‖ := by
    calc
      ‖euclideanMap A x‖ = ‖G x - (G x - euclideanMap A x)‖ := by
        congr 1
        abel
      _ ≤ ‖G x‖ + ‖G x - euclideanMap A x‖ := norm_sub_le _ _
  linarith

/-- Specialized lower-gain transfer from the frozen source matrix `J_0` to
the actual source seed-linearization `J_epsilon`. -/
theorem sourceEpsilonJacobian_lower_bound_transfer_of_half_perturbation
    {m n : ℕ} (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n) {κ : ℝ}
    (hzero : HasEuclideanLowerBound (sourceJacobianMatrixFromCoordinates e sample) κ)
    (hperturb : ∀ x,
      ‖sourceEpsilonJacobianEuclideanApply e sample x -
          euclideanMap (sourceJacobianMatrixFromCoordinates e sample) x‖ ≤
        (κ / 2) * ‖x‖) :
    ∀ x, (κ / 2) * ‖x‖ ≤ ‖sourceEpsilonJacobianEuclideanApply e sample x‖ := by
  exact euclidean_lower_bound_transfer_of_half_perturbation
    (sourceJacobianMatrixFromCoordinates e sample)
    (sourceEpsilonJacobianEuclideanApply e sample) hzero hperturb

/-- A deterministic lower-gain transfer from the frozen source matrix to the
actual imbalance-dependent seed linearization.  The hypothesis on
`sourceJacobianPerturbationScale` is precisely the remaining numerical
smallness condition needed after the source good event and frozen lower-gain
bound have been supplied. -/
theorem sourceEpsilonJacobian_lower_bound_transfer_of_good
    {M m n : ℕ} (hM : 2 ≤ M)
    (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (hgood : SourceCoordinateSampleGood M sample)
    (himbalance : ∀ j, |(sample j).1.2.1| ≤ sourceEpsilon M)
    {κ : ℝ}
    (hzero : HasEuclideanLowerBound (sourceJacobianMatrixFromCoordinates e sample) κ)
    (hscale : sourceJacobianPerturbationScale M n ≤ κ / 2) :
    ∀ x, (κ / 2) * ‖x‖ ≤ ‖sourceEpsilonJacobianEuclideanApply e sample x‖ := by
  apply sourceEpsilonJacobian_lower_bound_transfer_of_half_perturbation
    e sample hzero
  intro x
  calc
    ‖sourceEpsilonJacobianEuclideanApply e sample x -
        euclideanMap (sourceJacobianMatrixFromCoordinates e sample) x‖ ≤
      sourceJacobianPerturbationScale M n * ‖x‖ :=
      norm_sourceEpsilonJacobianEuclideanApply_sub_frozen_le_good_operator
        hM e sample hgood himbalance x
    _ ≤ (κ / 2) * ‖x‖ :=
      mul_le_mul_of_nonneg_right hscale (norm_nonneg _)

end NLA.FR05
