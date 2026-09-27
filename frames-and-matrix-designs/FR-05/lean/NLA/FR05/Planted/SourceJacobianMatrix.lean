import NLA.FR05.Geometry.LeastSingular
import NLA.FR05.Densities.SourceRows
import NLA.FR05.SmallBall.SmallBallAlgebra

/-! ## SourceJacobianMatrix -/

section

/-
The finite real matrix representation of the source Jacobian in (3.21).

The coordinate type keeps the scalar, complex, and complex-tail components
separate, while the last theorems put it back at the source dimensions
`4 M - 5`.
-/


set_option autoImplicit false
noncomputable section

namespace NLA.FR05

open scoped BigOperators ComplexConjugate Matrix RealInnerProductSpace

/-- One of the real coordinates in the source Jacobian chart. -/
inductive SourceJacobianCoordinate (n : ℕ)
  | sigma
  | beta
  | gamma
  | pRe (j : Fin n)
  | pIm (j : Fin n)
  | qRe (j : Fin n)
  | qIm (j : Fin n)
  deriving DecidableEq, Fintype

instance (n : ℕ) : Nonempty (SourceJacobianCoordinate n) := ⟨.sigma⟩

/-- Real coordinate vectors for the source Jacobian. -/
abbrev SourceJacobianVector (n : ℕ) := SourceJacobianCoordinate n → ℝ

/-- Squared Euclidean energy of a real source-Jacobian coordinate vector. -/
def sourceJacobianEnergy {n : ℕ} (x : SourceJacobianVector n) : ℝ :=
  ∑ j, x j ^ 2

/-- The frozen row form only uses the radial coordinate, the two phases, and
the Gaussian tail.  It is therefore unchanged when the coupled source row is
replaced by its zero-imbalance reference row. -/
theorem sourceRowJacobianForm_zeroImbalance {n : ℕ} (r : PlantedRow n)
    (σ β γ : ℝ) (p q : Signal n) :
    sourceRowJacobianForm r.zeroImbalance σ β γ p q =
      sourceRowJacobianForm r σ β γ p q := by
  rfl

/-- The matrix row form is exactly the linearized planted equation for the
zero-imbalance reference row `a_i^0` used in (3.21). -/
theorem plantedEquationLinear_zeroImbalance_source_formula {n : ℕ}
    (r : PlantedRow n) (σ β γ : ℝ) (p q : Signal n) :
    plantedEquationLinear r.zeroImbalance σ ((β : ℂ) + γ * Complex.I) p q =
      sourceRowJacobianForm r σ β γ p q := by
  calc
    plantedEquationLinear r.zeroImbalance σ ((β : ℂ) + γ * Complex.I) p q =
        sourceRowJacobianForm r.zeroImbalance σ β γ p q :=
      plantedEquationLinear_source_formula r.zeroImbalance
        (by simp [PlantedRow.zeroImbalance]) σ β γ p q
    _ = sourceRowJacobianForm r σ β γ p q :=
      sourceRowJacobianForm_zeroImbalance r σ β γ p q

/-- Decode the `p` coordinates into a complex tail vector. -/
def sourceJacobianP {n : ℕ} (x : SourceJacobianVector n) : Signal n :=
  fun j => (x (.pRe j) : ℂ) + (x (.pIm j) : ℂ) * Complex.I

/-- Decode the `q` coordinates into a complex tail vector. -/
def sourceJacobianQ {n : ℕ} (x : SourceJacobianVector n) : Signal n :=
  fun j => (x (.qRe j) : ℂ) + (x (.qIm j) : ℂ) * Complex.I

/-- The real-coordinate decoding preserves the usual squared complex
energy of the `p` tail block. -/
theorem signalEnergy_sourceJacobianP {n : ℕ} (x : SourceJacobianVector n) :
    signalEnergy (sourceJacobianP x) =
      (∑ j, (x (.pRe j) ^ 2 + x (.pIm j) ^ 2)) := by
  unfold signalEnergy squaredEuclideanNorm sourceJacobianP
  simp_rw [Complex.normSq_add_mul_I]

/-- The analogous squared-energy identity for the `q` tail block. -/
theorem signalEnergy_sourceJacobianQ {n : ℕ} (x : SourceJacobianVector n) :
    signalEnergy (sourceJacobianQ x) =
      (∑ j, (x (.qRe j) ^ 2 + x (.qIm j) ^ 2)) := by
  unfold signalEnergy squaredEuclideanNorm sourceJacobianQ
  simp_rw [Complex.normSq_add_mul_I]

/-- Decode real chart coordinates into the five arguments of (3.21). -/
def sourceJacobianDecode {n : ℕ} (x : SourceJacobianVector n) :
    ℝ × ℝ × ℝ × Signal n × Signal n :=
  (x .sigma, x .beta, x .gamma, sourceJacobianP x, sourceJacobianQ x)

theorem sourceJacobianP_add {n : ℕ} (x y : SourceJacobianVector n) :
    sourceJacobianP (x + y) = sourceJacobianP x + sourceJacobianP y := by
  funext j
  simp [sourceJacobianP]
  ring

theorem sourceJacobianQ_add {n : ℕ} (x y : SourceJacobianVector n) :
    sourceJacobianQ (x + y) = sourceJacobianQ x + sourceJacobianQ y := by
  funext j
  simp [sourceJacobianQ]
  ring

theorem sourceJacobianP_smul {n : ℕ} (c : ℝ) (x : SourceJacobianVector n) :
    sourceJacobianP (c • x) = c • sourceJacobianP x := by
  funext j
  simp [sourceJacobianP]
  ring

theorem sourceJacobianQ_smul {n : ℕ} (c : ℝ) (x : SourceJacobianVector n) :
    sourceJacobianQ (c • x) = c • sourceJacobianQ x := by
  funext j
  simp [sourceJacobianQ]
  ring

/-- Every finite real coordinate vector is the sum of its coordinate axes. -/
theorem sourceJacobianVector_eq_sum_single {n : ℕ} (x : SourceJacobianVector n) :
    x = ∑ j, x j • Pi.single j 1 := by
  ext j
  simp [Pi.single_apply]

/-- The real linear functional furnished by one source row in (3.21). -/
noncomputable def sourceRowJacobianLinear {n : ℕ} (r : PlantedRow n) :
    SourceJacobianVector n →ₗ[ℝ] ℝ :=
  { toFun := fun x =>
      sourceRowJacobianForm r (x .sigma) (x .beta) (x .gamma)
        (sourceJacobianP x) (sourceJacobianQ x)
    map_add' := by
      intro x y
      simp only [Pi.add_apply]
      rw [sourceJacobianP_add, sourceJacobianQ_add]
      unfold sourceRowJacobianForm
      have harg :
          (sourceJacobianP x + sourceJacobianP y) +
              Complex.exp ((phaseGap r : ℂ) * Complex.I) •
                (sourceJacobianQ x + sourceJacobianQ y) =
            (sourceJacobianP x +
              Complex.exp ((phaseGap r : ℂ) * Complex.I) • sourceJacobianQ x) +
              (sourceJacobianP y +
                Complex.exp ((phaseGap r : ℂ) * Complex.I) • sourceJacobianQ y) := by
        ext j
        simp only [Pi.add_apply, Pi.smul_apply]
        ring
      rw [harg, dotProduct_add]
      simp only [Complex.add_re]
      ring
    map_smul' := by
      intro c x
      simp only [Pi.smul_apply]
      rw [sourceJacobianP_smul, sourceJacobianQ_smul]
      unfold sourceRowJacobianForm
      have harg :
          c • sourceJacobianP x + Complex.exp ((phaseGap r : ℂ) * Complex.I) •
              (c • sourceJacobianQ x) =
            c • (sourceJacobianP x +
              Complex.exp ((phaseGap r : ℂ) * Complex.I) • sourceJacobianQ x) := by
        calc
          c • sourceJacobianP x + Complex.exp ((phaseGap r : ℂ) * Complex.I) •
                (c • sourceJacobianQ x) =
              c • sourceJacobianP x + c •
                (Complex.exp ((phaseGap r : ℂ) * Complex.I) • sourceJacobianQ x) := by
              rw [smul_comm]
          _ = c • (sourceJacobianP x +
                Complex.exp ((phaseGap r : ℂ) * Complex.I) • sourceJacobianQ x) := by
              rw [smul_add]
      rw [harg, dotProduct_smul]
      simp only [Complex.smul_re, smul_eq_mul, RingHom.id_apply]
      ring }

/-- Expand a source row functional in the real coordinate basis. -/
theorem sourceRowJacobianLinear_eq_sum_coordinates {n : ℕ} (r : PlantedRow n)
    (x : SourceJacobianVector n) :
    sourceRowJacobianLinear r x =
      ∑ j, sourceRowJacobianLinear r (Pi.single j 1) * x j := by
  conv_lhs => rw [sourceJacobianVector_eq_sum_single x]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The square real matrix whose `i`th row is Li's Jacobian form for the
corresponding planted row. -/
noncomputable def sourceJacobianMatrix {n : ℕ}
    (rows : SourceJacobianCoordinate n → PlantedRow n) :
    Matrix (SourceJacobianCoordinate n) (SourceJacobianCoordinate n) ℝ :=
  fun i j => sourceRowJacobianLinear (rows i) (Pi.single j 1)

/-- Matrix multiplication by the finite real Jacobian is exactly the source
row formula (3.21) in the decoded `(sigma, beta, gamma, p, q)` coordinates. -/
theorem sourceJacobianMatrix_mulVec_apply {n : ℕ}
    (rows : SourceJacobianCoordinate n → PlantedRow n)
    (x : SourceJacobianVector n) (i : SourceJacobianCoordinate n) :
    (sourceJacobianMatrix rows *ᵥ x) i =
      sourceRowJacobianForm (rows i) (x .sigma) (x .beta) (x .gamma)
        (sourceJacobianP x) (sourceJacobianQ x) := by
  rw [Matrix.mulVec_apply_eq_sum]
  change (∑ j, sourceRowJacobianLinear (rows i) (Pi.single j 1) * x j) = _
  rw [← sourceRowJacobianLinear_eq_sum_coordinates]
  rfl

/-- An explicit finite equivalence separates the three scalar coordinates
from the real and imaginary coordinates of `p` and `q`. -/
def sourceJacobianCoordinateEquivSum (n : ℕ) :
    SourceJacobianCoordinate n ≃
      Fin 3 ⊕ (Fin n ⊕ (Fin n ⊕ (Fin n ⊕ Fin n))) where
  toFun
    | .sigma => .inl 0
    | .beta => .inl 1
    | .gamma => .inl 2
    | .pRe j => .inr (.inl j)
    | .pIm j => .inr (.inr (.inl j))
    | .qRe j => .inr (.inr (.inr (.inl j)))
    | .qIm j => .inr (.inr (.inr (.inr j)))
  invFun
    | .inl j => Fin.cases .sigma (fun j => Fin.cases .beta (fun _ => .gamma) j) j
    | .inr (.inl j) => .pRe j
    | .inr (.inr (.inl j)) => .pIm j
    | .inr (.inr (.inr (.inl j))) => .qRe j
    | .inr (.inr (.inr (.inr j))) => .qIm j
  left_inv := by
    intro i
    cases i <;> rfl
  right_inv := by
    intro i
    rcases i with i | i
    · fin_cases i <;> rfl
    · rcases i with i | i
      · rfl
      · rcases i with i | i
        · rfl
        · rcases i with i | i
          · rfl
          · rfl

/-- The coordinate type has the expected real dimension. -/
theorem card_sourceJacobianCoordinate (n : ℕ) :
    Fintype.card (SourceJacobianCoordinate n) = 1 + 2 + 2 * n + 2 * n := by
  rw [Fintype.card_congr (sourceJacobianCoordinateEquivSum n)]
  simp
  lia

/-- The real coordinate energy splits into the three scalar coordinates and
the two decoded complex tail energies. -/
theorem sourceJacobianEnergy_eq_scalar_tail {n : ℕ}
    (x : SourceJacobianVector n) :
    sourceJacobianEnergy x =
      x .sigma ^ 2 + x .beta ^ 2 + x .gamma ^ 2 +
        signalEnergy (sourceJacobianP x) + signalEnergy (sourceJacobianQ x) := by
  rw [signalEnergy_sourceJacobianP, signalEnergy_sourceJacobianQ]
  unfold sourceJacobianEnergy
  rw [← (sourceJacobianCoordinateEquivSum n).symm.sum_comp]
  simp only [sourceJacobianCoordinateEquivSum, Fintype.sum_sum_type]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp
  have hone :
      Fin.cases (SourceJacobianCoordinate.sigma (n := n))
        (fun j => Fin.cases (SourceJacobianCoordinate.beta (n := n))
          (fun _ => SourceJacobianCoordinate.gamma (n := n)) j) (1 : Fin 3) =
        SourceJacobianCoordinate.beta (n := n) := by
    rfl
  have htwo :
      Fin.cases (SourceJacobianCoordinate.sigma (n := n))
        (fun j => Fin.cases (SourceJacobianCoordinate.beta (n := n))
          (fun _ => SourceJacobianCoordinate.gamma (n := n)) j) (2 : Fin 3) =
        SourceJacobianCoordinate.gamma (n := n) := by
    rfl
  rw [hone, htwo]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- The coordinate energy of a Euclidean vector agrees with its squared
Euclidean norm after passing through `WithLp.ofLp`. -/
theorem sourceJacobianEnergy_ofLp_eq_norm_sq {n : ℕ}
    (x : EuclideanSpace ℝ (SourceJacobianCoordinate n)) :
    sourceJacobianEnergy (WithLp.ofLp x) = ‖x‖ ^ 2 := by
  unfold sourceJacobianEnergy
  rw [EuclideanSpace.real_norm_sq_eq]

/-- A unit source-Jacobian direction lies in one of the two branches used in
Lemma 3.6: either its tail energy is at least one quarter, or its three
scalar coefficients carry at least three quarters of the energy. -/
theorem sourceJacobian_scalar_or_tail_energy_ge_quarter {n : ℕ}
    (x : SourceJacobianVector n) (hunit : sourceJacobianEnergy x = 1) :
    (1 / 4 : ℝ) ≤ signalEnergy (sourceJacobianP x) + signalEnergy (sourceJacobianQ x) ∨
      (3 / 4 : ℝ) ≤ x .sigma ^ 2 + x .beta ^ 2 + x .gamma ^ 2 := by
  rw [sourceJacobianEnergy_eq_scalar_tail] at hunit
  by_cases htail : (1 / 4 : ℝ) ≤ signalEnergy (sourceJacobianP x) +
      signalEnergy (sourceJacobianQ x)
  · exact Or.inl htail
  · right
    have htail' : signalEnergy (sourceJacobianP x) +
        signalEnergy (sourceJacobianQ x) < 1 / 4 := lt_of_not_ge htail
    linarith

/-- The same energy dichotomy expressed for a unit vector in the Euclidean
domain used by the least-gain statement. -/
theorem sourceJacobian_scalar_or_tail_energy_ge_quarter_of_norm_one {n : ℕ}
    (x : EuclideanSpace ℝ (SourceJacobianCoordinate n)) (hunit : ‖x‖ = 1) :
    (1 / 4 : ℝ) ≤ signalEnergy (sourceJacobianP (WithLp.ofLp x)) +
        signalEnergy (sourceJacobianQ (WithLp.ofLp x)) ∨
      (3 / 4 : ℝ) ≤ (WithLp.ofLp x) .sigma ^ 2 +
        (WithLp.ofLp x) .beta ^ 2 + (WithLp.ofLp x) .gamma ^ 2 := by
  apply sourceJacobian_scalar_or_tail_energy_ge_quarter
  rw [sourceJacobianEnergy_ofLp_eq_norm_sq, hunit]
  norm_num

/-- Reindex a finite family of planted rows by the coordinate type, producing
the square real Jacobian matrix. -/
noncomputable def sourceJacobianMatrixOfRows {m n : ℕ}
    (e : SourceJacobianCoordinate n ≃ Fin m) (rows : Fin m → PlantedRow n) :
    Matrix (SourceJacobianCoordinate n) (SourceJacobianCoordinate n) ℝ :=
  sourceJacobianMatrix (fun i => rows (e i))

theorem sourceJacobianMatrixOfRows_mulVec_apply {m n : ℕ}
    (e : SourceJacobianCoordinate n ≃ Fin m) (rows : Fin m → PlantedRow n)
    (x : SourceJacobianVector n) (i : SourceJacobianCoordinate n) :
    (sourceJacobianMatrixOfRows e rows *ᵥ x) i =
      sourceRowJacobianForm (rows (e i)) (x .sigma) (x .beta) (x .gamma)
        (sourceJacobianP x) (sourceJacobianQ x) := by
  exact sourceJacobianMatrix_mulVec_apply (fun i => rows (e i)) x i

/-- The source Jacobian matrix as a function of the actual sampled source
coordinates. The off-support default is the same one used by the source-law
bridge, so this is total on the full sample space. -/
noncomputable def sourceJacobianMatrixFromCoordinates {m n : ℕ}
    (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n) :
    Matrix (SourceJacobianCoordinate n) (SourceJacobianCoordinate n) ℝ :=
  sourceJacobianMatrixOfRows e (sourceRowsFromCoordinates sample)

/-- The coupled zero-imbalance rows defining the frozen Jacobian `J_0`. -/
def sourceZeroImbalanceRows {m n : ℕ}
    (sample : Fin m → SourcePlantedCoordinates n) : Fin m → PlantedRow n :=
  fun i => (sourceRowsFromCoordinates sample i).zeroImbalance

theorem sourceJacobianMatrixFromCoordinates_mulVec_apply {m n : ℕ}
    (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (x : SourceJacobianVector n) (i : SourceJacobianCoordinate n) :
    (sourceJacobianMatrixFromCoordinates e sample *ᵥ x) i =
      sourceRowJacobianForm
        (sourceCoordinatesToPlantedRowOrDefault (sample (e i)))
        (x .sigma) (x .beta) (x .gamma) (sourceJacobianP x) (sourceJacobianQ x) := by
  exact sourceJacobianMatrixOfRows_mulVec_apply e (sourceRowsFromCoordinates sample) x i

/-- The source matrix constructed from (3.21) is exactly the seed
linearization for the coupled zero-imbalance rows, not merely a surrogate
matrix with the same dimensions. -/
theorem sourceJacobianMatrixFromCoordinates_mulVec_eq_zeroImbalanceLinear
    {m n : ℕ} (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (x : SourceJacobianVector n) (i : SourceJacobianCoordinate n) :
    (sourceJacobianMatrixFromCoordinates e sample *ᵥ x) i =
      plantedEquationLinear (sourceZeroImbalanceRows sample (e i))
        (x .sigma) ((x .beta : ℂ) + (x .gamma) * Complex.I)
        (sourceJacobianP x) (sourceJacobianQ x) := by
  rw [sourceJacobianMatrixFromCoordinates_mulVec_apply]
  symm
  exact plantedEquationLinear_zeroImbalance_source_formula
    (sourceRowsFromCoordinates sample (e i)) (x .sigma) (x .beta) (x .gamma)
      (sourceJacobianP x) (sourceJacobianQ x)

/-- At the source dimensions, the real-coordinate type has the same finite
cardinality as the sampled-row index. -/
noncomputable def sourceJacobianCoordinateEquivSourceRows (M : ℕ) (hM : 2 ≤ M) :
    SourceJacobianCoordinate (sourceTailDimension M) ≃ Fin (sourceRowCount M) :=
  Fintype.equivOfCardEq (by
    rw [card_sourceJacobianCoordinate]
    simpa using source_chart_real_parameter_count M hM)

/-- The square finite real Jacobian attached to one full source sample at
dimension `M`. -/
noncomputable def sourceJacobianMatrixAt (M : ℕ) (hM : 2 ≤ M)
    (sample : Fin (sourceRowCount M) → SourcePlantedCoordinates (sourceTailDimension M)) :
    Matrix (SourceJacobianCoordinate (sourceTailDimension M))
      (SourceJacobianCoordinate (sourceTailDimension M)) ℝ :=
  sourceJacobianMatrixFromCoordinates (sourceJacobianCoordinateEquivSourceRows M hM) sample

theorem sourceJacobianMatrixAt_mulVec_apply (M : ℕ) (hM : 2 ≤ M)
    (sample : Fin (sourceRowCount M) → SourcePlantedCoordinates (sourceTailDimension M))
    (x : SourceJacobianVector (sourceTailDimension M))
    (i : SourceJacobianCoordinate (sourceTailDimension M)) :
    (sourceJacobianMatrixAt M hM sample *ᵥ x) i =
      sourceRowJacobianForm
        (sourceCoordinatesToPlantedRowOrDefault
          (sample (sourceJacobianCoordinateEquivSourceRows M hM i)))
        (x .sigma) (x .beta) (x .gamma) (sourceJacobianP x) (sourceJacobianQ x) := by
  exact sourceJacobianMatrixFromCoordinates_mulVec_apply
    (sourceJacobianCoordinateEquivSourceRows M hM) sample x i

/-- The deterministic Lemma 3.7 inclusion, specialized to actual source
samples but before any small-ball or probability estimate is applied. -/
theorem exists_sourceJacobian_rowSpanDistanceBad_of_not_hasEuclideanLowerBound
    {m n : ℕ} (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n) {κ : ℝ} (hκ : 0 < κ)
    (hnot : ¬ HasEuclideanLowerBound (sourceJacobianMatrixFromCoordinates e sample) κ) :
    ∃ i : SourceJacobianCoordinate n,
      RowSpanDistanceBad (sourceJacobianMatrixFromCoordinates e sample) i
        ((Fintype.card (SourceJacobianCoordinate n) : ℝ) * κ) := by
  exact exists_rowSpanDistanceBad_of_not_hasEuclideanLowerBound
    (sourceJacobianMatrixFromCoordinates e sample) hκ hnot

/-- The same deterministic inclusion at Li's source dimensions, with the
threshold written as `sourceRowCount M * kappa`. -/
theorem exists_sourceJacobianAt_rowSpanDistanceBad_of_not_hasEuclideanLowerBound
    (M : ℕ) (hM : 2 ≤ M)
    (sample : Fin (sourceRowCount M) → SourcePlantedCoordinates (sourceTailDimension M))
    {κ : ℝ} (hκ : 0 < κ)
    (hnot : ¬ HasEuclideanLowerBound (sourceJacobianMatrixAt M hM sample) κ) :
    ∃ i : SourceJacobianCoordinate (sourceTailDimension M),
      RowSpanDistanceBad (sourceJacobianMatrixAt M hM sample) i
        ((sourceRowCount M : ℝ) * κ) := by
  obtain ⟨i, hi⟩ :=
    exists_sourceJacobian_rowSpanDistanceBad_of_not_hasEuclideanLowerBound
      (sourceJacobianCoordinateEquivSourceRows M hM) sample hκ hnot
  refine ⟨i, ?_⟩
  have hcard : Fintype.card (SourceJacobianCoordinate (sourceTailDimension M)) =
      sourceRowCount M := by
    rw [card_sourceJacobianCoordinate]
    exact source_chart_real_parameter_count M hM
  simpa only [sourceJacobianMatrixAt, hcard] using hi

end NLA.FR05

end
end

/-! ## SourceJacobianEnergy -/

section

/-
Source-coordinate energy bookkeeping for the two small-ball branches in
Lemma 3.6.  This is a thin bridge between the finite real Jacobian chart and
the `tailEnergy` notation used by the conditional Gaussian estimate.
-/


set_option autoImplicit false
noncomputable section

namespace NLA.FR05

/-- A unit real source-Jacobian direction is either tail-dominated, in the
notation required by the Gaussian conditional estimate, or has the scalar
energy required by the phase estimate. -/
theorem sourceJacobian_scalar_or_tail_tailEnergy_ge_quarter {n : ℕ}
    (x : SourceJacobianVector n) (hunit : sourceJacobianEnergy x = 1) :
    (1 / 4 : ℝ) ≤ tailEnergy (sourceJacobianP x) + tailEnergy (sourceJacobianQ x) ∨
      (3 / 4 : ℝ) ≤ x .sigma ^ 2 + x .beta ^ 2 + x .gamma ^ 2 := by
  simpa only [tailEnergy_eq_signalEnergy] using
    (sourceJacobian_scalar_or_tail_energy_ge_quarter x hunit)

/-- The same dichotomy for the unit Euclidean vectors used in the least-gain
formulation of the square source Jacobian. -/
theorem sourceJacobian_scalar_or_tail_tailEnergy_ge_quarter_of_norm_one {n : ℕ}
    (x : EuclideanSpace ℝ (SourceJacobianCoordinate n)) (hunit : ‖x‖ = 1) :
    (1 / 4 : ℝ) ≤ tailEnergy (sourceJacobianP (WithLp.ofLp x)) +
        tailEnergy (sourceJacobianQ (WithLp.ofLp x)) ∨
      (3 / 4 : ℝ) ≤ (WithLp.ofLp x) .sigma ^ 2 +
        (WithLp.ofLp x) .beta ^ 2 + (WithLp.ofLp x) .gamma ^ 2 := by
  simpa only [tailEnergy_eq_signalEnergy] using
    (sourceJacobian_scalar_or_tail_energy_ge_quarter_of_norm_one x hunit)

end NLA.FR05

end

end
