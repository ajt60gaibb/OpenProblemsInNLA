import NLA.Proofs.RE05.RegressionTranscript
import NLA.Proofs.RE05.ComplementProjection

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators Matrix InnerProductSpace

/-- The two literal measurement blocks, packed only for analysis. -/
abbrev MeasurementIndex {n : ℕ} (plan : Plan n) :=
  (Fin plan.selected.length × Fin n) ⊕ (Fin plan.s × Fin n)

abbrev MeasurementSpace {n : ℕ} (plan : Plan n) :=
  EuclideanSpace ℝ (MeasurementIndex plan)

def measurementScale {n : ℕ} (plan : Plan n) : ℝ := Real.sqrt (1 / (plan.s : ℝ))

theorem measurementScale_sq {n : ℕ} (plan : Plan n) :
    measurementScale plan ^ 2 = 1 / (plan.s : ℝ) := by
  exact Real.sq_sqrt (one_div_nonneg.mpr (Nat.cast_nonneg _))

def packedMeasurement {n : ℕ} (plan : Plan n)
    (L : Fin plan.selected.length → Fin n → ℝ) (R : Fin plan.s → Fin n → ℝ) :
    MeasurementSpace plan :=
  WithLp.toLp 2 (Sum.elim (fun p => L p.1 p.2)
    (fun p => measurementScale plan * R p.1 p.2))

theorem packedMeasurement_inner {n : ℕ} (plan : Plan n)
    (L L' : Fin plan.selected.length → Fin n → ℝ)
    (R R' : Fin plan.s → Fin n → ℝ) :
    ⟪packedMeasurement plan L R, packedMeasurement plan L' R'⟫_ℝ =
      (∑ h, dot (L h) (L' h)) + (1 / (plan.s : ℝ)) * ∑ g, dot (R g) (R' g) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [packedMeasurement, dotProduct, WithLp.ofLp_toLp, Pi.star_apply,
    star_trivial, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_prod_type, dot]
  congr 1
  · apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      (measurementScale plan * R' g i) * (measurementScale plan * R g i) =
          measurementScale plan ^ 2 * (R g i * R' g i) := by ring
      _ = _ := by rw [measurementScale_sq]

def measurementVector {n : ℕ} (plan : Plan n) (M : Square n) : MeasurementSpace plan :=
  packedMeasurement plan (fun h => M.transpose *ᵥ uColumn plan h)
    (fun g => complement plan (M *ᵥ (fun k => plan.G k g)))

def observationVector {n : ℕ} (plan : Plan n) (responses : List (Fin n → ℝ)) :
    MeasurementSpace plan :=
  packedMeasurement plan (observedLeft plan responses)
    (fun g => complement plan (observedRight plan responses g))

/-- The actual plan's measurement is linear for every plan, with no promise
about the supplied columns or a positive sketch width. -/
def measurementMap {n : ℕ} (plan : Plan n) : Square n →ₗ[ℝ] MeasurementSpace plan where
  toFun := measurementVector plan
  map_add' A B := by
    ext p
    rcases p with p | p
    · simp [measurementVector, packedMeasurement, Matrix.transpose_add, Matrix.add_mulVec]
    · simp [measurementVector, packedMeasurement, complement_eq_mulVec,
        Matrix.add_mulVec, Matrix.mulVec_add, mul_add]
  map_smul' t A := by
    ext p
    rcases p with p | p
    · simp [measurementVector, packedMeasurement, Matrix.transpose_smul,
        Matrix.smul_mulVec, smul_eq_mul]
    · simp [measurementVector, packedMeasurement, complement_eq_mulVec,
        Matrix.smul_mulVec, Matrix.mulVec_smul, smul_eq_mul]
      ring

theorem observationVector_planAnswers {n : ℕ} (A : Square n) (plan : Plan n) :
    observationVector plan (planAnswers A plan) = measurementVector plan A := by
  ext p
  rcases p with p | p
  · simp [observationVector, measurementVector, packedMeasurement, observedLeft_planAnswers]
  · simp [observationVector, measurementVector, packedMeasurement, observedRight_planAnswers]

theorem observationVector_copyResponses {n : ℕ} (A : Square n)
    (schedule : Fin 15 → Plan n) (copy : Fin 15) :
    observationVector (schedule copy) (copyResponses schedule (batchAnswers A schedule) copy) =
      measurementVector (schedule copy) A := by
  rw [copyResponses_batchAnswers, observationVector_planAnswers]

/-- The supplied, unmodified matrix representation as a linear map. -/
def matrixRepresentationMap {n q : ℕ} (P : Basis n q) :
    (Fin (q + 1) → ℝ) →ₗ[ℝ] Square n where
  toFun := represent P
  map_add' c d := by
    ext i j
    simp [represent, add_mul, Finset.sum_add_distrib]
  map_smul' t c := by
    ext i j
    simp [represent, Finset.mul_sum, mul_assoc]

theorem represent_eq_sum {n q : ℕ} (P : Basis n q) (c : Fin (q + 1) → ℝ) :
    represent P c = ∑ j, c j • P j := by
  ext i k
  simp [represent, Matrix.sum_apply]

theorem represent_single {n q : ℕ} (P : Basis n q) (j : Fin (q + 1)) :
    represent P (Pi.single j 1) = P j := by
  ext i k
  simp [represent, Pi.single_apply]

def coefficientMeasurement {n q : ℕ} (P : Basis n q) (plan : Plan n) :
    (Fin (q + 1) → ℝ) →ₗ[ℝ] MeasurementSpace plan :=
  (measurementMap plan).comp (matrixRepresentationMap P)

theorem coefficientMeasurement_apply {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (c : Fin (q + 1) → ℝ) :
    coefficientMeasurement P plan c = measurementVector plan (represent P c) := rfl

theorem coefficientMeasurement_single {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (j : Fin (q + 1)) :
    coefficientMeasurement P plan (Pi.single j 1) = measurementVector plan (P j) := by
  rw [coefficientMeasurement_apply, represent_single]

theorem coefficientMeasurement_sum {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (c : Fin (q + 1) → ℝ) :
    coefficientMeasurement P plan c = ∑ j, c j • measurementVector plan (P j) := by
  rw [coefficientMeasurement_apply, represent_eq_sum]
  change (measurementMap plan) (∑ j, c j • P j) = _
  simp only [map_sum, map_smul]
  rfl

theorem gram_eq_measurement_inner {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (j k : Fin (q + 1)) :
    gram P plan j k = ⟪measurementVector plan (P j), measurementVector plan (P k)⟫_ℝ := by
  rw [measurementVector, measurementVector, packedMeasurement_inner]
  rfl

theorem rhs_eq_measurement_inner {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) (j : Fin (q + 1)) :
    rhs P plan responses j = ⟪measurementVector plan (P j), observationVector plan responses⟫_ℝ := by
  rw [measurementVector, observationVector, packedMeasurement_inner]
  rfl

theorem gram_mulVec_eq_inner {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (c : Fin (q + 1) → ℝ) (j : Fin (q + 1)) :
    (gram P plan *ᵥ c) j =
      ⟪measurementVector plan (P j), coefficientMeasurement P plan c⟫_ℝ := by
  rw [coefficientMeasurement_sum, inner_sum]
  simp only [inner_smul_right, gram_eq_measurement_inner, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem gram_quadratic {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (c d : Fin (q + 1) → ℝ) :
    dot c (gram P plan *ᵥ d) =
      ⟪coefficientMeasurement P plan c, coefficientMeasurement P plan d⟫_ℝ := by
  rw [coefficientMeasurement_sum, sum_inner]
  simp only [real_inner_smul_left, dot, gram_mulVec_eq_inner]

theorem rhs_linear {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) (c : Fin (q + 1) → ℝ) :
    dot c (rhs P plan responses) =
      ⟪coefficientMeasurement P plan c, observationVector plan responses⟫_ℝ := by
  rw [coefficientMeasurement_sum, sum_inner]
  simp only [real_inner_smul_left, dot, rhs_eq_measurement_inner]

end NLA.Proofs.RE05
