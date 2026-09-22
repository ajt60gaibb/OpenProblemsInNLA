import NLA.IE21.SphericalLaw

/-!
Finite independent rows with the literal normalized surface law.
Original proof: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLA.IE21

theorem measurable_rowsMatrix (m n : ℕ) : Measurable (@rowsMatrix m n) := by
  unfold rowsMatrix
  fun_prop

theorem measurable_matrixRow (m n : ℕ) (i : Fin m) :
    Measurable (fun A : Mat m n => matrixRow A i) := by
  unfold matrixRow
  fun_prop

@[simp] theorem matrixRow_rowsMatrix {m n : ℕ} (u : Fin m → Space n) (i : Fin m) :
    matrixRow (rowsMatrix u) i = u i := by
  rfl

@[simp] theorem rowsMatrix_matrixRow {m n : ℕ} (A : Mat m n) :
    rowsMatrix (matrixRow A) = A := by
  rfl

theorem independent_row_transport {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n : ℕ} (A : Ω → Mat m n)
    (hA : IndependentSphereRows μ A) : μ.map A = matrixLaw m n := by
  have hm : ∀ i, Measurable (fun ω => matrixRow (A ω) i) :=
    fun i => (measurable_matrixRow m n i).comp hA.1
  have h := hA.2.1.map_fun_eq_pi_map (fun i => (hm i).aemeasurable)
  simp only [hA.2.2] at h
  have hh := congrArg (fun ν : Measure (Fin m → Space n) => ν.map rowsMatrix) h
  rw [Measure.map_map (measurable_rowsMatrix m n) (measurable_pi_lambda _ hm)] at hh
  simpa only [Function.comp_def, rowsMatrix_matrixRow, matrixLaw] using hh

theorem product_row_semantics (m n : ℕ) (hn : 1 ≤ n) :
    IsProbabilityMeasure (matrixLaw m n) ∧
    IndependentSphereRows (matrixLaw m n) (fun A => A) ∧
    (matrixLaw m n) {A | ∀ i, ‖matrixRow A i‖ = 1} = 1 := by
  let : IsProbabilityMeasure (sphereLaw n) := (surface_probability n hn).2.2.2.1
  have hp : IsProbabilityMeasure (matrixLaw m n) :=
    Measure.isProbabilityMeasure_map (measurable_rowsMatrix m n).aemeasurable
  let := hp
  have hrow (i : Fin m) : (matrixLaw m n).map (fun A => matrixRow A i) = sphereLaw n := by
    rw [matrixLaw, Measure.map_map (measurable_matrixRow m n i) (measurable_rowsMatrix m n)]
    simpa only [Function.comp_def, matrixRow_rowsMatrix] using
      (measurePreserving_eval (fun _ : Fin m => sphereLaw n) i).map_eq
  have hrows : (matrixLaw m n).map (fun A => matrixRow A) =
      Measure.pi (fun _ : Fin m => sphereLaw n) := by
    rw [matrixLaw, Measure.map_map (measurable_pi_lambda _ (measurable_matrixRow m n))
      (measurable_rowsMatrix m n)]
    have hident : (fun x : Fin m → Space n => matrixRow (rowsMatrix x)) = id := by
      funext x i
      rfl
    simp only [Function.comp_def, hident, Measure.map_id]
  have hind : iIndepFun (fun i (A : Mat m n) => matrixRow A i) (matrixLaw m n) := by
    apply (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (measurable_matrixRow m n i).aemeasurable)).2
    simpa only [hrow] using hrows
  refine ⟨hp, ⟨measurable_id, hind, hrow⟩, ?_⟩
  apply (ae_iff_prob_eq_one (by unfold matrixRow; fun_prop)).1
  rw [ae_all_iff]
  intro i
  have hu : ∀ᵐ u ∂sphereLaw n, ‖u‖ = 1 :=
    (ae_iff_prob_eq_one (by fun_prop)).2 (surface_probability n hn).2.2.2.2
  rw [← hrow i] at hu
  exact (ae_map_iff (measurable_matrixRow m n i).aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet).1 hu

end NLA.IE21
