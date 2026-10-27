import NLA.Proofs.RE06.GaussianRotation

/-! Flattening the actual rotated column law into the row/column product
index used by the weighted quadratic estimates. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

/-- Coordinate rearrangement preserves the finite Gaussian law exactly. -/
theorem gaussian_columns_flatten_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (n q : ℕ) (X : Ω → (Fin q → (Fin n → ℝ)))
    (hX : HasLaw X (Measure.pi (fun _ : Fin q =>
      Measure.pi (fun _ : Fin n => gaussianReal 0 1))) μ) :
    HasLaw (fun ω => fun p : Fin n × Fin q => X ω p.2 p.1)
      (Measure.pi (fun _ : Fin n × Fin q => gaussianReal 0 1)) μ := by
  have hu : HasLaw ((MeasurableEquiv.curry (Fin q) (Fin n) ℝ).symm)
      (Measure.pi (fun _ : Fin q × Fin n => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin q => Measure.pi (fun _ : Fin n => gaussianReal 0 1))) := by
    refine ⟨(MeasurableEquiv.curry _ _ _).symm.measurable.aemeasurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry_symm (fun (_ : Fin q) (_ : Fin n) => gaussianReal 0 1))
  have hp := (measurePreserving_piCongrLeft (fun _ : Fin q × Fin n => gaussianReal 0 1)
    (Equiv.prodComm (Fin n) (Fin q))).hasLaw
  exact hp.comp (hu.comp hX)

/-- Full scalar product law of every actual orthogonally rotated block entry. -/
theorem gaussianBlock_rotated_entries_hasLaw (n q offset : ℕ)
    (e : Fin q → GaussianEuclid n ≃ₗᵢ[ℝ] GaussianEuclid n) :
    HasLaw (fun ω : ℕ → ℝ => fun p : Fin n × Fin q =>
      (e p.2 (WithLp.toLp 2 (fun i : Fin n => gaussianBlock n q offset ω i p.2))) p.1)
      (Measure.pi (fun _ : Fin n × Fin q => gaussianReal 0 1)) GaussianLaw :=
  gaussian_columns_flatten_hasLaw n q _ (gaussianBlock_rotated_coordinates_hasLaw n q offset e)

#assert_trust kernel gaussian_columns_flatten_hasLaw
#assert_trust kernel gaussianBlock_rotated_entries_hasLaw
#print axioms gaussian_columns_flatten_hasLaw
#print axioms gaussianBlock_rotated_entries_hasLaw
end NLA.Proofs.RE06
