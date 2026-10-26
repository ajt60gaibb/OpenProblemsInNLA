import NLA.Proofs.RE06.GaussianStream

/-! Actual Gaussian block columns and deterministic orthogonal rotations.
All statements retain the frozen countable source law. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

abbrev GaussianEuclid (n : ℕ) := EuclideanSpace ℝ (Fin n)

theorem gaussianBlock_columns_hasLaw (n q offset : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => fun j : Fin q => fun i : Fin n =>
      gaussianBlock n q offset ω i j)
      (Measure.pi (fun _ : Fin q => Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
      GaussianLaw := by
  refine finite_stream_groups_hasLaw
    (fun p : (j : Fin q) × Fin n => gaussianBlockIndex n offset (p.2, p.1)) ?_
  intro ⟨j, i⟩ ⟨j', i'⟩ he
  have hp : (i, j) = (i', j') := gaussianBlockIndex_injective n offset q he
  have hi := congrArg Prod.fst hp
  have hj := congrArg Prod.snd hp
  cases hi
  cases hj
  rfl

/-- The usual Euclidean Gaussian is an actual pushforward of scalar entries. -/
theorem gaussianEuclid_hasLaw (n : ℕ) :
    HasLaw (WithLp.toLp 2 : (Fin n → ℝ) → GaussianEuclid n)
      (stdGaussian (GaussianEuclid n)) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  exact ⟨(WithLp.measurable_toLp 2 _).aemeasurable, map_pi_eq_stdGaussian⟩

theorem gaussianEuclid_coordinates_hasLaw (n : ℕ) :
    HasLaw (WithLp.ofLp : GaussianEuclid n → (Fin n → ℝ))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) (stdGaussian (GaussianEuclid n)) := by
  refine ⟨(WithLp.measurable_ofLp 2 _).aemeasurable, ?_⟩
  rw [← map_pi_eq_stdGaussian, Measure.map_map (WithLp.measurable_ofLp 2 _)
    (WithLp.measurable_toLp 2 _)]
  exact Measure.map_id

/-- Every fixed Euclidean orthogonal change of coordinates preserves the law. -/
theorem gaussianEuclid_rotation_hasLaw (n : ℕ)
    (e : GaussianEuclid n ≃ₗᵢ[ℝ] GaussianEuclid n) :
    HasLaw e (stdGaussian (GaussianEuclid n)) (stdGaussian (GaussianEuclid n)) :=
  ⟨e.continuous.measurable.aemeasurable, stdGaussian_map e⟩

theorem gaussianBlock_euclidean_columns_hasLaw (n q offset : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => fun j : Fin q =>
      WithLp.toLp 2 (fun i : Fin n => gaussianBlock n q offset ω i j))
      (Measure.pi (fun _ : Fin q => stdGaussian (GaussianEuclid n))) GaussianLaw := by
  have hm : MeasurePreserving
      (fun x : Fin q → (Fin n → ℝ) => fun j => WithLp.toLp 2 (x j))
      (Measure.pi (fun _ : Fin q => Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
      (Measure.pi (fun _ : Fin q => stdGaussian (GaussianEuclid n))) :=
    measurePreserving_pi _ _ (fun _ => (gaussianEuclid_hasLaw n).measurePreserving
      (WithLp.measurable_toLp 2 _))
  exact hm.hasLaw.comp (gaussianBlock_columns_hasLaw n q offset)

/-- Distinct columns may be rotated by distinct deterministic orthogonal maps. -/
theorem gaussianBlock_rotated_columns_hasLaw (n q offset : ℕ)
    (e : Fin q → GaussianEuclid n ≃ₗᵢ[ℝ] GaussianEuclid n) :
    HasLaw (fun ω : ℕ → ℝ => fun j : Fin q =>
      e j (WithLp.toLp 2 (fun i : Fin n => gaussianBlock n q offset ω i j)))
      (Measure.pi (fun _ : Fin q => stdGaussian (GaussianEuclid n))) GaussianLaw := by
  have hm : MeasurePreserving (fun x : Fin q → GaussianEuclid n => fun j => e j (x j))
      (Measure.pi (fun _ : Fin q => stdGaussian (GaussianEuclid n)))
      (Measure.pi (fun _ : Fin q => stdGaussian (GaussianEuclid n))) :=
    measurePreserving_pi _ _ (fun j => (gaussianEuclid_rotation_hasLaw n (e j)).measurePreserving
      (e j).continuous.measurable)
  exact hm.hasLaw.comp (gaussianBlock_euclidean_columns_hasLaw n q offset)

/-- After rotating and returning to scalar coordinates, every column still
has the iterated scalar Gaussian product law. -/
theorem gaussianBlock_rotated_coordinates_hasLaw (n q offset : ℕ)
    (e : Fin q → GaussianEuclid n ≃ₗᵢ[ℝ] GaussianEuclid n) :
    HasLaw (fun ω : ℕ → ℝ => fun j : Fin q => fun i : Fin n =>
      (e j (WithLp.toLp 2 (fun i' : Fin n => gaussianBlock n q offset ω i' j))) i)
      (Measure.pi (fun _ : Fin q => Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
      GaussianLaw := by
  have hm : MeasurePreserving (fun x : Fin q → GaussianEuclid n => fun j => WithLp.ofLp (x j))
      (Measure.pi (fun _ : Fin q => stdGaussian (GaussianEuclid n)))
      (Measure.pi (fun _ : Fin q => Measure.pi (fun _ : Fin n => gaussianReal 0 1))) :=
    measurePreserving_pi _ _ (fun _ => (gaussianEuclid_coordinates_hasLaw n).measurePreserving
      (WithLp.measurable_ofLp 2 _))
  exact hm.hasLaw.comp (gaussianBlock_rotated_columns_hasLaw n q offset e)

#assert_trust kernel gaussianBlock_columns_hasLaw
#assert_trust kernel gaussianEuclid_hasLaw
#assert_trust kernel gaussianEuclid_coordinates_hasLaw
#assert_trust kernel gaussianEuclid_rotation_hasLaw
#assert_trust kernel gaussianBlock_euclidean_columns_hasLaw
#assert_trust kernel gaussianBlock_rotated_columns_hasLaw
#assert_trust kernel gaussianBlock_rotated_coordinates_hasLaw
#print axioms gaussianBlock_columns_hasLaw
#print axioms gaussianEuclid_hasLaw
#print axioms gaussianEuclid_coordinates_hasLaw
#print axioms gaussianEuclid_rotation_hasLaw
#print axioms gaussianBlock_euclidean_columns_hasLaw
#print axioms gaussianBlock_rotated_columns_hasLaw
#print axioms gaussianBlock_rotated_coordinates_hasLaw
end NLA.Proofs.RE06
