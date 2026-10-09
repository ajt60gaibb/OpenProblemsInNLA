import ProofProject.FiniteModelMargin

/-!
# Hilbert realization of the perturbed coefficient metric

The coefficient space is embedded in an L² product using its synthesis in the
original Hilbert space and a positive multiple of its Euclidean realization.
Its range is a distinct, finite-dimensional Hilbert space. In particular, no
second norm or inner product is installed on the original space.
-/

noncomputable section

open scoped BigOperators

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {N : ℕ}

/-- Synthesis as a complex linear map. -/
def finiteSynthesisLinear (f : Fin N → H) : (Fin N → ℂ) →ₗ[ℂ] H where
  toFun := finiteSynthesis f
  map_add' c d := by simp [finiteSynthesis, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [finiteSynthesis, Finset.smul_sum, smul_smul]

/-- An L² embedding whose norm squared is the prescribed perturbed energy. -/
def roundedEmbedding (f : Fin N → H) (η : ℝ) :
    (Fin N → ℂ) →ₗ[ℂ] WithLp 2 (H × EuclideanSpace ℂ (Fin N)) :=
  (WithLp.linearEquiv 2 ℂ (H × EuclideanSpace ℂ (Fin N))).symm.toLinearMap.comp
    ((finiteSynthesisLinear f).prod
      ((Real.sqrt η : ℂ) • (EuclideanSpace.equiv (Fin N) ℂ).symm.toLinearMap))

@[simp]
theorem roundedEmbedding_fst (f : Fin N → H) (η : ℝ) (c : Fin N → ℂ) :
    (roundedEmbedding f η c).fst = finiteSynthesis f c := rfl

@[simp]
theorem roundedEmbedding_snd (f : Fin N → H) (η : ℝ) (c : Fin N → ℂ) :
    (roundedEmbedding f η c).snd =
      (Real.sqrt η : ℂ) • (EuclideanSpace.equiv (Fin N) ℂ).symm c := rfl

theorem roundedEmbedding_injective (f : Fin N → H) {η : ℝ} (hη : 0 < η) :
    Function.Injective (roundedEmbedding f η) := by
  intro c d h
  have hs := congrArg WithLp.snd h
  rw [roundedEmbedding_snd, roundedEmbedding_snd] at hs
  have hroot : (Real.sqrt η : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hη).ne'
  have he := (smul_right_injective _ hroot) hs
  exact (EuclideanSpace.equiv (Fin N) ℂ).symm.injective he

/-- The Hilbert space carrying the rounded metric, realized as an actual
subspace of an L² product. It is distinct from the original space `H`. -/
def RoundedSpace (f : Fin N → H) (η : ℝ) := (roundedEmbedding f η).range

instance (f : Fin N → H) (η : ℝ) : NormedAddCommGroup (RoundedSpace f η) :=
  inferInstanceAs (NormedAddCommGroup (roundedEmbedding f η).range)

instance (f : Fin N → H) (η : ℝ) : InnerProductSpace ℂ (RoundedSpace f η) :=
  inferInstanceAs (InnerProductSpace ℂ (roundedEmbedding f η).range)

instance (f : Fin N → H) (η : ℝ) : FiniteDimensional ℂ (RoundedSpace f η) :=
  inferInstanceAs (FiniteDimensional ℂ (roundedEmbedding f η).range)

instance (f : Fin N → H) (η : ℝ) : CompleteSpace (RoundedSpace f η) :=
  FiniteDimensional.complete ℂ (RoundedSpace f η)

/-- The original complex coefficients are linear coordinates on the new space. -/
def roundedCoefficients (f : Fin N → H) {η : ℝ} (hη : 0 < η) :
    RoundedSpace f η ≃ₗ[ℂ] (Fin N → ℂ) :=
  (LinearEquiv.ofInjective (roundedEmbedding f η) (roundedEmbedding_injective f hη)).symm

/-- The distinguished basis corresponds to the usual coordinate vectors. -/
def roundedBasis (f : Fin N → H) {η : ℝ} (hη : 0 < η) :
    Module.Basis (Fin N) ℂ (RoundedSpace f η) :=
  (Pi.basisFun ℂ (Fin N)).map (roundedCoefficients f hη).symm

@[simp]
theorem roundedBasis_repr (f : Fin N → H) {η : ℝ} (hη : 0 < η)
    (x : RoundedSpace f η) (j : Fin N) :
    (roundedBasis f hη).repr x j = roundedCoefficients f hη x j := by
  simp [roundedBasis]

@[simp]
theorem roundedCoefficients_symm_val (f : Fin N → H) {η : ℝ} (hη : 0 < η)
    (c : Fin N → ℂ) :
    ((roundedCoefficients f hη).symm c).val = roundedEmbedding f η c := rfl

/-- Synthesis with the distinguished basis is inverse to taking coefficients. -/
@[simp]
theorem roundedBasis_finiteSynthesis (f : Fin N → H) {η : ℝ} (hη : 0 < η)
    (c : Fin N → ℂ) :
    finiteSynthesis (roundedBasis f hη) c = (roundedCoefficients f hη).symm c := by
  simpa only [finiteSynthesis, roundedBasis_repr, LinearEquiv.apply_symm_apply] using
    (roundedBasis f hη).sum_repr ((roundedCoefficients f hη).symm c)

/-- Taking coefficients and synthesizing the new basis recovers every vector. -/
@[simp]
theorem roundedBasis_synthesis_coefficients (f : Fin N → H) {η : ℝ} (hη : 0 < η)
    (x : RoundedSpace f η) :
    finiteSynthesis (roundedBasis f hη) (roundedCoefficients f hη x) = x := by
  simp

theorem roundedEmbedding_norm_sq (f : Fin N → H) {η : ℝ} (hη : 0 ≤ η)
    (c : Fin N → ℂ) :
    ‖roundedEmbedding f η c‖ ^ 2 =
      ‖finiteSynthesis f c‖ ^ 2 + η * coefficientEnergy c := by
  rw [WithLp.prod_norm_sq_eq_of_L2, roundedEmbedding_fst, roundedEmbedding_snd,
    norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hη,
    EuclideanSpace.norm_sq_eq]
  rfl

/-- The new norm realizes exactly the perturbed coefficient energy. -/
theorem roundedSpace_norm_sq (f : Fin N → H) {η : ℝ} (hη : 0 < η)
    (x : RoundedSpace f η) :
    ‖x‖ ^ 2 = ‖finiteSynthesis f (roundedCoefficients f hη x)‖ ^ 2 +
      η * coefficientEnergy (roundedCoefficients f hη x) := by
  have hx : roundedEmbedding f η (roundedCoefficients f hη x) = x.val := by
    exact LinearEquiv.ofInjective_symm_apply _ x
  rw [← roundedEmbedding_norm_sq f hη.le, hx]
  rfl

@[simp]
theorem roundedCoefficients_symm_norm_sq (f : Fin N → H) {η : ℝ} (hη : 0 < η)
    (c : Fin N → ℂ) :
    ‖(roundedCoefficients f hη).symm c‖ ^ 2 =
      ‖finiteSynthesis f c‖ ^ 2 + η * coefficientEnergy c := by
  rw [roundedSpace_norm_sq f hη, LinearEquiv.apply_symm_apply]

/-- The source's specific perturbation is the norm squared of the new Hilbert space. -/
theorem roundedSpace_norm_sq_eq_model (f : Fin N → H) {M : ℝ}
    (hM : 1 < M) (hN : 0 < N) (x : RoundedSpace f (metricEta M N)) :
    ‖x‖ ^ 2 = roundedModelEnergy M f
      (roundedCoefficients f (metricEta_pos hM hN) x) :=
  roundedSpace_norm_sq f (metricEta_pos hM hN) x

/-- The source's old and new vector norms differ by at most a factor √2. -/
theorem roundedSpace_norm_comparison (f : Fin N → H) {M : ℝ}
    (hM : 1 < M) (hN : 0 < N) (hf : ∀ j, ‖f j‖ = 1)
    (hpattern : ∀ (c : Fin N → ℂ) (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖)
    (x : RoundedSpace f (metricEta M N)) :
    ‖finiteSynthesis f (roundedCoefficients f (metricEta_pos hM hN) x)‖ ≤ ‖x‖ ∧
      ‖x‖ ≤ Real.sqrt 2 *
        ‖finiteSynthesis f (roundedCoefficients f (metricEta_pos hM hN) x)‖ := by
  have h := roundedModelEnergy_comparison f hM hN hf hpattern
    (roundedCoefficients f (metricEta_pos hM hN) x)
  rw [← roundedSpace_norm_sq_eq_model f hM hN x] at h
  constructor
  · exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h.1
  · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using h.2

end ProofProject
