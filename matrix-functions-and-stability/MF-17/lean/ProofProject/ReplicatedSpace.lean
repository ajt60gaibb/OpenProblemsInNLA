import ProofProject.ReplicationEnergy
import ProofProject.RoundedSpace

/-!
# A concrete Hilbert realization of replicated coefficients

The first component records the group means in the original Hilbert space;
the second records the zero-mean differences in Euclidean coefficient space.
This construction preserves the universe of the original Hilbert space.
-/

noncomputable section

open scoped BigOperators

namespace ProofProject

universe u

/-- The Hilbert space in which the copied family lives. -/
abbrev ReplicatedSpace (H : Type u) (n r : ℕ) :=
  WithLp 2 (H × EuclideanSpace ℂ (Fin n × Fin r))

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

/-- Group means as a linear map on pair-indexed coefficients. -/
def copiedMeanLinear (r : ℕ) : (Fin n × Fin r → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun c := copiedMean r (fun i l => c (i, l))
  map_add' c d := by
    funext i
    simp [copiedMean, Finset.sum_add_distrib, mul_add]
  map_smul' a c := by
    funext i
    simp [copiedMean, Finset.mul_sum, mul_left_comm]

/-- Subtract the mean separately in each group. -/
def copiedDeviationLinear (r : ℕ) : (Fin n × Fin r → ℂ) →ₗ[ℂ] (Fin n × Fin r → ℂ) where
  toFun c p := c p - copiedMeanLinear r c p.1
  map_add' c d := by
    ext p
    simp [map_add, sub_add_sub_comm]
  map_smul' a c := by
    ext p
    simp [map_smul, mul_sub]

/-- The copied synthesis map in an actual L² product of Hilbert spaces. -/
def replicatedCoefficientMap (f : Fin n → H) (r : ℕ) :
    (Fin n × Fin r → ℂ) →ₗ[ℂ] ReplicatedSpace H n r :=
  (WithLp.linearEquiv 2 ℂ (H × EuclideanSpace ℂ (Fin n × Fin r))).symm.toLinearMap.comp
    (((Real.sqrt (r : ℝ) : ℂ) • (finiteSynthesisLinear f).comp (copiedMeanLinear r)).prod
      ((EuclideanSpace.equiv (Fin n × Fin r) ℂ).symm.toLinearMap.comp (copiedDeviationLinear r)))

@[simp]
lemma replicatedCoefficientMap_fst (f : Fin n → H) (r : ℕ) (c : Fin n × Fin r → ℂ) :
    (replicatedCoefficientMap f r c).fst =
      (Real.sqrt (r : ℝ) : ℂ) • finiteSynthesis f (copiedMean r (fun i l => c (i, l))) := rfl

@[simp]
lemma replicatedCoefficientMap_snd (f : Fin n → H) (r : ℕ) (c : Fin n × Fin r → ℂ) :
    (replicatedCoefficientMap f r c).snd =
      (EuclideanSpace.equiv (Fin n × Fin r) ℂ).symm
        (fun p => c p - copiedMean r (fun i l => c (i, l)) p.1) := rfl

/-- The actual copied vectors are images of the usual coordinate vectors. -/
def replicatedFamily (f : Fin n → H) (r : ℕ) (p : Fin n × Fin r) : ReplicatedSpace H n r :=
  replicatedCoefficientMap f r (Pi.single p 1)

/-- Synthesis of the copied family is exactly the mean-and-deviation map. -/
lemma replicatedFamily_synthesis (f : Fin n → H) (r : ℕ) (ξ : Fin n → Fin r → ℂ) :
    (∑ p : Fin n × Fin r, ξ p.1 p.2 • replicatedFamily f r p) =
      replicatedCoefficientMap f r (fun p => ξ p.1 p.2) := by
  have hc : (∑ p : Fin n × Fin r, ξ p.1 p.2 • (Pi.single p (1 : ℂ) : Fin n × Fin r → ℂ)) =
      fun p : Fin n × Fin r => ξ p.1 p.2 := by
    ext q
    simp [Pi.single_apply]
  rw [← hc, map_sum]
  simp only [map_smul, replicatedFamily]

/-- The realization has precisely the source's replicated energy. -/
lemma replicatedCoefficientMap_norm_sq (f : Fin n → H) (r : ℕ)
    (ξ : Fin n → Fin r → ℂ) :
    ‖replicatedCoefficientMap f r (fun p => ξ p.1 p.2)‖ ^ 2 = copiedEnergy f r ξ := by
  rw [WithLp.prod_norm_sq_eq_of_L2, replicatedCoefficientMap_fst,
    replicatedCoefficientMap_snd, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (Nat.cast_nonneg _), EuclideanSpace.norm_sq_eq]
  simp only [copiedEnergy, copiedVariance, Fintype.sum_prod_type]
  rfl

/-- Norm square of synthesis with the actual copied vectors. -/
lemma replicatedFamily_synthesis_norm_sq (f : Fin n → H) (r : ℕ)
    (ξ : Fin n → Fin r → ℂ) :
    ‖∑ p : Fin n × Fin r, ξ p.1 p.2 • replicatedFamily f r p‖ ^ 2 =
      copiedEnergy f r ξ := by
  rw [replicatedFamily_synthesis, replicatedCoefficientMap_norm_sq]

/-- The mean of one pair-indexed coordinate vector. -/
lemma copiedMean_pair_single (r : ℕ) (p : Fin n × Fin r) (i : Fin n) :
    copiedMean r (fun j l => (Pi.single p (1 : ℂ) : Fin n × Fin r → ℂ) (j, l)) i =
      if i = p.1 then (r : ℂ)⁻¹ else 0 := by
  rcases p with ⟨j, k⟩
  by_cases h : i = j
  · subst i
    simp [copiedMean, Pi.single_apply]
  · simp [copiedMean, h]

/-- Each copied vector has exactly the prescribed zero-mean Euclidean part. -/
@[simp]
lemma replicatedFamily_snd_apply (f : Fin n → H) (r : ℕ) (p q : Fin n × Fin r) :
    (replicatedFamily f r p).snd q =
      (Pi.single p (1 : ℂ) : Fin n × Fin r → ℂ) q - (if q.1 = p.1 then (r : ℂ)⁻¹ else 0) := by
  simp [replicatedFamily, replicatedCoefficientMap_snd, copiedMean_pair_single]

/-- A nonzero square root in the coefficient field. -/
lemma copiedSqrt_ne_zero {r : ℕ} (hr : 0 < r) : (Real.sqrt (r : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < r by exact_mod_cast hr)).ne'

/-- Each copied vector has original-space component `fᵢ/√r`. -/
lemma replicatedFamily_fst (f : Fin n → H) {r : ℕ} (hr : 0 < r) (p : Fin n × Fin r) :
    (replicatedFamily f r p).fst = (Real.sqrt (r : ℝ) : ℂ)⁻¹ • f p.1 := by
  rw [replicatedFamily, replicatedCoefficientMap_fst]
  simp only [copiedMean_pair_single, finiteSynthesis]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, smul_smul]
  congr 1
  have hs : (Real.sqrt (r : ℝ) : ℂ) ^ 2 = (r : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg r)
  rw [← hs]
  field_simp [copiedSqrt_ne_zero hr]

/-- Copying a unit family produces another unit family in the concrete
Hilbert realization. -/
lemma replicatedFamily_norm (f : Fin n → H) {r : ℕ} (hr : 0 < r)
    (hf : ∀ i, ‖f i‖ = 1) (p : Fin n × Fin r) : ‖replicatedFamily f r p‖ = 1 := by
  let ξ : Fin n → Fin r → ℂ := fun i l => (Pi.single p (1 : ℂ) : Fin n × Fin r → ℂ) (i, l)
  have hsynth : finiteSynthesis f (copiedMean r ξ) = (r : ℂ)⁻¹ • f p.1 := by
    simp [ξ, copiedMean_pair_single, finiteSynthesis]
  have htotal : (∑ i, ∑ l, ‖ξ i l‖ ^ 2) = (1 : ℝ) := by
    rcases p with ⟨j, k⟩
    simp [ξ, Pi.single_apply, apply_ite, ite_and]
  have hmean : (∑ i, ‖copiedMean r ξ i‖ ^ 2) = ‖(r : ℂ)⁻¹‖ ^ 2 := by
    simp [ξ, copiedMean_pair_single, apply_ite]
  have hvar : (∑ i, copiedVariance r ξ i) = 1 - (r : ℝ) * ‖(r : ℂ)⁻¹‖ ^ 2 := by
    simp only [copiedVariance_eq_sum_norm_sq_sub hr, Finset.sum_sub_distrib,
      ← Finset.mul_sum, htotal, hmean]
  have henergy : copiedEnergy f r ξ = 1 := by
    rw [copiedEnergy, hsynth, hvar, norm_smul, hf, mul_one]
    ring
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  change ‖replicatedCoefficientMap f r (fun q => ξ q.1 q.2)‖ ^ 2 = 1 ^ 2
  rw [replicatedCoefficientMap_norm_sq, henergy]
  norm_num

/-- Constant coefficients in each group embed the old coefficient vector
isometrically into the replicated model. -/
def copiedLift (r : ℕ) (a : Fin n → ℂ) : Fin n → Fin r → ℂ :=
  fun i _ => (Real.sqrt (r : ℝ) : ℂ)⁻¹ * a i

lemma copiedLift_mean {r : ℕ} (hr : 0 < r) (a : Fin n → ℂ) :
    copiedMean r (copiedLift r a) = fun i => (Real.sqrt (r : ℝ) : ℂ)⁻¹ * a i := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  funext i
  simp [copiedMean, copiedLift, ← mul_assoc, hrC]

lemma copiedLift_ne_zero {r : ℕ} (hr : 0 < r) {a : Fin n → ℂ} (ha : a ≠ 0) :
    copiedLift r a ≠ 0 := by
  intro h
  apply ha
  funext i
  have hi := congrFun (congrFun h i) ⟨0, hr⟩
  simp only [copiedLift, Pi.zero_apply] at hi
  exact (mul_eq_zero.mp hi).resolve_left (inv_ne_zero (copiedSqrt_ne_zero hr))

/-- Constant copies synthesize precisely the original vector with zero deviation. -/
lemma replicatedCoefficientMap_copiedLift (f : Fin n → H) {r : ℕ}
    (hr : 0 < r) (a : Fin n → ℂ) :
    replicatedCoefficientMap f r (fun p => copiedLift r a p.1 p.2) =
      WithLp.toLp 2 (finiteSynthesis f a, (0 : EuclideanSpace ℂ (Fin n × Fin r))) := by
  apply (WithLp.linearEquiv 2 ℂ (H × EuclideanSpace ℂ (Fin n × Fin r))).injective
  apply Prod.ext
  · change (Real.sqrt (r : ℝ) : ℂ) • finiteSynthesis f (copiedMean r (copiedLift r a)) = _
    rw [copiedLift_mean hr]
    change (Real.sqrt (r : ℝ) : ℂ) •
      finiteSynthesisLinear f ((Real.sqrt (r : ℝ) : ℂ)⁻¹ • a) = _
    rw [map_smul, smul_smul, mul_inv_cancel₀ (copiedSqrt_ne_zero hr), one_smul]
    rfl
  · change (EuclideanSpace.equiv (Fin n × Fin r) ℂ).symm
      (fun p => copiedLift r a p.1 p.2 - copiedMean r (copiedLift r a) p.1) = 0
    rw [copiedLift_mean hr]
    have hz : (fun p : Fin n × Fin r =>
        (Real.sqrt (r : ℝ) : ℂ)⁻¹ * a p.1 - (Real.sqrt (r : ℝ) : ℂ)⁻¹ * a p.1) = 0 := by
      ext p
      exact sub_self _
    change (EuclideanSpace.equiv (Fin n × Fin r) ℂ).symm
      (fun p : Fin n × Fin r => (Real.sqrt (r : ℝ) : ℂ)⁻¹ * a p.1 -
        (Real.sqrt (r : ℝ) : ℂ)⁻¹ * a p.1) = 0
    rw [hz, map_zero]

/-- The constant-copy coefficient lift preserves the synthesis norm exactly. -/
lemma replicatedFamily_copiedLift_norm (f : Fin n → H) {r : ℕ}
    (hr : 0 < r) (a : Fin n → ℂ) :
    ‖∑ p : Fin n × Fin r, copiedLift r a p.1 p.2 • replicatedFamily f r p‖ =
      ‖finiteSynthesis f a‖ := by
  rw [replicatedFamily_synthesis, replicatedCoefficientMap_copiedLift f hr]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp

end ProofProject
