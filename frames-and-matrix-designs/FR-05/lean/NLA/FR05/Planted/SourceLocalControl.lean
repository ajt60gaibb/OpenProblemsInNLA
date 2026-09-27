import NLA.FR05.Planted.SourceMatrixPerturbation

set_option autoImplicit false
noncomputable section
open WithLp
open scoped BigOperators RealInnerProductSpace
namespace NLA.FR05

def sourceFactorDecode {n : ℕ} :
    EuclideanSpace ℝ (SourceJacobianCoordinate n) →ₗ[ℝ] FactorParameters n where
  toFun x := (x .sigma, (x .beta : ℂ) + (x .gamma : ℂ) * Complex.I,
    sourceJacobianP (ofLp x), sourceJacobianQ (ofLp x))
  map_add' x y := by
    ext <;> simp [sourceJacobianP, sourceJacobianQ] <;> ring
  map_smul' c x := by
    ext <;> simp [sourceJacobianP, sourceJacobianQ, smul_eq_mul] <;> ring

theorem sourceFactorDecode_direction_le {n : ℕ}
    (x : EuclideanSpace ℝ (SourceJacobianCoordinate n)) :
    factorDirectionSup (sourceFactorDecode x).1 (sourceFactorDecode x).2.1
      (sourceFactorDecode x).2.2.1 (sourceFactorDecode x).2.2.2 ≤ 4 * ‖x‖ := by
  have hp := norm_plusDirection_sourceJacobian_le_two_mul_euclideanNorm (ofLp x)
  have hq := norm_minusDirection_sourceJacobian_le_two_mul_euclideanNorm (ofLp x)
  simpa [sourceFactorDecode, factorDirectionSup] using (show
    ‖plusDirection ((ofLp x) .sigma) (((ofLp x) .beta : ℂ) + (ofLp x) .gamma * Complex.I)
      (sourceJacobianP (ofLp x))‖ +
    ‖minusDirection ((ofLp x) .sigma) (sourceJacobianQ (ofLp x))‖ ≤ 4 * ‖toLp 2 (ofLp x)‖ by
      linarith)

def sourceEquationEuclidean {m n : ℕ}
    (e : SourceJacobianCoordinate n ≃ Fin m) (sample : Fin m → SourcePlantedCoordinates n)
    (x : EuclideanSpace ℝ (SourceJacobianCoordinate n)) :
    EuclideanSpace ℝ (SourceJacobianCoordinate n) :=
  toLp 2 (fun i ↦ plantedEquationMap (sourceRowsFromCoordinates sample) (sourceFactorDecode x) (e i))

/-- For a quadratic map the symmetric difference is its derivative at the
midpoint: the two quadratic remainders cancel exactly. -/
theorem sourceEquation_midpoint_difference_identity {m n : ℕ}
    (e : SourceJacobianCoordinate n ≃ Fin m) (sample : Fin m → SourcePlantedCoordinates n)
    (x y : EuclideanSpace ℝ (SourceJacobianCoordinate n)) :
    sourceEquationEuclidean e sample x - sourceEquationEuclidean e sample y -
        sourceEpsilonJacobianEuclideanApply e sample (x - y) =
      toLp 2 (fun i ↦
        plantedEquationMapDerivativeVariation (sourceRowsFromCoordinates sample)
          (sourceFactorDecode ((1 / 2 : ℝ) • (x + y)))
          (sourceFactorDecode (x - y)) (e i)) := by
  let θ := sourceFactorDecode ((1 / 2 : ℝ) • (x + y))
  let η := sourceFactorDecode (x - y)
  have hp := plantedEquationMap_add_smul_expansion (sourceRowsFromCoordinates sample) θ η (1 / 2)
  have hm := plantedEquationMap_add_smul_expansion (sourceRowsFromCoordinates sample) θ η (-1 / 2)
  have hx : θ + (1 / 2 : ℝ) • η = sourceFactorDecode x := by
    dsimp [θ, η]
    rw [← map_smul, ← map_add]
    congr 1
    module
  have hy : θ + (-1 / 2 : ℝ) • η = sourceFactorDecode y := by
    dsimp [θ, η]
    rw [← map_smul, ← map_add]
    congr 1
    module
  rw [hx, plantedEquationMapDirectional_eq_linear_add_variation] at hp
  rw [hy, plantedEquationMapDirectional_eq_linear_add_variation] at hm
  apply ofLp_injective
  funext i
  have hp' := congr_fun hp (e i)
  have hm' := congr_fun hm (e i)
  change plantedEquationMap _ (sourceFactorDecode x) (e i) -
    plantedEquationMap _ (sourceFactorDecode y) (e i) -
    plantedEquationMapLinear _ η (e i) = _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp' hm'
  change _ = plantedEquationMapDerivativeVariation _ θ η (e i)
  linarith only [hp', hm']

theorem source_sqrt_card_le_two_mul {M : ℕ} (hM : 2 ≤ M) :
    Real.sqrt (Fintype.card (SourceJacobianCoordinate (sourceTailDimension M))) ≤ 2 * M := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by lia)
  have hc : (Fintype.card (SourceJacobianCoordinate (sourceTailDimension M)) : ℝ) ≤
      4 * M := by
    rw [card_sourceJacobianCoordinate, source_chart_real_parameter_count M hM]
    exact_mod_cast (show sourceRowCount M ≤ 4 * M by unfold sourceRowCount; lia)
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith

/-- The midpoint stays in the same ball, giving a single bilinear estimate
with constant 1024 in place of the former two-term bound 2048. -/
theorem sourceEquation_nonlinear_difference_le {M m : ℕ} (hM : 2 ≤ M)
    (e : SourceJacobianCoordinate (sourceTailDimension M) ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates (sourceTailDimension M))
    (hgood : SourceCoordinateSampleGood M sample)
    (x y : EuclideanSpace ℝ (SourceJacobianCoordinate (sourceTailDimension M)))
    {R : ℝ} (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖sourceEquationEuclidean e sample x - sourceEquationEuclidean e sample y -
      sourceEpsilonJacobianEuclideanApply e sample (x - y)‖ ≤
      1024 * (M : ℝ) ^ 6 * R * ‖x - y‖ := by
  let z := (1 / 2 : ℝ) • (x + y)
  have hz : ‖z‖ ≤ R := by
    dsimp [z]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith [norm_add_le x y]
  have hzd := (sourceFactorDecode_direction_le z).trans
    (mul_le_mul_of_nonneg_left hz (by norm_num : (0 : ℝ) ≤ 4))
  have hd := sourceFactorDecode_direction_le (x - y)
  rw [sourceEquation_midpoint_difference_identity]
  calc
    _ ≤ Real.sqrt (Fintype.card (SourceJacobianCoordinate (sourceTailDimension M))) *
        (512 * (M : ℝ) ^ 5 * R * ‖x - y‖) := by
      apply euclideanNorm_le_sqrt_card_mul_of_abs_le (hC := by positivity)
      intro i
      let row := sourceRowsFromCoordinates sample (e i)
      let θ := sourceFactorDecode z
      let η := sourceFactorDecode (x - y)
      have hrow : plantedRowSupEnergy row ≤ 16 * (M : ℝ) ^ 5 :=
        plantedRowSupEnergy_sourceCoordinatesToPlantedRowOrDefault_le hM _ (hgood (e i))
      calc
        _ ≤ 2 * plantedRowSupEnergy row *
            factorDirectionSup θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 *
            factorDirectionSup η.1 η.2.1 η.2.2.1 η.2.2.2 :=
          abs_plantedEquationDerivativeVariation_le_sup row θ.1 η.1
            θ.2.1 η.2.1 θ.2.2.1 θ.2.2.2 η.2.2.1 η.2.2.2
        _ ≤ 2 * (16 * (M : ℝ) ^ 5) * (4 * R) * (4 * ‖x - y‖) := by
          gcongr
          · exact factorDirectionSup_nonneg _ _ _ _
          · exact factorDirectionSup_nonneg _ _ _ _
        _ = _ := by ring
    _ ≤ (2 * M) * (512 * (M : ℝ) ^ 5 * R * ‖x - y‖) := by
      gcongr
      exact source_sqrt_card_le_two_mul hM
    _ = _ := by ring

theorem sourceJacobianPerturbationScale_le {M : ℕ} (hM : 2 ≤ M) :
    sourceJacobianPerturbationScale M (sourceTailDimension M) ≤ 512 / (M : ℝ) ^ 44 := by
  have hm : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by lia)
  unfold sourceJacobianPerturbationScale
  rw [source_tailDimension_add_two hM]
  calc
    _ ≤ (2 * M) * (16 * (M : ℝ) ^ 2 * (16 * M) / sourceDelta M * sourceEpsilon M) := by
      apply mul_le_mul_of_nonneg_right (source_sqrt_card_le_two_mul hM)
      unfold sourceDelta sourceEpsilon
      positivity
    _ = _ := by unfold sourceDelta sourceEpsilon; field_simp; ring

theorem sourceEquation_frozen_difference_le {M m : ℕ} (hM : 2 ≤ M)
    (e : SourceJacobianCoordinate (sourceTailDimension M) ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates (sourceTailDimension M))
    (hgood : SourceCoordinateSampleGood M sample)
    (himbalance : ∀ j, |(sample j).1.2.1| ≤ sourceEpsilon M)
    (x y : EuclideanSpace ℝ (SourceJacobianCoordinate (sourceTailDimension M)))
    {R : ℝ} (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖sourceEquationEuclidean e sample x - sourceEquationEuclidean e sample y -
      euclideanMap (sourceJacobianMatrixFromCoordinates e sample) (x - y)‖ ≤
      (512 / (M : ℝ) ^ 44 + 2048 * (M : ℝ) ^ 6 * R) * ‖x - y‖ := by
  have hn := sourceEquation_nonlinear_difference_le hM e sample hgood x y hR hx hy
  have hp := norm_sourceEpsilonJacobianEuclideanApply_sub_frozen_le_good_operator
    hM e sample hgood himbalance (x - y)
  have hs := sourceJacobianPerturbationScale_le hM
  calc
    _ = ‖(sourceEquationEuclidean e sample x - sourceEquationEuclidean e sample y -
        sourceEpsilonJacobianEuclideanApply e sample (x - y)) +
        (sourceEpsilonJacobianEuclideanApply e sample (x - y) -
          euclideanMap (sourceJacobianMatrixFromCoordinates e sample) (x - y))‖ := by
      congr 1
      abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ 1024 * (M : ℝ) ^ 6 * R * ‖x - y‖ +
        sourceJacobianPerturbationScale M (sourceTailDimension M) * ‖x - y‖ := add_le_add hn hp
    _ ≤ 2048 * (M : ℝ) ^ 6 * R * ‖x - y‖ +
        (512 / (M : ℝ) ^ 44) * ‖x - y‖ := by gcongr; norm_num
    _ = _ := by ring

theorem sourceEquation_seed_le {M m : ℕ} (hM : 2 ≤ M)
    (e : SourceJacobianCoordinate (sourceTailDimension M) ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates (sourceTailDimension M))
    (hgood : SourceCoordinateSampleGood M sample)
    (himbalance : ∀ j, |(sample j).1.2.1| ≤ sourceEpsilon M) :
    ‖sourceEquationEuclidean e sample 0‖ ≤ 2 / (M : ℝ) ^ 49 := by
  have hm : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by lia)
  have he : sourceEquationEuclidean e sample 0 =
      toLp 2 (fun i ↦ (sample (e i)).1.2.1) := by
    unfold sourceEquationEuclidean
    rw [map_zero, plantedEquationMap_zero]
    congr 1
    funext i
    change (sourceCoordinatesToPlantedRowOrDefault _).imbalance = _
    rw [sourceCoordinatesToPlantedRowOrDefault_eq_of_good hM _ (hgood (e i))]
    rfl
  rw [he]
  calc
    _ ≤ Real.sqrt (Fintype.card (SourceJacobianCoordinate (sourceTailDimension M))) *
        sourceEpsilon M := euclideanNorm_le_sqrt_card_mul_of_abs_le _
          (sourceEpsilon_pos M (by lia)).le (fun i ↦ himbalance (e i))
    _ ≤ (2 * M) * sourceEpsilon M := by
      exact mul_le_mul_of_nonneg_right (source_sqrt_card_le_two_mul hM)
        (sourceEpsilon_pos M (by lia)).le
    _ = _ := by unfold sourceEpsilon; field_simp

end NLA.FR05
