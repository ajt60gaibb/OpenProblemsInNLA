import NLA.FR05.Gaussian.NormalizedProjectionLaw

/-!
# Sequential Haar conditioning and overlap-column volume

The sections develop `HaarColumnConditioning`, `HaarSequentialLaw`, `OverlapColumnsVolume`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section HaarColumnConditioning

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Elementwise

def headFixedUnitaryMatrix {n : ℕ} (W : SourceUnitary n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Fin.cons (Fin.cons 1 (fun _ ↦ 0)) (fun i ↦ Fin.cons 0 (W.val i))

theorem headFixedUnitaryMatrix_gram {n : ℕ} (W : SourceUnitary n) :
    (headFixedUnitaryMatrix W)ᴴ * headFixedUnitaryMatrix W = 1 := by
  ext i j
  change (∑ k, star (headFixedUnitaryMatrix W k i) * headFixedUnitaryMatrix W k j) =
    if i = j then 1 else 0
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · refine Fin.cases ?_ (fun j ↦ ?_) j
    · simp [headFixedUnitaryMatrix, Fin.sum_univ_succ]
    · simp [headFixedUnitaryMatrix, Fin.sum_univ_succ, eq_comm]
  · refine Fin.cases ?_ (fun j ↦ ?_) j
    · simp [headFixedUnitaryMatrix, Fin.sum_univ_succ]
    · have h := congrFun (congrFun (Matrix.UnitaryGroup.star_mul_self W) i) j
      simpa [headFixedUnitaryMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_succ, Matrix.one_apply, Matrix.star_eq_conjTranspose] using h

def headFixedUnitary {n : ℕ} (W : SourceUnitary n) : SourceUnitary (n + 1) :=
  ⟨headFixedUnitaryMatrix W, Matrix.mem_unitaryGroup_iff'.mpr (headFixedUnitaryMatrix_gram W)⟩

@[fun_prop]
theorem continuous_headFixedUnitary (n : ℕ) :
    Continuous (headFixedUnitary (n := n)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · refine Fin.cases ?_ (fun j ↦ ?_) j <;> exact continuous_const
  · refine Fin.cases ?_ (fun j ↦ ?_) j
    · exact continuous_const
    · exact (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

theorem headFixedUnitary_mul_first {n : ℕ} (U : SourceUnitary (n + 1))
    (W : SourceUnitary n) (i : Fin (n + 1)) :
    (U * headFixedUnitary W).val i 0 = U.val i 0 := by
  change (∑ k, U.val i k * headFixedUnitaryMatrix W k 0) = _
  simp [headFixedUnitaryMatrix, Fin.sum_univ_succ]

theorem headFixedUnitary_mul_tail {n : ℕ} (U : SourceUnitary (n + 1))
    (W : SourceUnitary n) (i : Fin (n + 1)) (j : Fin n) :
    (U * headFixedUnitary W).val i j.succ = ∑ k, U.val i k.succ * W.val k j := by
  change (∑ k, U.val i k * headFixedUnitaryMatrix W k j.succ) = _
  simp [headFixedUnitaryMatrix, Fin.sum_univ_succ]

def sourceComplementRows {n : ℕ} (hn : 1 ≤ n) (U : SourceUnitary (n + 1)) :
    Matrix (Fin 2) (Fin n) ℂ :=
  fun i j ↦ U.val (Fin.castLE (by lia) i) j.succ

def matrixOfColumns (z w : Signal 2) : SourceOverlapMatrix :=
  fun i ↦ ![z i, w i]

@[fun_prop]
theorem continuous_matrixOfColumns :
    Continuous (fun p : Signal 2 × Signal 2 ↦ matrixOfColumns p.1 p.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases j
  · exact (continuous_apply i).comp continuous_fst
  · exact (continuous_apply i).comp continuous_snd

theorem sourceHaarCorner_headFixedUnitary {n : ℕ} (hn : 1 ≤ n)
    (U : SourceUnitary (n + 1)) (W : SourceUnitary n) :
    sourceHaarCorner (by lia) (U * headFixedUnitary W) =
      matrixOfColumns (sourceHaarFirstTwoCoordinates (by lia) U)
        (sourceComplementRows hn U *ᵥ sourceHaarFirstColumn (by lia) W) := by
  ext i j
  fin_cases j
  · exact headFixedUnitary_mul_first U W _
  · exact headFixedUnitary_mul_tail U W _ ⟨0, by lia⟩

theorem sourceComplementRows_gram {n : ℕ} (hn : 1 ≤ n) (U : SourceUnitary (n + 1)) :
    sourceComplementRows hn U * (sourceComplementRows hn U)ᴴ =
      1 - Matrix.vecMulVec (sourceHaarFirstTwoCoordinates (by lia) U)
        (star (sourceHaarFirstTwoCoordinates (by lia) U)) := by
  ext i j
  have h := congrFun (congrFun (Unitary.coe_mul_star_self U)
    (Fin.castLE (by lia : 2 ≤ n + 1) i)) (Fin.castLE (by lia : 2 ≤ n + 1) j)
  simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, Fin.castLE_inj] at h
  rw [Fin.sum_univ_succ] at h
  change (∑ k : Fin n, U.val (Fin.castLE (by lia) i) k.succ *
    star (U.val (Fin.castLE (by lia) j) k.succ)) =
    (if i = j then 1 else 0) -
      U.val (Fin.castLE (by lia) i) 0 * star (U.val (Fin.castLE (by lia) j) 0)
  linear_combination h

end HaarColumnConditioning

section HaarSequentialLaw

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal BigOperators Matrix.Norms.Elementwise


theorem normalizedGaussian_projection_of_factor {m : ℕ} (hm : 3 ≤ m)
    (C : Matrix (Fin 2) (Fin m) ℂ) (L : SourceOverlapMatrix)
    (hL : L.det ≠ 0) (hC : C * Cᴴ = L * Lᴴ) :
    (standardComplexGaussianTail m).map (fun x ↦ C *ᵥ normalizedComplexVector x) =
      (sphereProjectionLaw (m - 3)).map (fun w ↦ L *ᵥ w) := by
  let B : Matrix (Fin m) (Fin 2) ℂ := Cᴴ * L⁻¹ᴴ
  have hLi : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hL)
  have hRi : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hL)
  have hB : Bᴴ * B = 1 := by
    simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = L⁻¹ * (C * Cᴴ) * L⁻¹ᴴ := by simp only [Matrix.mul_assoc]
      _ = L⁻¹ * (L * Lᴴ) * L⁻¹ᴴ := by rw [hC]
      _ = (L⁻¹ * L) * (L⁻¹ * L)ᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hLi]; simp
  have hCB : L * Bᴴ = C := by
    simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [← Matrix.mul_assoc, hRi, Matrix.one_mul]
  rw [← normalizedGaussian_orthonormal_projection hm B hB,
    Measure.map_map (by fun_prop) (by
      exact (show Continuous (fun w : Signal m ↦ Bᴴ *ᵥ w) by fun_prop).measurable.comp
        (measurable_normalizedComplexVector m))]
  congr 1
  funext x
  exact congrArg (fun A ↦ A *ᵥ normalizedComplexVector x) hCB.symm |>.trans
    (Matrix.mulVec_mulVec _ _ _).symm

@[fun_prop]
theorem continuous_sourceComplementRows {n : ℕ} (hn : 1 ≤ n) :
    Continuous (sourceComplementRows hn) := by
  exact continuous_pi fun i ↦ continuous_pi fun j ↦
    (continuous_apply j.succ).comp
      ((continuous_apply (Fin.castLE (by lia : 2 ≤ n + 1) i)).comp continuous_subtype_val)

theorem lintegral_sourceHaarCorner_conditioning {n : ℕ} (hn : 1 ≤ n)
    (f : SourceOverlapMatrix → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ U : SourceUnitary (n + 1), f (sourceHaarCorner (by lia) U) ∂sourceUnitaryLaw (n + 1)) =
      ∫⁻ U : SourceUnitary (n + 1), ∫⁻ x : Signal n,
        f (matrixOfColumns (sourceHaarFirstTwoCoordinates (by lia) U)
          (sourceComplementRows hn U *ᵥ normalizedComplexVector x))
        ∂standardComplexGaussianTail n ∂sourceUnitaryLaw (n + 1) := by
  have hc : Measurable (fun p : SourceUnitary (n + 1) × SourceUnitary n ↦
      f (sourceHaarCorner (by lia) (p.1 * headFixedUnitary p.2))) := by
    apply hf.comp
    apply Continuous.measurable
    exact (continuous_sourceHaarCorner _).comp
      (continuous_fst.mul ((continuous_headFixedUnitary n).comp continuous_snd))
  have htranslate (W : SourceUnitary n) :
      (∫⁻ U : SourceUnitary (n + 1),
        f (sourceHaarCorner (by lia) (U * headFixedUnitary W)) ∂sourceUnitaryLaw (n + 1)) =
      ∫⁻ U : SourceUnitary (n + 1),
        f (sourceHaarCorner (by lia) U) ∂sourceUnitaryLaw (n + 1) :=
    lintegral_mul_right_eq_self (μ := sourceUnitaryLaw (n + 1))
      (fun U ↦ f (sourceHaarCorner (by lia) U)) (headFixedUnitary W)
  calc
    _ = ∫⁻ W : SourceUnitary n, ∫⁻ U : SourceUnitary (n + 1),
        f (sourceHaarCorner (by lia) (U * headFixedUnitary W))
          ∂sourceUnitaryLaw (n + 1) ∂sourceUnitaryLaw n := by
      simp_rw [htranslate]
      simp
    _ = ∫⁻ U : SourceUnitary (n + 1), ∫⁻ W : SourceUnitary n,
        f (sourceHaarCorner (by lia) (U * headFixedUnitary W))
          ∂sourceUnitaryLaw n ∂sourceUnitaryLaw (n + 1) :=
      lintegral_lintegral_swap hc.aemeasurable |>.symm
    _ = _ := by
      apply lintegral_congr
      intro U
      simp_rw [sourceHaarCorner_headFixedUnitary hn]
      have hfv : Measurable (fun v : Signal n ↦
          f (matrixOfColumns (sourceHaarFirstTwoCoordinates (by lia) U)
            (sourceComplementRows hn U *ᵥ v))) := by
        apply hf.comp
        have hmul : Continuous (fun v : Signal n ↦ sourceComplementRows hn U *ᵥ v) :=
          continuous_const.matrix_mulVec continuous_id
        exact continuous_matrixOfColumns.measurable.comp
          (measurable_const.prodMk hmul.measurable)
      rw [← lintegral_map hfv (continuous_sourceHaarFirstColumn (by lia)).measurable,
        sourceHaarFirstColumn_eq_normalizedGaussian (by lia),
        lintegral_map hfv (measurable_normalizedComplexVector n)]

end HaarSequentialLaw

section OverlapColumnsVolume

open MeasureTheory Matrix
open scoped ENNReal

instance : MeasureSpace SourceOverlapMatrix :=
  inferInstanceAs (MeasureSpace (Fin 2 → Fin 2 → ℂ))

def overlapColumnsEquiv : SourceOverlapMatrix ≃ᵐ Signal 2 × Signal 2 where
  toFun K := (fun i ↦ K i 0, fun i ↦ K i 1)
  invFun p := matrixOfColumns p.1 p.2
  left_inv K := by ext i j; fin_cases j <;> rfl
  right_inv p := rfl
  measurable_toFun := by
    change Measurable (fun K : SourceOverlapMatrix ↦ (fun i ↦ K i 0, fun i ↦ K i 1))
    fun_prop
  measurable_invFun := continuous_matrixOfColumns.measurable

theorem volumePreserving_overlapColumnsEquiv : MeasurePreserving overlapColumnsEquiv := by
  have hrow := volume_preserving_pi (fun _ : Fin 2 ↦
    volume_preserving_piFinTwo (fun _ : Fin 2 ↦ ℂ))
  have hcol := volume_measurePreserving_arrowProdEquivProdArrow ℂ ℂ (Fin 2)
  exact hcol.comp hrow

theorem lintegral_overlapMatrix_columns (f : SourceOverlapMatrix → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ K, f K) = ∫⁻ z : Signal 2, ∫⁻ w : Signal 2, f (matrixOfColumns z w) := by
  rw [← volumePreserving_overlapColumnsEquiv.symm.map_eq,
    lintegral_map hf overlapColumnsEquiv.symm.measurable,
    Measure.volume_eq_prod, lintegral_prod (fun p : Signal 2 × Signal 2 ↦ f (overlapColumnsEquiv.symm p))
      (hf.comp overlapColumnsEquiv.symm.measurable).aemeasurable]
  rfl

end OverlapColumnsVolume

end NLA.FR05
