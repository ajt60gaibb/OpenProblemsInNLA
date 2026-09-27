import NLA.FR05.Likelihood.CanonicalKernelBounds

set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix WithLp

namespace NLA.FR05

attribute [local fun_prop] measurable_sourceDensity

def conditionalGaussianMap (L R : Matrix (Fin 4) (Fin 2) ℂ)
    (N P : SourceOverlapMatrix) (p : Signal 4 × (Signal 2 × Signal 2)) :
    Signal 2 × Signal 2 :=
  (Lᴴ *ᵥ star p.1 + Nᴴ *ᵥ star p.2.1,
    Rᴴ *ᵥ star p.1 + Pᴴ *ᵥ star p.2.2)

@[fun_prop] theorem continuous_conditionalGaussianMap
    (L R : Matrix (Fin 4) (Fin 2) ℂ) (N P : SourceOverlapMatrix) :
    Continuous (conditionalGaussianMap L R N P) := by
  unfold conditionalGaussianMap
  fun_prop

def conditionalGaussianColumns (L R : Matrix (Fin 4) (Fin 2) ℂ)
    (N P : SourceOverlapMatrix) : Matrix (Fin 8) (Fin 2 ⊕ Fin 2) ℂ :=
  (fromRows (fromCols L R)
    ((fromBlocks N 0 0 P).submatrix (finSumFinEquiv (m := 2) (n := 2)).symm id)).submatrix
      (finSumFinEquiv (m := 4) (n := 4)).symm id

theorem conditionalGaussianColumns_gram
    (L R : Matrix (Fin 4) (Fin 2) ℂ) (N P : SourceOverlapMatrix) :
    (conditionalGaussianColumns L R N P)ᴴ * conditionalGaussianColumns L R N P =
      fromBlocks (Lᴴ * L + Nᴴ * N) (Lᴴ * R) (Rᴴ * L) (Rᴴ * R + Pᴴ * P) := by
  unfold conditionalGaussianColumns
  rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_id_id,
    conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows, conjTranspose_fromCols_eq_fromRows_conjTranspose,
    fromRows_mul_fromCols, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_id_id,
    fromBlocks_conjTranspose, fromBlocks_multiply]
  simp only [conjTranspose_zero, zero_mul, mul_zero, add_zero, zero_add]
  ext i j
  cases i <;> cases j <;> simp

theorem conditionalGaussianColumns_projection
    (L R : Matrix (Fin 4) (Fin 2) ℂ) (N P : SourceOverlapMatrix) (x : Signal 8) :
    unpackSourceProjections (gaussianMatrixProjection (conditionalGaussianColumns L R N P) x) =
      conditionalGaussianMap L R N P
        ((splitGaussianSum 4 4 x).1, splitGaussianSum 2 2 (splitGaussianSum 4 4 x).2) := by
  unfold gaussianMatrixProjection conditionalGaussianColumns
  rw [conjTranspose_submatrix, submatrix_mulVec_equiv, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mulVec, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mulVec,
    conjTranspose_submatrix, submatrix_mulVec_equiv, fromBlocks_conjTranspose,
    fromBlocks_mulVec]
  simp only [conjTranspose_zero, zero_mulVec, add_zero, zero_add]
  rfl

theorem conditionalGaussianLaw_eq_canonical
    (L R : Matrix (Fin 4) (Fin 2) ℂ) (N P : SourceOverlapMatrix)
    (hL : Lᴴ * L + Nᴴ * N = 1) (hR : Rᴴ * R + Pᴴ * P = 1)
    (hK : overlapOperatorNorm (Lᴴ * R) < 1) :
    ((standardComplexGaussianTail 4).prod
      ((standardComplexGaussianTail 2).prod (standardComplexGaussianTail 2))).map
        (conditionalGaussianMap L R N P) = canonicalOverlapLaw (Lᴴ * R) := by
  have hg := gaussianMatrixProjection_law_eq_of_gram
    (conditionalGaussianColumns L R N P) (canonicalOverlapColumns (Lᴴ * R)) (by
      rw [conditionalGaussianColumns_gram, hL, hR, canonicalOverlapColumns_gram hK]
      simp)
  have hh := congrArg (Measure.map unpackSourceProjections) hg
  rw [← canonicalOverlapLaw_eq_projection] at hh
  rw [Measure.map_map continuous_unpackSourceProjections.measurable
    (continuous_gaussianMatrixProjection _).measurable] at hh
  have he : unpackSourceProjections ∘ gaussianMatrixProjection (conditionalGaussianColumns L R N P) =
      conditionalGaussianMap L R N P ∘
        (fun p : Signal 4 × Signal 4 ↦ (p.1, splitGaussianSum 2 2 p.2)) ∘ splitGaussianSum 4 4 := by
    funext x
    exact conditionalGaussianColumns_projection L R N P x
  rw [he, ← Measure.map_map (continuous_conditionalGaussianMap L R N P).measurable
      (by unfold splitGaussianSum; fun_prop),
    ← Measure.map_map (by unfold splitGaussianSum; fun_prop) (continuous_splitGaussianSum 4 4).measurable,
    standardComplexGaussianTail_map_splitSum] at hh
  have hs :
      ((standardComplexGaussianTail 4).prod (standardComplexGaussianTail 4)).map
        (fun p : Signal 4 × Signal 4 ↦ (p.1, splitGaussianSum 2 2 p.2)) =
      (standardComplexGaussianTail 4).prod
        ((standardComplexGaussianTail 2).prod (standardComplexGaussianTail 2)) := by
    have h := Measure.map_prod_map (standardComplexGaussianTail 4)
      (standardComplexGaussianTail 4) measurable_id (continuous_splitGaussianSum 2 2).measurable
    have hsplit := standardComplexGaussianTail_map_splitSum 2 2
    rw [hsplit, Measure.map_id] at h
    exact h.symm
  rwa [hs] at hh

end NLA.FR05
