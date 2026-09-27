import NLA.FR05.Likelihood.HaarLikelihood

set_option autoImplicit false
noncomputable section

open MeasureTheory Matrix
open scoped BigOperators

namespace NLA.FR05

abbrev SourceOverlapMatrix := Matrix (Fin 2) (Fin 2) ℂ

instance : BorelSpace SourceOverlapMatrix :=
  inferInstanceAs (BorelSpace (Fin 2 → Fin 2 → ℂ))

def sourceOverlap {M : ℕ} (hM : 2 ≤ M) (U V : SourceUnitary M) :
    SourceOverlapMatrix :=
  (sourceTwoFrame hM U)ᴴ * sourceTwoFrame hM V

theorem continuous_sourceOverlap {M : ℕ} (hM : 2 ≤ M) :
    Continuous (fun p : SourceUnitary M × SourceUnitary M ↦ sourceOverlap hM p.1 p.2) :=
  ((continuous_sourceTwoFrame hM).comp continuous_fst).matrix_conjTranspose.matrix_mul
    ((continuous_sourceTwoFrame hM).comp continuous_snd)

/-- The actual overlap law of two independent Haar two-frames. -/
def sourceOverlapLaw (M : ℕ) (hM : 2 ≤ M) : Measure SourceOverlapMatrix :=
  ((sourceUnitaryLaw M).prod (sourceUnitaryLaw M)).map
    (fun p ↦ sourceOverlap hM p.1 p.2)

instance (M : ℕ) (hM : 2 ≤ M) : IsProbabilityMeasure (sourceOverlapLaw M hM) :=
  Measure.isProbabilityMeasure_map (continuous_sourceOverlap hM).measurable.aemeasurable

def overlapFrobeniusSq (K : SourceOverlapMatrix) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (K i j)

def overlapDeterminant (K : SourceOverlapMatrix) : ℝ :=
  (Matrix.det (1 - K * Kᴴ)).re

theorem overlapFrobeniusSq_nonneg (K : SourceOverlapMatrix) :
    0 ≤ overlapFrobeniusSq K :=
  Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ Complex.normSq_nonneg _))

theorem overlapDeterminant_identity (K : SourceOverlapMatrix) :
    overlapDeterminant K = 1 - overlapFrobeniusSq K + Complex.normSq K.det := by
  simp [overlapDeterminant, overlapFrobeniusSq, Matrix.det_fin_two, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem overlap_det_normSq_le (K : SourceOverlapMatrix) :
    4 * Complex.normSq K.det ≤ overlapFrobeniusSq K ^ 2 := by
  have hgram := Complex.normSq_nonneg
    (K 0 0 * star (K 1 0) + K 0 1 * star (K 1 1))
  have hdiff := sq_nonneg
    ((Complex.normSq (K 0 0) + Complex.normSq (K 0 1)) -
      (Complex.normSq (K 1 0) + Complex.normSq (K 1 1)))
  simp [overlapFrobeniusSq, Matrix.det_fin_two, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im] at *
  nlinarith only [hgram, hdiff]

/-- A two-by-two determinant bound avoiding spectral decomposition. -/
theorem overlapDeterminant_le_exp (K : SourceOverlapMatrix)
    (hK : overlapFrobeniusSq K ≤ 2) :
    overlapDeterminant K ≤ Real.exp (-overlapFrobeniusSq K) := by
  have hx := overlapFrobeniusSq_nonneg K
  have hd := overlap_det_normSq_le K
  have he := Real.add_one_le_exp (-overlapFrobeniusSq K / 2)
  have hp := Real.exp_pos (-overlapFrobeniusSq K / 2)
  have hs : (1 - overlapFrobeniusSq K / 2) ^ 2 ≤
      Real.exp (-overlapFrobeniusSq K / 2) ^ 2 := by
    nlinarith
  have heq : Real.exp (-overlapFrobeniusSq K / 2) ^ 2 =
      Real.exp (-overlapFrobeniusSq K) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hs
  rw [overlapDeterminant_identity]
  nlinarith

end NLA.FR05
