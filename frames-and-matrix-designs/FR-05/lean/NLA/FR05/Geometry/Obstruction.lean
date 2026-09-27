/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NLA.FR05.Definitions

/-!
# Phase retrieval: coordinate invariance and obstructions

The first section gives the deterministic API for transporting measurement
equalities and global phase through linear maps. Invertible changes of signal
coordinates preserve phase-retrieval injectivity, without any unitarity assumption.

The second section turns a rank-one-difference kernel certificate into an
obstruction to injectivity. This is the exact bridge used in Lemma 2.1 and the
planted-law proof. No probability or quotient-space construction is used here.
-/

set_option autoImplicit false
open scoped BigOperators ComplexConjugate Matrix
noncomputable section

namespace NLA.FR05

section Invariance

variable {m d e : ℕ}

/-- A complex-linear map preserves global phase. -/
theorem GloballyPhased.map {x y : Signal d} (h : GloballyPhased x y)
    (f : Signal d →ₗ[ℂ] Signal e) : GloballyPhased (f x) (f y) := by
  obtain ⟨θ, rfl⟩ := h
  exact ⟨θ, f.map_smul _ _⟩

/-- An invertible complex-linear map preserves and reflects global phase. -/
@[simp]
theorem globallyPhased_linearEquiv_iff (f : Signal d ≃ₗ[ℂ] Signal e) (x y : Signal d) :
    GloballyPhased (f x) (f y) ↔ GloballyPhased x y := by
  constructor
  · intro h
    simpa only [LinearEquiv.coe_coe, f.symm_apply_apply] using h.map f.symm.toLinearMap
  · exact fun h ↦ h.map f.toLinearMap

/-- Multiplying a frame on the right composes its measurements with the
corresponding linear map on signals. The right-hand matrix need not be square. -/
theorem rowMagnitude_mul (A : Frame m d) (B : Matrix (Fin d) (Fin e) ℂ)
    (x : Signal e) (i : Fin m) :
    rowMagnitude (A * B) x i = rowMagnitude A (B *ᵥ x) i := by
  exact congrArg (fun y : Signal m ↦ ‖y i‖) (Matrix.mulVec_mulVec x A B).symm

/-- Measurement equality after a right matrix product is equality on the transformed signals. -/
theorem sameMeasurements_mul (A : Frame m d) (B : Matrix (Fin d) (Fin e) ℂ)
    (x y : Signal e) :
    SameMeasurements (A * B) x y ↔ SameMeasurements A (B *ᵥ x) (B *ᵥ y) := by
  simp only [SameMeasurements, rowMagnitude_mul]

/-- Transport injectivity through any complex-linear change of signal coordinates
that identifies the measurement-equality predicates of two frames. -/
theorem phaseRetrievalInjective_iff_of_linearEquiv (A : Frame m d) (B : Frame m e)
    (f : Signal e ≃ₗ[ℂ] Signal d)
    (h : ∀ x y, SameMeasurements B x y ↔ SameMeasurements A (f x) (f y)) :
    PhaseRetrievalInjective B ↔ PhaseRetrievalInjective A := by
  constructor
  · intro hB x y hxy
    have hphase := hB (f.symm x) (f.symm y) ((h _ _).mpr (by simpa using hxy))
    simpa only [LinearEquiv.coe_coe, f.apply_symm_apply] using hphase.map f.toLinearMap
  · intro hA x y hxy
    exact (globallyPhased_linearEquiv_iff f x y).mp (hA _ _ ((h x y).mp hxy))

/-- Independently rescaling the columns by nonzero complex numbers preserves
phase-retrieval injectivity. The scaling need not preserve norms. -/
theorem phaseRetrievalInjective_mul_diagonal (A : Frame m d) (c : Signal d)
    (hc : ∀ j, c j ≠ 0) :
    PhaseRetrievalInjective (A * Matrix.diagonal c) ↔ PhaseRetrievalInjective A := by
  let f : Signal d ≃ₗ[ℂ] Signal d := LinearEquiv.piCongrRight fun j ↦
    LinearEquiv.smulOfNeZero ℂ ℂ (c j) (hc j)
  have hf (x : Signal d) : Matrix.diagonal c *ᵥ x = f x := by
    ext j
    exact Matrix.mulVec_diagonal c x j
  apply phaseRetrievalInjective_iff_of_linearEquiv A (A * Matrix.diagonal c) f
  intro x y
  simpa only [hf] using sameMeasurements_mul A (Matrix.diagonal c) x y

end Invariance

section Obstruction

/-- The two distinguished signal coordinates are distinct. -/
theorem firstCoordinate_ne_secondCoordinate (d : ℕ) (hd : 2 ≤ d) :
    firstCoordinate d hd ≠ secondCoordinate d hd := by
  simp [firstCoordinate, secondCoordinate]

/-- Two signals with equal measurements that are not globally phased refute
injectivity of the original phase-retrieval predicate. -/
theorem not_phaseRetrievalInjective_of_witness {m d : ℕ} (A : Frame m d)
    (x y : Signal d) (hmeas : SameMeasurements A x y)
    (hnphase : ¬ GloballyPhased x y) :
    ¬ PhaseRetrievalInjective A := by
  intro hinj
  exact hnphase (hinj x y hmeas)

/-- The quadratic form of a rank-one Hermitian outer product is the squared
modulus of the associated linear functional. -/
theorem quadraticForm_vecMulVec {d : ℕ} (a x : Signal d) :
    quadraticForm (Matrix.vecMulVec x (star x)) a =
      (Complex.normSq (star a ⬝ᵥ x) : ℂ) := by
  rw [quadraticForm, Matrix.vecMulVec_mulVec]
  rw [op_smul_eq_smul, dotProduct_smul]
  rw [Matrix.star_dotProduct]
  simp only [Complex.normSq_eq_conj_mul_self, smul_eq_mul, starRingEnd_apply]

/-- Evaluation of a Hermitian quadratic form respects matrix subtraction. -/
theorem quadraticForm_sub {d : ℕ} (a : Signal d)
    (Q R : Matrix (Fin d) (Fin d) ℂ) :
    quadraticForm (Q - R) a = quadraticForm Q a - quadraticForm R a := by
  simp only [quadraticForm, Matrix.sub_mulVec, dotProduct_sub]

/-- The quadratic form of `xxᴴ - yyᴴ` is the difference of the two squared
measurement moduli. -/
theorem quadraticForm_rankOneDifference {d : ℕ} (a x y : Signal d) :
    quadraticForm (rankOneDifference x y) a =
      (Complex.normSq (star a ⬝ᵥ x) - Complex.normSq (star a ⬝ᵥ y) : ℂ) := by
  rw [rankOneDifference, quadraticForm_sub, quadraticForm_vecMulVec,
    quadraticForm_vecMulVec]

/-- Rewriting a row measurement as the norm of its Hermitian linear
functional. -/
theorem rowMagnitude_eq_norm_dotProduct_conjugateRow {m d : ℕ}
    (A : Frame m d) (x : Signal d) (i : Fin m) :
    rowMagnitude A x i = ‖star (conjugateRow A i) ⬝ᵥ x‖ := by
  simp only [rowMagnitude, conjugateRow, star_star]
  rfl

/-- An all-row zero certificate for `xxᴴ - yyᴴ` produces identical
measurement moduli.  This is the exact deterministic bridge used at the end
of Proposition 3.1. -/
theorem sameMeasurements_of_rankOneDifference_quadraticForm_eq_zero
    {m d : ℕ} (A : Frame m d) (x y : Signal d)
    (hzero : ∀ i, quadraticForm (rankOneDifference x y) (conjugateRow A i) = 0) :
    SameMeasurements A x y := by
  intro i
  rw [rowMagnitude_eq_norm_dotProduct_conjugateRow,
    rowMagnitude_eq_norm_dotProduct_conjugateRow]
  have hq := hzero i
  rw [quadraticForm_rankOneDifference] at hq
  have hnormSq : Complex.normSq (star (conjugateRow A i) ⬝ᵥ x) =
      Complex.normSq (star (conjugateRow A i) ⬝ᵥ y) := by
    exact_mod_cast sub_eq_zero.mp hq
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hnormSq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormSq

/-- A rank-one-difference kernel certificate refutes phase-retrieval
injectivity whenever its two signals are genuinely distinct modulo phase. -/
theorem not_phaseRetrievalInjective_of_rankOneDifference_quadraticForm_eq_zero
    {m d : ℕ} (A : Frame m d) (x y : Signal d)
    (hzero : ∀ i, quadraticForm (rankOneDifference x y) (conjugateRow A i) = 0)
    (hnphase : ¬ GloballyPhased x y) :
    ¬ PhaseRetrievalInjective A := by
  apply not_phaseRetrievalInjective_of_witness A x y
  · exact sameMeasurements_of_rankOneDifference_quadraticForm_eq_zero A x y hzero
  · exact hnphase

/-- Every standard basis signal has the same measurements under the flat frame. -/
theorem flatFrame_measurements_equal {m d : ℕ} (i : Fin m) (j k : Fin d) :
    rowMagnitude (flatFrame m d) (standardBasis j) i =
      rowMagnitude (flatFrame m d) (standardBasis k) i := by
  simp [rowMagnitude, flatFrame, standardBasis]

/-- The first and second standard signals cannot differ by a unit complex
phase: evaluating a putative equality at the second coordinate gives `1 = 0`. -/
theorem standardBasis_first_not_globallyPhased_second (d : ℕ) (hd : 2 ≤ d) :
    ¬ GloballyPhased (standardBasis (firstCoordinate d hd))
      (standardBasis (secondCoordinate d hd)) := by
  intro hphase
  obtain ⟨θ, hθ⟩ := hphase
  have hsecond := congrFun hθ (secondCoordinate d hd)
  have hne : secondCoordinate d hd ≠ firstCoordinate d hd :=
    Ne.symm (firstCoordinate_ne_secondCoordinate d hd)
  simp [standardBasis, hne] at hsecond

/-- In every FR-05 ambient dimension there is an explicit frame with a
rank-two ambiguity. This is a kernel-checked base witness only; it is not the
open-neighbourhood or Gaussian-probability assertion of the manuscript. -/
theorem flatFrame_not_phaseRetrievalInjective (d : ℕ) (hd : 2 ≤ d) :
    ¬ PhaseRetrievalInjective (flatFrame (4 * d - 5) d) := by
  apply not_phaseRetrievalInjective_of_witness
    (flatFrame (4 * d - 5) d)
    (standardBasis (firstCoordinate d hd))
    (standardBasis (secondCoordinate d hd))
  · intro i
    exact flatFrame_measurements_equal i _ _
  · exact standardBasis_first_not_globallyPhased_second d hd

end Obstruction

end NLA.FR05
