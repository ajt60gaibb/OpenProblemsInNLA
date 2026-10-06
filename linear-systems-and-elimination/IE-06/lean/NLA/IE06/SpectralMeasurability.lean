import NLA.IE06.SpectralStacking
import NLA.IE06.KyFan
import NLA.IE06.GaussianRegression

/-! Intrinsic spectral events for the selected-block extension estimate.
No measurable singular-vector or nullspace-basis selection is made. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Matrix Module
namespace NLA.IE06.SpectralMeasurability
open Spectral SpectralStacking KyFan

local instance matrixMeasurable (r c : Type*) : MeasurableSpace (Matrix r c ℝ) :=
  inferInstanceAs (MeasurableSpace (r → c → ℝ))
local instance matrixBorel (r c : Type*) [Fintype r] [Fintype c] : BorelSpace (Matrix r c ℝ) :=
  inferInstanceAs (BorelSpace (r → c → ℝ))

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem singularValues_le_add_opNorm (A B : E →L[ℝ] F) (i : ℕ) :
    A.toLinearMap.singularValues i ≤ B.toLinearMap.singularValues i + ‖A-B‖ := by
  by_cases hi : i < finrank ℝ E
  · let z : Fin (finrank ℝ E) := ⟨i,hi⟩
    let U := A.toLinearMap.isSymmetric_adjoint_comp_self.leadingEigenSubspace rfl
      (Nat.succ_le_of_lt hi)
    let V := B.toLinearMap.isSymmetric_adjoint_comp_self.trailingEigenSubspace rfl z
    obtain ⟨x,hxU,hxV,hx0⟩ :=
      Submodule.exists_ne_zero_mem_inf_of_finrank_lt_add_finrank U V (by
        dsimp only [U,V]
        rw [A.toLinearMap.isSymmetric_adjoint_comp_self.finrank_leadingEigenSubspace,
          B.toLinearMap.isSymmetric_adjoint_comp_self.finrank_trailingEigenSubspace]
        dsimp only [z]
        omega)
    have ha := singularValue_mul_norm_le_of_mem_leading A.toLinearMap rfl z hxU
    have hb := norm_le_singularValue_mul_of_mem_trailing B.toLinearMap rfl z hxV
    have hsub := (A-B).le_opNorm x
    have htri : ‖A x‖ ≤ ‖B x‖ + ‖(A-B) x‖ := by
      have he : A x = B x+(A-B) x := by simp
      rw [he]
      exact norm_add_le _ _
    have hh : A.toLinearMap.singularValues i * ‖x‖ ≤
        (B.toLinearMap.singularValues i+‖A-B‖)*‖x‖ := by
      change A.toLinearMap.singularValues i * ‖x‖ ≤ ‖A x‖ at ha
      change ‖B x‖ ≤ B.toLinearMap.singularValues i * ‖x‖ at hb
      nlinarith only [ha,hb,hsub,htri]
    exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hx0)).mp hh
  · rw [A.toLinearMap.singularValues_of_finrank_le (by omega)]
    exact add_nonneg (B.toLinearMap.singularValues_nonneg _) (norm_nonneg _)

theorem singularValues_lipschitz (i : ℕ) :
    LipschitzWith 1 (fun A : E →L[ℝ] F => A.toLinearMap.singularValues i) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply abs_le.mpr
  have h₁ := singularValues_le_add_opNorm A B i
  have h₂ := singularValues_le_add_opNorm B A i
  rw [norm_sub_rev] at h₂
  constructor <;> linarith

theorem singularValues_le_of_norm_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (A : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] H) (h : ∀ x, ‖A x‖ ≤ ‖B x‖) (i : ℕ) :
    A.singularValues i ≤ B.singularValues i := by
  by_cases hi : i < finrank ℝ E
  · let z : Fin (finrank ℝ E) := ⟨i,hi⟩
    let U := A.isSymmetric_adjoint_comp_self.leadingEigenSubspace rfl (Nat.succ_le_of_lt hi)
    let V := B.isSymmetric_adjoint_comp_self.trailingEigenSubspace rfl z
    obtain ⟨x,hxU,hxV,hx0⟩ :=
      Submodule.exists_ne_zero_mem_inf_of_finrank_lt_add_finrank U V (by
        dsimp only [U,V]
        rw [A.isSymmetric_adjoint_comp_self.finrank_leadingEigenSubspace,
          B.isSymmetric_adjoint_comp_self.finrank_trailingEigenSubspace]
        dsimp only [z]
        omega)
    exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hx0)).mp
      (((singularValue_mul_norm_le_of_mem_leading A rfl z hxU).trans (h x)).trans
        (norm_le_singularValue_mul_of_mem_trailing B rfl z hxV))
  · rw [A.singularValues_of_finrank_le (by omega)]
    exact B.singularValues_nonneg _

theorem singularValues_eq_of_norm_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (A : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] H) (h : ∀ x, ‖A x‖ = ‖B x‖) (i : ℕ) :
    A.singularValues i = B.singularValues i :=
  le_antisymm (singularValues_le_of_norm_le A B (fun x => (h x).le) i)
    (singularValues_le_of_norm_le B A (fun x => (h x).ge) i)

theorem continuous_euclideanMap {r c : Type*} [Fintype r] [Fintype c] [DecidableEq r] [DecidableEq c] :
    Continuous (fun A : Matrix r c ℝ => (euclideanMap A).toContinuousLinearMap) := by
  let L : Matrix r c ℝ →ₗ[ℝ]
      (EuclideanSpace ℝ c →L[ℝ] EuclideanSpace ℝ r) :=
    (LinearMap.toContinuousLinearMap :
      (EuclideanSpace ℝ c →ₗ[ℝ] EuclideanSpace ℝ r) ≃ₗ[ℝ]
      (EuclideanSpace ℝ c →L[ℝ] EuclideanSpace ℝ r)).toLinearMap.comp
      Matrix.toEuclideanLin.toLinearMap
  exact L.continuous_of_finiteDimensional

theorem continuous_singularValue {r c : Type*} [Fintype r] [Fintype c] [DecidableEq r] [DecidableEq c] (i : ℕ) :
    Continuous (fun A : Matrix r c ℝ => singularValue A i) := by
  have h := (singularValues_lipschitz (E := EuclideanSpace ℝ c)
    (F := EuclideanSpace ℝ r) i).continuous.comp
      (continuous_euclideanMap (r := r) (c := c))
  convert h using 1
  funext A
  rfl

theorem measurable_singularValue {r c : Type*} [Fintype r] [Fintype c] [DecidableEq r] [DecidableEq c] (i : ℕ) :
    Measurable (fun A : Matrix r c ℝ => singularValue A i) :=
  (continuous_singularValue i).measurable

theorem continuous_opNorm {r c : Type*} [Fintype r] [Fintype c] [DecidableEq r] [DecidableEq c] :
    Continuous (opNorm : Matrix r c ℝ → ℝ) :=
  continuous_euclideanMap.norm

theorem measurable_opNorm {r c : Type*} [Fintype r] [Fintype c] [DecidableEq r] [DecidableEq c] :
    Measurable (opNorm : Matrix r c ℝ → ℝ) :=
  continuous_opNorm.measurable

theorem measurable_frobeniusNorm {m n : ℕ} :
    Measurable (frobeniusNorm : Matrix (Fin m) (Fin n) ℝ → ℝ) := by
  unfold frobeniusNorm
  fun_prop

/-- A total measurable formula equal to the spectral pseudoinverse on the
full-row-rank locus; no claim of equality is made for singular row Grams. -/
def gramInverse {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  Aᴴ*(A*Aᴴ)⁻¹

theorem measurable_gramInverse {m n : ℕ} : Measurable (@gramInverse m n) := by
  have hg : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => A*Aᴴ) := by
    exact (GaussianRegression.gram_continuous (m := m) (n := n)).measurable
  have hi := (GaussianRegression.measurable_inverse m).comp hg
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [gramInverse, Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.measurable_sum
  intro k _
  have hl : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => star (A k i)) := by fun_prop
  exact hl.mul ((hi.eval).eval)

theorem gramInverse_eq_pinv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (h : Function.Surjective (euclideanMap A)) : gramInverse A = pinv A :=
  (pinv_eq_gram_inverse A (gram_posDef_of_surjective A h).isUnit).symm

theorem surjective_iff_gram_det_ne_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Function.Surjective (euclideanMap A) ↔ (A*Aᴴ).det ≠ 0 := by
  constructor
  · intro h
    exact (Matrix.isUnit_iff_isUnit_det _).mp (gram_posDef_of_surjective A h).isUnit |>.ne_zero
  · intro h
    have hh := mul_pinv_eq_one A ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h))
    intro y
    refine ⟨euclideanMap (pinv A) y, ?_⟩
    have he := congrArg Matrix.toEuclideanLin hh
    simp only [Matrix.toLpLin_mul_same, Matrix.toLpLin_one] at he
    exact congrArg (fun f : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) => f y) he

theorem measurableSet_surjective {m n : ℕ} :
    MeasurableSet {A : Matrix (Fin m) (Fin n) ℝ | Function.Surjective (euclideanMap A)} := by
  simp only [surjective_iff_gram_det_ne_zero]
  have hg : Continuous (fun A : Matrix (Fin m) (Fin n) ℝ => (A*Aᴴ).det) :=
    (GaussianRegression.gram_continuous (m := m) (n := n)).matrix_det
  exact (measurableSet_eq_fun hg.measurable measurable_const).compl

theorem singularValue_rowEquiv {r r' c : Type*} [Fintype r] [Fintype r'] [Fintype c]
    [DecidableEq r] [DecidableEq r'] [DecidableEq c]
    (A : Matrix r c ℝ) (e : r' ≃ r) (i : ℕ) :
    singularValue (A.submatrix e id) i = singularValue A i := by
  apply singularValues_eq_of_norm_eq
  intro x
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have he : ∀ j : r', (euclideanMap (A.submatrix e id) x) j = (euclideanMap A x) (e j) := by
    intro j
    rfl
  simp_rw [he]
  exact Fintype.sum_equiv e _ _ (fun j => rfl)

/-! Transitive kernel audits for each owned declaration. -/
#assert_trust kernel matrixMeasurable
#assert_trust kernel matrixBorel
#print axioms matrixMeasurable
#print axioms matrixBorel
#assert_trust kernel singularValues_le_add_opNorm
#assert_trust kernel singularValues_lipschitz
#assert_trust kernel singularValues_le_of_norm_le
#assert_trust kernel singularValues_eq_of_norm_eq
#assert_trust kernel continuous_euclideanMap
#assert_trust kernel continuous_singularValue
#assert_trust kernel measurable_singularValue
#assert_trust kernel continuous_opNorm
#assert_trust kernel measurable_opNorm
#assert_trust kernel measurable_frobeniusNorm
#assert_trust kernel gramInverse
#assert_trust kernel measurable_gramInverse
#assert_trust kernel gramInverse_eq_pinv
#assert_trust kernel surjective_iff_gram_det_ne_zero
#assert_trust kernel measurableSet_surjective
#assert_trust kernel singularValue_rowEquiv
#print axioms singularValues_le_add_opNorm
#print axioms singularValues_lipschitz
#print axioms singularValues_le_of_norm_le
#print axioms singularValues_eq_of_norm_eq
#print axioms continuous_euclideanMap
#print axioms continuous_singularValue
#print axioms measurable_singularValue
#print axioms continuous_opNorm
#print axioms measurable_opNorm
#print axioms measurable_frobeniusNorm
#print axioms gramInverse
#print axioms measurable_gramInverse
#print axioms gramInverse_eq_pinv
#print axioms surjective_iff_gram_det_ne_zero
#print axioms measurableSet_surjective
#print axioms singularValue_rowEquiv

end NLA.IE06.SpectralMeasurability
