import NLA.Proofs.RA10.MatrixFunctionalCalculus

/-! The compression inequality for operator-monotone functions on the positive
half-line. A Schur-complement comparison controls an arbitrary off-diagonal
block; continuity removes the positive scalar perturbation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Matrix Filter Topology
open scoped BigOperators Matrix

namespace NLA.Proofs.RA10

theorem matrix_blockDiagonal_posDef {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ}
    (hA : A.PosDef) (hB : B.PosDef) : (fromBlocks A 0 0 B).PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos (hA.1.fromBlocks (by simp) hB.1)
  intro x hx
  have heq : star x ⬝ᵥ ((fromBlocks A 0 0 B) *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) +
      star (x ∘ Sum.inr) ⬝ᵥ (B *ᵥ (x ∘ Sum.inr)) := by
    simp [dotProduct, mulVec, Fintype.sum_sum_type, Function.comp_def]
  rw [heq]
  by_cases hl : x ∘ Sum.inl = 0
  · have hr : x ∘ Sum.inr ≠ 0 := by
      intro hr
      apply hx
      funext i
      cases i with
      | inl i => exact congrFun hl i
      | inr i => exact congrFun hr i
    exact add_pos_of_nonneg_of_pos (hA.posSemidef.dotProduct_mulVec_nonneg _)
      (hB.dotProduct_mulVec_pos hr)
  · exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos hl)
      (hB.posSemidef.dotProduct_mulVec_nonneg _)

theorem matrix_posSemidef_limit {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ℕ → Matrix ι ι ℝ} {A : Matrix ι ι ℝ}
    (hlim : Tendsto M atTop (𝓝 A)) (hM : ∀ n, (M n).PosSemidef) : A.PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact tendsto_nhds_unique
      (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim j) i)
      (by
        have h := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim i) j
        convert h using 1
        funext n
        exact (Matrix.isHermitian_iff_isSymm.mp (hM n).1).apply i j)
  · intro x
    have hc : Continuous (fun Y : Matrix ι ι ℝ => star x ⬝ᵥ (Y *ᵥ x)) := by
      simp only [dotProduct, mulVec]
      fun_prop
    exact ge_of_tendsto ((hc.tendsto A).comp hlim)
      (Eventually.of_forall fun n => (hM n).dotProduct_mulVec_nonneg x)

theorem matrix_cfc_add_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ℝ → ℝ) {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (c : ℝ) :
    cfc f (A + c • 1) = cfc (fun x => f (x + c)) A := by
  have hc : ContinuousOn f ((fun x : ℝ => x + c) '' spectrum ℝ A) := by
    have : Finite ((fun x : ℝ => x + c) '' spectrum ℝ A) :=
      (A.finite_real_spectrum.image _).to_subtype
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  have h := cfc_comp f (fun x : ℝ => x + c) A hA hc (by fun_prop)
  have heq : cfc (fun x : ℝ => x + c) A = A + c • 1 := by
    simpa only [cfc_id' ℝ A hA, Algebra.algebraMap_eq_smul_one] using!
      cfc_add_const c (fun x : ℝ => x) A (by fun_prop) hA
  rw [heq] at h
  exact h.symm

theorem matrix_cfc_shift_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    {A : Matrix ι ι ℝ} (hA : A.PosDef) {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun n => cfc f (A + s n • 1)) atTop (𝓝 (cfc f A)) := by
  simp_rw [matrix_cfc_add_scalar f hA.1, hA.1.cfc_eq, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply]
  have hd : Tendsto (fun n => diagonal (fun i => f (hA.1.eigenvalues i + s n))) atTop
      (𝓝 (diagonal (fun i => f (hA.1.eigenvalues i)))) := by
    apply ((show Continuous (fun a : ι → ℝ => diagonal a) by fun_prop).tendsto _).comp
    apply tendsto_pi_nhds.mpr
    intro i
    have hc := hf.continuousAt (isOpen_Ioi.mem_nhds (hA.eigenvalues_pos i))
    apply hc.tendsto.comp
    simpa only [add_zero] using tendsto_const_nhds.add hs
  simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
    (tendsto_const_nhds.mul hd).mul tendsto_const_nhds

theorem operatorMonotone_compression_approx {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {f : ℝ → ℝ} (hf : OperatorMonotoneOnPositive f)
    {X : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} (hX : X.PosDef)
    {ε : ℝ} (hε : 0 < ε) :
    (cfc f (X.toBlocks₁₁ + ε • 1) - (cfc f X).toBlocks₁₁).PosSemidef := by
  let A := X.toBlocks₁₁
  let B := X.toBlocks₁₂
  let C := X.toBlocks₂₂
  let D := C + ε⁻¹ • (B.transpose * B)
  have hA : A.PosDef := hX.submatrix Sum.inl_injective
  have hC : C.PosDef := hX.submatrix Sum.inr_injective
  have hE : (ε • (1 : Matrix ι ι ℝ)).PosDef := PosDef.one.smul hε
  have hD : D.PosDef := hC.add_posSemidef (by
    apply PosSemidef.smul _ (inv_nonneg.mpr hε.le)
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self B)
  have hH : (fromBlocks (A + ε • 1) 0 0 D).PosDef :=
    matrix_blockDiagonal_posDef (hA.add hE) hD
  have hcomp : (fromBlocks (ε • (1 : Matrix ι ι ℝ)) (-B) (-B).conjTranspose
      (ε⁻¹ • (B.transpose * B))).PosSemidef := by
    let : Invertible ε := invertibleOfNonzero hε.ne'
    let := hE.isUnit.invertible
    apply (PosDef.fromBlocks₁₁ (-B) _ hE).mpr
    have hinv : (ε • (1 : Matrix ι ι ℝ))⁻¹ = ε⁻¹ • 1 := by
      simpa only [invOf_eq_inv, inv_one] using
        Matrix.inv_smul (A := (1 : Matrix ι ι ℝ)) ε (by simp)
    simp only [hinv, conjTranspose_eq_transpose_of_trivial, transpose_neg,
      Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, smul_neg, sub_self]
    exact (PosSemidef.zero : (0 : Matrix κ κ ℝ).PosSemidef)
  have hdiff : fromBlocks (A + ε • 1) 0 0 D - X =
      fromBlocks (ε • 1) (-B) (-B).conjTranspose (ε⁻¹ • (B.transpose * B)) := by
    ext i j
    cases i with
    | inl i => cases j <;>
      simp [A, B, C, D, fromBlocks, toBlocks₁₁, toBlocks₁₂, toBlocks₂₂]
    | inr i =>
      cases j with
      | inl j =>
        change 0 - X (Sum.inr i) (Sum.inl j) = star (-X (Sum.inl j) (Sum.inr i))
        simpa only [zero_sub, star_neg, star_trivial] using
          congrArg Neg.neg (hX.1.apply (Sum.inl j) (Sum.inr i))
      | inr j => simp [A, B, C, D, fromBlocks, toBlocks₂₂]
  have h := (matrix_operatorMonotone_cfc hf hH hX (hdiff ▸ hcomp)).submatrix Sum.inl
  rw [matrix_cfc_blockDiagonal f (hA.add hE).1 hD.1] at h
  exact h

theorem operatorMonotone_compression {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {f : ℝ → ℝ}
    (hf : OperatorMonotoneOnPositive f) (hcont : ContinuousOn f (Set.Ioi 0))
    {X : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} (hX : X.PosDef) :
    (cfc f X.toBlocks₁₁ - (cfc f X).toBlocks₁₁).PosSemidef := by
  let s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hs : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply matrix_posSemidef_limit
    ((matrix_cfc_shift_tendsto hcont (hX.submatrix Sum.inl_injective) hs).sub tendsto_const_nhds)
  intro n
  exact operatorMonotone_compression_approx hf hX (show 0 < s n by dsimp [s]; positivity)

#assert_trust kernel matrix_blockDiagonal_posDef
#assert_trust kernel matrix_posSemidef_limit
#assert_trust kernel matrix_cfc_add_scalar
#assert_trust kernel matrix_cfc_shift_tendsto
#assert_trust kernel operatorMonotone_compression_approx
#assert_trust kernel operatorMonotone_compression
#print axioms operatorMonotone_compression

end NLA.Proofs.RA10
