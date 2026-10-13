import NLA.Proofs.RA10.OperatorMonotoneKraus
import NLA.Proofs.RA10.MatrixLoewnerCriterion
import NLA.Proofs.RA10.LoewnerAtomMonotonicity

/-! The divided difference of a differentiable operator-monotone function on
the positive half-line is operator antitone, including matrices with the
anchor in their spectrum. Inversion supplies the second Hansen piece. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Statements.RA10 Matrix Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace NLA.Proofs.RA10

theorem orderedPSD_posDef_of_eigenvalues_pos {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {a : Fin n → ℝ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hA : OrderedPSDSpectralDecomposition A a Q) (ha : ∀ i, 0 < a i) : A.PosDef := by
  have hQ : Q.transpose * Q = 1 := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hA.2.2.1 i j
  have hu : IsUnit Q := isUnit_iff_exists_inv.mpr ⟨Q.transpose, mul_eq_one_comm.mp hQ⟩
  rw [hA.2.2.2, spectralMatrix_factor]
  simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
    hu.posDef_star_right_conjugate_iff.mpr (posDef_diagonal_iff.mpr ha)

theorem operatorMonotoneOnPositive_of_cfc {f : ℝ → ℝ}
    (hf : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ),
      A.PosDef → B.PosDef → (A - B).PosSemidef → (cfc f A - cfc f B).PosSemidef) :
    OperatorMonotoneOnPositive f := by
  intro n _ A B a b Q R ha hb hA hB hAB
  apply (sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mpr
  rw [orderedPSD_functionMatrix_eq_cfc f hA, orderedPSD_functionMatrix_eq_cfc f hB]
  exact hf n A B (orderedPSD_posDef_of_eigenvalues_pos hA ha)
    (orderedPSD_posDef_of_eigenvalues_pos hB hb)
    ((sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mp hAB)

theorem operatorMonotoneOnPositive_congr {f g : ℝ → ℝ}
    (hf : OperatorMonotoneOnPositive f) (heq : ∀ x > 0, f x = g x) :
    OperatorMonotoneOnPositive g := by
  intro n hn A B a b Q R ha hb hA hB hAB
  rw [← functionMatrix_congr a Q (fun i => heq _ (ha i)),
    ← functionMatrix_congr b R (fun i => heq _ (hb i))]
  exact hf n hn A B a b Q R ha hb hA hB hAB

theorem operatorMonotoneOnPositive_const_add {f : ℝ → ℝ}
    (hf : OperatorMonotoneOnPositive f) (c : ℝ) :
    OperatorMonotoneOnPositive (fun x => c + f x) := by
  intro n hn A B a b Q R ha hb hA hB hAB
  rw [functionMatrix_add, functionMatrix_add,
    functionMatrix_const c a Q hA.2.2.1, functionMatrix_const c b R hB.2.2.1,
    add_sub_add_left_eq_sub]
  exact hf n hn A B a b Q R ha hb hA hB hAB

theorem real_dslope_neg (f : ℝ → ℝ) (a b : ℝ) :
    dslope (fun x => -f x) a b = -dslope f a b := by
  by_cases h : b = a
  · subst b
    simp only [dslope_same, deriv.fun_neg]
  · rw [dslope_of_ne _ h, dslope_of_ne _ h, slope_def_field, slope_def_field]
    ring

theorem operatorMonotone_neg_dslope {f : ℝ → ℝ}
    (hf : OperatorMonotoneOnPositive f) (hc : ContinuousOn f (Ioi 0))
    (hd : ∀ x > 0, DifferentiableAt ℝ f x) {c : ℝ} (hcpos : 0 < c) :
    OperatorMonotoneOnPositive (fun x => -dslope f c x) := by
  have hsc : ContinuousOn (dslope f c) (Ioi 0) :=
    (continuousOn_dslope (isOpen_Ioi.mem_nhds hcpos)).mpr ⟨hc, hd _ hcpos⟩
  apply operatorMonotoneOnPositive_of_cfc
  intro n A B hA hB hAB
  apply matrix_loewner_monotone (c := c) hsc.neg
    (fun x hx hxc => ((differentiableAt_dslope_of_ne hxc).mpr (hd x hx)).neg) _ hB hA hAB
  intro a ha hac
  change Matrix.PosSemidef (fun i j => dslope (fun x => -dslope f c x) (a j) (a i))
  simpa only [real_dslope_neg] using operatorMonotone_kraus hf hc hd hcpos ha hac

theorem matrix_cfc_comp_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ℝ → ℝ) {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    cfc (fun x => f x⁻¹) A = cfc f A⁻¹ := by
  have hc : ContinuousOn f ((fun x : ℝ => x⁻¹) '' spectrum ℝ A) := by
    have : Finite ((fun x : ℝ => x⁻¹) '' spectrum ℝ A) :=
      (A.finite_real_spectrum.image _).to_subtype
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  simpa only [Matrix.coe_units_inv, IsUnit.unit_spec] using!
    cfc_comp_inv f hA.isUnit.unit (by simpa only [IsUnit.unit_spec] using hc)
      (by simpa only [IsUnit.unit_spec] using (Matrix.isHermitian_iff_isSelfAdjoint.mp hA.1))

theorem operatorMonotone_neg_inverse {f : ℝ → ℝ}
    (hf : OperatorMonotoneOnPositive f) :
    OperatorMonotoneOnPositive (fun x => -f x⁻¹) := by
  apply operatorMonotoneOnPositive_of_cfc
  intro n A B hA hB hAB
  have hinv := matrix_inverse_sub_posSemidef hA.posSemidef hB.posSemidef hAB hA.isUnit hB.isUnit
  have h := matrix_operatorMonotone_cfc hf (posDef_inv_iff.mpr hB) (posDef_inv_iff.mpr hA) hinv
  rw [cfc_neg _ A, cfc_neg _ B,
    matrix_cfc_comp_inverse f hA, matrix_cfc_comp_inverse f hB, neg_sub_neg]
  exact h

theorem real_dslope_neg_inverse_at_one {f : ℝ → ℝ}
    (hd : DifferentiableAt ℝ f 1) {x : ℝ} (hx : x ≠ 0) :
    dslope (fun y => -f y⁻¹) 1 x⁻¹ = x * dslope f 1 x := by
  by_cases hx1 : x = 1
  · subst x
    have hd' : HasDerivAt f (deriv f 1) (1 : ℝ)⁻¹ := by simpa using hd.hasDerivAt
    have hh := (hd'.comp 1 (hasDerivAt_inv (by norm_num : (1 : ℝ) ≠ 0))).neg
    simpa [Function.comp_def] using hh.deriv
  · have hi : x⁻¹ ≠ 1 := by
      intro h
      apply hx1
      simpa only [inv_inv, inv_one] using congrArg (fun r : ℝ => r⁻¹) h
    rw [dslope_of_ne _ hi, dslope_of_ne _ hx1, slope_def_field, slope_def_field,
      inv_inv, inv_one]
    field_simp
    ring

#assert_trust kernel orderedPSD_posDef_of_eigenvalues_pos
#assert_trust kernel operatorMonotoneOnPositive_of_cfc
#assert_trust kernel operatorMonotoneOnPositive_congr
#assert_trust kernel operatorMonotoneOnPositive_const_add
#assert_trust kernel real_dslope_neg
#assert_trust kernel operatorMonotone_neg_dslope
#assert_trust kernel matrix_cfc_comp_inverse
#assert_trust kernel operatorMonotone_neg_inverse
#assert_trust kernel real_dslope_neg_inverse_at_one
#print axioms operatorMonotone_neg_dslope

end NLA.Proofs.RA10
