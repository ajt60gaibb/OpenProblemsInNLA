import NLA.Proofs.RA10.MatrixDividedDifference
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! The second divided-difference matrix is negative semidefinite for an
operator-monotone function on the positive half-line. The proof uses an
arrowhead perturbation and the already proved compression inequality. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Matrix Filter Topology
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace NLA.Proofs.RA10

theorem real_dslope_comm (f : ℝ → ℝ) (a b : ℝ) : dslope f a b = dslope f b a := by
  by_cases h : b = a
  · subst b; rfl
  · rw [dslope_of_ne f h, dslope_of_ne f (Ne.symm h)]
    exact slope_comm f a b

theorem real_dslope_dslope_swap {f : ℝ → ℝ} {a c x : ℝ}
    (hac : a ≠ c) (hxc : x ≠ c) (hd : DifferentiableAt ℝ f a) :
    dslope (dslope f a) c x = dslope (dslope f c) a x := by
  by_cases hxa : x = a
  · subst x
    have hg := ((hd.hasDerivAt.sub_const (f c)).div
      ((hasDerivAt_id a).sub_const c) (sub_ne_zero.mpr hac))
    have he : (fun x : ℝ => (f x - f c) / (x - c)) =ᶠ[𝓝 a] dslope f c := by
      filter_upwards [(dslope_eventuallyEq_slope_of_ne f hac).symm] with x hx
      simpa only [slope_def_field] using hx
    have hdg := (hg.congr_of_eventuallyEq he.symm).deriv
    rw [dslope_same, hdg, dslope_of_ne _ hac, slope_def_field,
      dslope_same, dslope_of_ne _ hac.symm, slope_def_field]
    simp only [id_eq]
    field_simp
    ring
  · rw [dslope_of_ne _ hxc, dslope_of_ne _ hxa, slope_def_field, slope_def_field,
      dslope_of_ne _ hxa, dslope_of_ne _ hac.symm,
      dslope_of_ne _ hxc, dslope_of_ne _ hac,
      slope_def_field, slope_def_field, slope_def_field, slope_def_field]
    field_simp
    ring

def arrowheadDirection {ι : Type*} : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  fromBlocks 0 (fun _ _ => 1) (fun _ _ => 1) 0

theorem arrowheadDirection_isHermitian {ι : Type*} :
    (arrowheadDirection (ι := ι)).IsHermitian := by
  apply isHermitian_iff_isSymm.mpr
  ext i j
  cases i <;> cases j <;> rfl

theorem arrowhead_second_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ℝ → ℝ) (a : ι → ℝ) (c t : ℝ) (i j : ι) :
    (cfc f (diagonal (Sum.elim a (fun _ : Unit => c)) + t • arrowheadDirection (ι := ι))
      - diagonal (fun k => f (Sum.elim a (fun _ : Unit => c) k))) (Sum.inl i) (Sum.inl j) =
      t ^ 2 * ∑ k : ι,
        cfc (dslope (dslope f (a j)) c)
          (diagonal (Sum.elim a (fun _ : Unit => c)) + t • arrowheadDirection (ι := ι))
          (Sum.inl i) (Sum.inl k) := by
  rw [matrix_cfc_diagonal_perturbation f _ arrowheadDirection_isHermitian]
  simp only [mul_apply, Fintype.sum_sum_type, arrowheadDirection, fromBlocks, of_apply,
    Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, mul_zero, Finset.sum_const_zero,
    mul_one, Fintype.sum_unique, zero_add]
  have h := matrix_cfc_diagonal_perturbation (dslope f (a j))
    (Sum.elim a (fun _ : Unit => c)) arrowheadDirection_isHermitian t (Sum.inl i) (Sum.inr ())
  simp only [Matrix.sub_apply, Matrix.diagonal_apply, Sum.inl_ne_inr, ↓reduceIte, sub_zero,
    Sum.elim_inr, Sum.elim_inl, mul_apply, Fintype.sum_sum_type, arrowheadDirection,
    fromBlocks, of_apply, Matrix.zero_apply,
    mul_one, mul_zero, Finset.sum_const_zero, add_zero] at h
  rw [h]
  ring

theorem operatorMonotone_kraus {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℝ → ℝ} (hf : OperatorMonotoneOnPositive f)
    (hc : ContinuousOn f (Set.Ioi 0))
    (hd : ∀ x > 0, DifferentiableAt ℝ f x)
    {c : ℝ} (hcpos : 0 < c) {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (hac : ∀ i, a i ≠ c) :
    Matrix.PosSemidef (fun i j => -dslope (dslope f c) (a j) (a i)) := by
  let d : ι ⊕ Unit → ℝ := Sum.elim a (fun _ => c)
  let X : ℝ → Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
    fun t => diagonal d + t • arrowheadDirection
  let N : ℝ → Matrix ι ι ℝ := fun t i j =>
    ∑ k : ι, cfc (dslope (dslope f (a j)) c) (X t) (Sum.inl i) (Sum.inl k)
  have hdpos : (diagonal d).PosDef := posDef_diagonal_iff.mpr (by
    intro i; cases i with
    | inl i => exact ha i
    | inr i => exact hcpos)
  have hXlim : Tendsto X (𝓝[≠] 0) (𝓝 (diagonal d)) := by
    have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [zero_smul, add_zero] using
      tendsto_const_nhds.add (ht.smul (tendsto_const_nhds (x := arrowheadDirection (ι := ι))))
  have hXherm (t : ℝ) : (X t).IsHermitian :=
    (isHermitian_diagonal d).add (arrowheadDirection_isHermitian.smul
      (show IsSelfAdjoint t from rfl))
  have hNlim : Tendsto N (𝓝[≠] 0)
      (𝓝 (fun i j => dslope (dslope f (a j)) c (a i))) := by
    apply tendsto_pi_nhds.mpr; intro i
    apply tendsto_pi_nhds.mpr; intro j
    have hc₁ : ContinuousOn (dslope f (a j)) (Set.Ioi 0) :=
      (continuousOn_dslope (isOpen_Ioi.mem_nhds (ha j))).mpr ⟨hc, hd _ (ha j)⟩
    have hc₂ : ContinuousOn (dslope (dslope f (a j)) c) (Set.Ioi 0) :=
      (continuousOn_dslope (isOpen_Ioi.mem_nhds hcpos)).mpr
        ⟨hc₁, (differentiableAt_dslope_of_ne (Ne.symm (hac j))).mpr (hd _ hcpos)⟩
    have hcf := matrix_cfc_tendsto_positive hc₂ hXlim hdpos
      (Eventually.of_forall hXherm)
    have hh := tendsto_finsetSum Finset.univ (fun k _ =>
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hcf (Sum.inl i)) (Sum.inl k))
    simpa [N, matrix_cfc_diagonal, diagonal_apply, d] using hh
  have hN : ∀ᶠ t in 𝓝[≠] (0 : ℝ), (-N t).PosSemidef := by
    filter_upwards [matrix_posDef_eventually hXlim hdpos (Eventually.of_forall hXherm),
      self_mem_nhdsWithin] with t ht ht0
    have h := operatorMonotone_compression hf hc ht
    have hblock : (X t).toBlocks₁₁ = diagonal a := by
      ext i j
      simp [X, d, toBlocks₁₁, diagonal_apply, arrowheadDirection, fromBlocks, of_apply]
    rw [hblock, matrix_cfc_diagonal] at h
    have heq : diagonal (fun i => f (a i)) - (cfc f (X t)).toBlocks₁₁ = t ^ 2 • (-N t) := by
      ext i j
      have hh := arrowhead_second_difference f a c t i j
      simp only [Matrix.sub_apply, Matrix.diagonal_apply, Sum.inl.injEq, Sum.elim_inl] at hh
      change (if i = j then f (a i) else 0) - cfc f (X t) (Sum.inl i) (Sum.inl j) =
        t ^ 2 * -(N t i j)
      change cfc f (X t) (Sum.inl i) (Sum.inl j) - (if i = j then f (a i) else 0) =
        t ^ 2 * N t i j at hh
      linarith
    rw [heq] at h
    have hscale := h.smul (inv_nonneg.mpr (sq_nonneg t))
    simpa only [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (show t ≠ 0 from ht0)),
      one_smul] using hscale
  have hresult := matrix_posSemidef_tendsto hNlim.neg hN
  have heq : -(fun i j => dslope (dslope f (a j)) c (a i) : Matrix ι ι ℝ) =
      (fun i j => -dslope (dslope f c) (a j) (a i)) := by
    ext i j
    exact congrArg Neg.neg (real_dslope_dslope_swap (hac j) (hac i) (hd _ (ha j)))
  exact heq ▸ hresult

#assert_trust kernel real_dslope_comm
#assert_trust kernel real_dslope_dslope_swap
#assert_trust kernel arrowheadDirection_isHermitian
#assert_trust kernel arrowhead_second_difference
#assert_trust kernel operatorMonotone_kraus
#print axioms operatorMonotone_kraus

end NLA.Proofs.RA10
