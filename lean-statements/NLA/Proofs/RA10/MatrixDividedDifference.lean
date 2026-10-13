import NLA.Proofs.RA10.OperatorMonotoneCompression
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Matrix.Order

/-! Exact divided-difference identities for real symmetric matrices. These
identities do not differentiate eigenvalues or choose continuous eigenvectors. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Matrix Filter Topology
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace NLA.Proofs.RA10

theorem matrix_posSemidef_tendsto {ι X : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter X} [l.NeBot] {B : X → Matrix ι ι ℝ} {A : Matrix ι ι ℝ}
    (hlim : Tendsto B l (𝓝 A)) (hB : ∀ᶠ x in l, (B x).PosSemidef) : A.PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    apply tendsto_nhds_unique (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim j) i)
    apply (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim i) j).congr'
    filter_upwards [hB] with x hx
    exact ((Matrix.isHermitian_iff_isSymm.mp hx.1).apply i j).symm
  · intro x
    have hc : Continuous (fun Y : Matrix ι ι ℝ => star x ⬝ᵥ (Y *ᵥ x)) := by
      simp only [dotProduct, mulVec]
      fun_prop
    exact ge_of_tendsto ((hc.tendsto A).comp hlim)
      (hB.mono fun _ h => h.dotProduct_mulVec_nonneg x)

theorem matrix_posDef_eventually {ι X : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter X} {B : X → Matrix ι ι ℝ} {A : Matrix ι ι ℝ}
    (hlim : Tendsto B l (𝓝 A)) (hA : A.PosDef)
    (hB : ∀ᶠ x in l, (B x).IsHermitian) : ∀ᶠ x in l, (B x).PosDef := by
  have hs : Set.Ioi (0 : ℝ) ∈ 𝓝ˢ (spectrum ℝ A) := by
    apply isOpen_Ioi.mem_nhdsSet.mpr
    rw [hA.1.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    exact hA.eigenvalues_pos i
  have he := (upperHemicontinuous_spectrum ℝ (Matrix ι ι ℝ)).upperHemicontinuousAt A _ hs
  filter_upwards [hlim.eventually he, hB] with x hx hherm
  apply hherm.posDef_iff_eigenvalues_pos.mpr
  intro i
  exact subset_of_mem_nhdsSet hx (hherm.eigenvalues_mem_spectrum_real i)

theorem matrix_cfc_continuousOn_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0)) :
    ContinuousOn (fun A : Matrix ι ι ℝ => cfc f A) {A | A.PosDef} := by
  apply ContinuousOn.cfc_of_mem_nhdsSet f (s := Set.Ioi 0) ?_ continuousOn_id
    (fun A hA => hA.1) hf
  apply isOpen_Ioi.mem_nhdsSet.mpr
  intro x hx
  rcases Set.mem_iUnion₂.mp hx with ⟨A, hA, hx⟩
  change x ∈ spectrum ℝ A at hx
  rw [hA.1.spectrum_real_eq_range_eigenvalues] at hx
  rcases hx with ⟨i, rfl⟩
  exact hA.eigenvalues_pos i

theorem matrix_cfc_tendsto_positive {ι X : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    {l : Filter X} {B : X → Matrix ι ι ℝ} {A : Matrix ι ι ℝ}
    (hlim : Tendsto B l (𝓝 A)) (hA : A.PosDef)
    (hB : ∀ᶠ x in l, (B x).IsHermitian) :
    Tendsto (fun x => cfc f (B x)) l (𝓝 (cfc f A)) := by
  exact (matrix_cfc_continuousOn_positive hf A hA).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hlim, matrix_posDef_eventually hlim hA hB⟩)

theorem matrix_cfc_dslope_mul_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ℝ → ℝ) (c : ℝ) {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    cfc (dslope f c) A * (A - c • 1) = cfc f A - f c • 1 := by
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ A) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  have hid : cfc (fun x : ℝ => x - c) A = A - c • 1 := by
    simpa only [cfc_id' ℝ A hA, Algebra.algebraMap_eq_smul_one, neg_smul,
      ← sub_eq_add_neg] using!
      cfc_add_const (-c) (fun x : ℝ => x) A (hc _) hA
  rw [← hid, ← cfc_mul (dslope f c) (fun x : ℝ => x - c) A (hc _) (hc _)]
  have heq : (fun x : ℝ => dslope f c x * (x - c)) = fun x => f x - f c := by
    funext x
    simpa only [smul_eq_mul, mul_comm] using sub_smul_dslope f c x
  rw [heq]
  simpa only [Algebra.algebraMap_eq_smul_one, neg_smul, ← sub_eq_add_neg] using!
    cfc_add_const (-f c) f A (hc _) hA

theorem matrix_cfc_sub_diagonal_column {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ℝ → ℝ) (a : ι → ℝ) {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (i j : ι) :
    (cfc f A - diagonal (fun k => f (a k))) i j =
      (cfc (dslope f (a j)) A * (A - diagonal a)) i j := by
  have h := congrArg (fun M : Matrix ι ι ℝ => M i j)
    (matrix_cfc_dslope_mul_sub f (a j) hA)
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal,
    Matrix.diagonal_apply, Matrix.one_apply] at h ⊢
  split_ifs at h ⊢ with hij <;> simp_all [mul_comm]

theorem matrix_cfc_diagonal_perturbation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ℝ → ℝ) (a : ι → ℝ) {H : Matrix ι ι ℝ} (hH : H.IsHermitian)
    (t : ℝ) (i j : ι) :
    (cfc f (diagonal a + t • H) - diagonal (fun k => f (a k))) i j =
      t * (cfc (dslope f (a j)) (diagonal a + t • H) * H) i j := by
  rw [matrix_cfc_sub_diagonal_column f a ((isHermitian_diagonal a).add (hH.smul (show IsSelfAdjoint t from rfl)))]
  simp only [add_sub_cancel_left, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]

theorem matrix_cfc_diagonal_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (hd : ∀ i, DifferentiableAt ℝ f (a i))
    {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (i j : ι) :
    HasDerivAt (fun t : ℝ => cfc f (diagonal a + t • H) i j)
      (dslope f (a j) (a i) * H i j) 0 := by
  have hc : ContinuousOn (dslope f (a j)) (Set.Ioi 0) :=
    (continuousOn_dslope (isOpen_Ioi.mem_nhds (ha j))).mpr ⟨hf, hd j⟩
  have hlim : Tendsto (fun t : ℝ => diagonal a + t • H) (𝓝[≠] 0) (𝓝 (diagonal a)) := by
    have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [zero_smul, add_zero] using
      tendsto_const_nhds.add (ht.smul (tendsto_const_nhds (x := H)))
  have hcf := matrix_cfc_tendsto_positive hc hlim (posDef_diagonal_iff.mpr ha)
    (Eventually.of_forall fun t => (isHermitian_diagonal a).add (hH.smul (show IsSelfAdjoint t from rfl)))
  have he := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp
    (hcf.mul (tendsto_const_nhds (x := H))) i) j
  rw [matrix_cfc_diagonal, diagonal_mul] at he
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  simp only [slope_def_field, sub_zero, zero_smul, add_zero, matrix_cfc_diagonal]
  have h := matrix_cfc_diagonal_perturbation f a hH t i j
  simp only [Matrix.sub_apply] at h
  rw [h, mul_div_cancel_left₀ _ ht0]

#assert_trust kernel matrix_posSemidef_tendsto
#assert_trust kernel matrix_posDef_eventually
#assert_trust kernel matrix_cfc_continuousOn_positive
#assert_trust kernel matrix_cfc_tendsto_positive
#assert_trust kernel matrix_cfc_dslope_mul_sub
#assert_trust kernel matrix_cfc_sub_diagonal_column
#assert_trust kernel matrix_cfc_diagonal_perturbation
#assert_trust kernel matrix_cfc_diagonal_hasDerivAt

end NLA.Proofs.RA10
