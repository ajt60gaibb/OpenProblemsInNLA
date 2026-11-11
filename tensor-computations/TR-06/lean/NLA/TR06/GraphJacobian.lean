/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.Definitions
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace NLA.TR06

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- The actual paired map into the L2 product: its squared output norm is
`‖A x‖ ^ 2 + ‖B x‖ ^ 2`, not the maximum of the two output norms. -/
def pairedL2Map (A : E →L[ℝ] F) (B : E →L[ℝ] G) :
    E →L[ℝ] WithLp 2 (F × G) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ F G).symm.toContinuousLinearMap.comp (A.prod B)

/-- The graph map x ↦ (x, T x), in the genuine Hilbert product. -/
def graphL2Map (T : E →L[ℝ] F) : E →L[ℝ] WithLp 2 (E × F) :=
  pairedL2Map (ContinuousLinearMap.id ℝ E) T

/-- B after the inverse of A onto its actual range. The range norm is induced
from F. This is the same construction used by the frozen inducedDerivative. -/
def rangeInverseOperator (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (hA : Function.Injective A) : LinearMap.range A.toLinearMap →L[ℝ] G :=
  B.comp (LinearEquiv.ofInjective A.toLinearMap hA).toContinuousLinearEquiv.symm.toContinuousLinearMap

/-- In an orthonormal eigenbasis for T* T, the graph Gram matrix is diagonal
with entries one plus its nonnegative eigenvalues. -/
private theorem normDet_graphL2Map_sq (T : E →L[ℝ] F) :
    (graphL2Map T).toLinearMap.normDet ^ 2 =
      ∏ i, (1 + T.toLinearMap.isSymmetric_adjoint_comp_self.eigenvalues rfl i) := by
  let S := T.toLinearMap.adjoint ∘ₗ T.toLinearMap
  let hS : S.IsSymmetric := T.toLinearMap.isSymmetric_adjoint_comp_self
  let b := hS.eigenvectorBasis rfl
  let ev := hS.eigenvalues rfl
  have heig (i) : S (b i) = ev i • b i := hS.apply_eigenvectorBasis rfl i
  have hgram : Matrix.gram ℝ (fun i => graphL2Map T (b i)) =
      Matrix.diagonal (fun i => 1 + ev i) := by
    ext i j
    change ⟪b i, b j⟫ + ⟪T.toLinearMap (b i), T.toLinearMap (b j)⟫ =
      if i = j then 1 + ev i else 0
    rw [← T.toLinearMap.adjoint_inner_right (b i) (T.toLinearMap (b j))]
    change ⟪b i, b j⟫ + ⟪b i, S (b j)⟫ = _
    rw [heig, inner_smul_right, b.inner_eq_ite]
    by_cases hij : i = j <;> simp [hij]
  have hdet : (graphL2Map T).toLinearMap.normDet ^ 2 =
      (Matrix.gram ℝ (fun i => graphL2Map T (b i))).det := by
    simpa using (graphL2Map T).toLinearMap.normDet_sq_eq_det_gram b
  rw [hgram, Matrix.det_diagonal] at hdet
  exact hdet

/-- The operator norm is bounded by the genuine L2 graph-volume Jacobian,
including a zero-dimensional domain. No numerical certificate is used. -/
theorem opNorm_le_normDet_graphL2Map (T : E →L[ℝ] F) :
    ‖T‖ ≤ (graphL2Map T).toLinearMap.normDet := by
  let S := T.toLinearMap.adjoint ∘ₗ T.toLinearMap
  let hS : S.IsSymmetric := T.toLinearMap.isSymmetric_adjoint_comp_self
  let b := hS.eigenvectorBasis rfl
  let ev := hS.eigenvalues rfl
  let D := (graphL2Map T).toLinearMap.normDet
  have hD : 0 ≤ D := (graphL2Map T).toLinearMap.normDet_nonneg
  have hev (i) : 0 ≤ ev i := T.toLinearMap.isPositive_adjoint_comp_self.nonneg_eigenvalues rfl i
  have hDsq : D ^ 2 = ∏ i, (1 + ev i) := normDet_graphL2Map_sq T
  have hevle (i) : ev i ≤ D ^ 2 := by
    rw [hDsq]
    apply le_trans (show ev i ≤ 1 + ev i by linarith)
    simpa only [Finset.prod_singleton] using
      Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ {i})
        (fun j _ => by linarith [hev j] : ∀ j ∈ ({i} : Finset _), 0 ≤ 1 + ev j)
        (fun j _ _ => by linarith [hev j])
  have heig (i) : S (b i) = ev i • b i := hS.apply_eigenvectorBasis rfl i
  apply T.opNorm_le_bound hD
  intro x
  have hquad : ‖T x‖ ^ 2 = ∑ i, ev i * ⟪b i, x⟫ ^ 2 := by
    calc
      ‖T x‖ ^ 2 = ⟪x, S x⟫ := by
        change ‖T x‖ ^ 2 = ⟪x, T.toLinearMap.adjoint (T x)⟫
        rw [T.toLinearMap.adjoint_inner_right]
        change ‖T x‖ ^ 2 = ⟪T x, T x⟫
        exact (real_inner_self_eq_norm_sq (T x)).symm
      _ = ∑ i, ev i * ⟪b i, x⟫ ^ 2 := by
        rw [← b.sum_inner_mul_inner x (S x)]
        apply Finset.sum_congr rfl
        intro i _
        rw [← hS (b i) x, heig, inner_smul_left, real_inner_comm x (b i)]
        simp only [conj_trivial]
        ring
  have hsquare : ‖T x‖ ^ 2 ≤ (D * ‖x‖) ^ 2 := by
    rw [hquad, mul_pow, ← b.sum_sq_inner_right x, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hevle i) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD (norm_nonneg _))).mp hsquare

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
private theorem normDet_postcomp_linearIsometry (L : F →ₗᵢ[ℝ] G) (A : E →ₗ[ℝ] F) :
    (L.toLinearMap.comp A).normDet = A.normDet := by
  rw [LinearMap.normDet_comp]
  have heq : L.toLinearMap.domRestrict A.range =
      (L.comp A.range.subtypeₗᵢ).toLinearMap := rfl
  rw [heq, LinearIsometry.normDet_eq_one, one_mul]

-- Retain the independently reviewed finite-dimensional F interface; the proof
-- itself only needs the finite-dimensional range of A.
set_option linter.unusedSectionVars false in
/-- For an injective input differential, its volume Jacobian times the
induced angular operator norm is bounded by the L2 paired-map Jacobian. -/
theorem opNorm_rangeInverseOperator_mul_normDet_le
    (A : E →L[ℝ] F) (B : E →L[ℝ] G) (hA : Function.Injective A) :
    ‖rangeInverseOperator A B hA‖ * A.toLinearMap.normDet ≤
      (pairedL2Map A B).toLinearMap.normDet := by
  let e := LinearEquiv.ofInjective A.toLinearMap hA
  let T := rangeInverseOperator A B hA
  let inclusion : WithLp 2 (LinearMap.range A.toLinearMap × G) →ₗᵢ[ℝ] WithLp 2 (F × G) :=
    A.toLinearMap.range.subtypeₗᵢ.withLpProdMap 2 (LinearIsometry.id : G →ₗᵢ[ℝ] G)
  have hT (x : E) : T (e x) = B x := by
    simp [T, rangeInverseOperator, e]
  have hpaired : (pairedL2Map A B).toLinearMap =
      inclusion.toLinearMap.comp ((graphL2Map T).toLinearMap.comp e.toLinearMap) := by
    ext x
    change WithLp.toLp 2 (A x, B x) = WithLp.toLp 2 ((e x).val, T (e x))
    rw [hT]
    rfl
  have hdetA : e.toLinearMap.normDet = A.toLinearMap.normDet := by
    change A.toLinearMap.rangeRestrict.normDet = A.toLinearMap.normDet
    exact LinearMap.normDet_codRestrict _
  calc
    ‖T‖ * A.toLinearMap.normDet ≤ (graphL2Map T).toLinearMap.normDet * A.toLinearMap.normDet :=
      mul_le_mul_of_nonneg_right (opNorm_le_normDet_graphL2Map T) A.toLinearMap.normDet_nonneg
    _ = (pairedL2Map A B).toLinearMap.normDet := by
      rw [hpaired, normDet_postcomp_linearIsometry,
        LinearMap.normDet_comp_of_finrank_eq e.toLinearMap (graphL2Map T).toLinearMap e.finrank_eq,
        hdetA]

#print axioms opNorm_le_normDet_graphL2Map
#print axioms opNorm_rangeInverseOperator_mul_normDet_le
#assert_trust kernel opNorm_le_normDet_graphL2Map
#assert_trust kernel opNorm_rangeInverseOperator_mul_normDet_le
end NLA.TR06
