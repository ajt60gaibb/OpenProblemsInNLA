import NLA.Proofs.RE06.GaussianMomentSchur
import NLA.Proofs.RE06.GaussianMomentProjection
import Mathlib.Analysis.Matrix.Hermitian
import NLA.Proofs.RE06.PseudoInverseRankEvents

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

namespace NLA.Proofs.RE06.GaussianMoment

def rowKernel {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ) :
    Submodule ℝ (GaussianEuclid p) := LinearMap.ker (Matrix.toEuclideanLin W)

def kernelDimension {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ) : ℕ :=
  Module.finrank ℝ (rowKernel W)

def kernelBasis {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ) :
    OrthonormalBasis (Fin (kernelDimension W)) ℝ (rowKernel W) :=
  stdOrthonormalBasis ℝ (rowKernel W)

def kernelCoordinates {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ) :
    GaussianEuclid p →L[ℝ] GaussianEuclid (kernelDimension W) :=
  (kernelBasis W).repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (rowKernel W).orthogonalProjectionOnto

theorem kernelCoordinates_coisometry {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ) :
    (kernelCoordinates W).comp (kernelCoordinates W).adjoint =
      ContinuousLinearMap.id ℝ (GaussianEuclid (kernelDimension W)) := by
  simp only [kernelCoordinates, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_orthogonalProjectionOnto]
  change ((kernelBasis W).repr : rowKernel W →L[ℝ] GaussianEuclid (kernelDimension W)) ∘L
    (rowKernel W).orthogonalProjectionOnto ∘L
    ((rowKernel W).subtypeL ∘L
      (((kernelBasis W).repr : rowKernel W →L[ℝ] GaussianEuclid (kernelDimension W)).adjoint)) = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  ext y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    Submodule.subtypeL_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    LinearIsometryEquiv.apply_symm_apply]

theorem kernelDimension_eq {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ)
    (hW : (W * W.transpose).det ≠ 0) : kernelDimension W = p - d := by
  have hsurj := (Pseudo.gram_det_ne_zero_iff_surjective W).mp hW
  have hsurjE : Function.Surjective (Matrix.toEuclideanLin W) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (WithLp.ofLp y)
    refine ⟨WithLp.toLp 2 x, ?_⟩
    change WithLp.toLp 2 (W.mulVec x) = y
    rw [hx]
    rfl
  have hdim := (Matrix.toEuclideanLin W).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurjE] at hdim
  simp only [Submodule.finrank_top, finrank_euclideanSpace, Fintype.card_fin] at hdim
  change d + kernelDimension W = p at hdim
  omega

theorem rowKernel_projection {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ)
    (x : GaussianEuclid p) :
    (rowKernel W).starProjection x = Matrix.toEuclideanLin (rowComplement W) x := by
  have hs : (Matrix.toEuclideanLin (rowComplement W)).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
      simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
        rowComplement_transpose W)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change Matrix.toEuclideanLin W (Matrix.toEuclideanLin (rowComplement W) x) = 0
    apply WithLp.ofLp_injective
    change W.mulVec ((rowComplement W).mulVec (WithLp.ofLp x)) = 0
    rw [Matrix.mulVec_mulVec, rowComplement_killed, Matrix.zero_mulVec]
  · intro y hy
    have hy0 : W.mulVec (WithLp.ofLp y) = 0 := congrArg WithLp.ofLp hy
    have hfix : Matrix.toEuclideanLin (rowComplement W) y = y := by
      apply WithLp.ofLp_injective
      exact rowComplement_fix_kernel W _ hy0
    rw [inner_sub_left, hs x y, hfix, sub_self]

end NLA.Proofs.RE06.GaussianMoment
