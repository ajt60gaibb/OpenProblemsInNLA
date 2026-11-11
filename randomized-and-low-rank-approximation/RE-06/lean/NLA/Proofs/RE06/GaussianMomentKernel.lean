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
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    Submodule.subtypeL_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    LinearIsometryEquiv.apply_symm_apply]
  exact (kernelBasis W).repr.apply_symm_apply y

theorem kernelDimension_eq {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ)
    (hW : (W * W.transpose).det ≠ 0) : kernelDimension W = p - d := by
  have hsurj := (Pseudo.gram_det_ne_zero_iff_surjective W).mp hW
  have hsurjE : Function.Surjective (Matrix.toEuclideanLin W) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (WithLp.ofLp y)
    refine ⟨WithLp.toLp 2 x, ?_⟩
    change WithLp.toLp 2 (W.mulVec x) = y
    rw [hx]
  have hdim := (Matrix.toEuclideanLin W).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurjE] at hdim
  simp only [finrank_top, finrank_euclideanSpace, Fintype.card_fin] at hdim
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

theorem kernelCoordinates_normSq {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ)
    (x : GaussianEuclid p) :
    normSq (WithLp.ofLp (kernelCoordinates W x)) =
      ∑ j, ((rowComplement W).mulVec (WithLp.ofLp x) j) ^ 2 := by
  have hn := (kernelBasis W).repr.norm_map ((rowKernel W).orthogonalProjectionOnto x)
  change ‖kernelCoordinates W x‖ = ‖(rowKernel W).orthogonalProjectionOnto x‖ at hn
  calc
    _ = ‖kernelCoordinates W x‖ ^ 2 :=
      (EuclideanSpace.real_norm_sq_eq _).symm
    _ = ‖(rowKernel W).orthogonalProjectionOnto x‖ ^ 2 := by rw [hn]
    _ = ‖(rowKernel W).starProjection x‖ ^ 2 := rfl
    _ = ‖Matrix.toEuclideanLin (rowComplement W) x‖ ^ 2 := by rw [rowKernel_projection]
    _ = _ := EuclideanSpace.real_norm_sq_eq _

theorem rowSchur_kernel_normSq {d p : ℕ} (z : Fin p → ℝ)
    (W : Matrix (Fin d) (Fin p) ℝ) (hW : (W * W.transpose).det ≠ 0) :
    rowSchur z W = normSq (WithLp.ofLp (kernelCoordinates W (WithLp.toLp 2 z))) := by
  rw [kernelCoordinates_normSq, rowSchur_residual_normSq z W hW,
    rowComplement_mulVec]

theorem rowSchur_inverse_integrable {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ)
    (hW : (W * W.transpose).det ≠ 0) (hdp : d + 2 < p) :
    Integrable (fun z : Fin p → ℝ => (rowSchur z W)⁻¹)
      (Measure.pi (fun _ : Fin p => gaussianReal 0 1)) := by
  have hq : 2 < kernelDimension W := by rw [kernelDimension_eq W hW]; omega
  have hlaw := coisometry_coordinates_hasLaw (kernelCoordinates W)
    (kernelCoordinates_coisometry W)
  have hi := normSq_inverse_integrable (kernelDimension W) hq
  have himap : Integrable (fun x : Fin (kernelDimension W) → ℝ => (normSq x)⁻¹)
      ((Measure.pi (fun _ : Fin p => gaussianReal 0 1)).map
        (fun x : Fin p → ℝ => WithLp.ofLp (kernelCoordinates W (WithLp.toLp 2 x)))) := by
    rw [hlaw.map_eq]
    exact hi
  have hicomp := himap.comp_aemeasurable hlaw.aemeasurable
  simpa only [Function.comp_def, ← rowSchur_kernel_normSq _ W hW] using hicomp

theorem rowSchur_inverse_integral {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ)
    (hW : (W * W.transpose).det ≠ 0) (hdp : d + 2 < p) :
    (∫ z : Fin p → ℝ, (rowSchur z W)⁻¹
      ∂Measure.pi (fun _ : Fin p => gaussianReal 0 1)) =
        1 / ((p : ℝ) - (d : ℝ) - 2) := by
  have hq : 2 < kernelDimension W := by rw [kernelDimension_eq W hW]; omega
  have hi := projected_normSq_inverse_integral hq (kernelCoordinates W)
    (kernelCoordinates_coisometry W)
  simp only [← rowSchur_kernel_normSq _ W hW] at hi
  rw [kernelDimension_eq W hW, Nat.cast_sub (by omega : d ≤ p)] at hi
  exact hi

end NLA.Proofs.RE06.GaussianMoment
