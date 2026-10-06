/-
A fixed orthonormal compression preserves the actual rectangular Gaussian law.
The independently approved contract is reviews/gaussian-append-specification.md.
This theorem concerns a deterministic compression; no random measurable
orthonormal selector or independence with another matrix statistic is asserted.
-/
import NLA.IE06.GaussianRegression
import NLA.IE06.SpectralStacking

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace
namespace NLA.IE06.GaussianCompression
open GaussianNull GaussianQuadratic GaussianRegression Spectral

theorem stdGaussian_adjoint {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℝ)
    (hU : Uᴴ * U = 1) :
    (stdGaussian (E n)).map (euclideanMap U).adjoint = stdGaussian (E k) := by
  apply Measure.ext_of_charFun
  ext t
  have heq : charFun ((stdGaussian (E n)).map (euclideanMap U).adjoint) t =
      charFun (stdGaussian (E n)) (euclideanMap U t) := by
    rw [charFun_apply, integral_map (by fun_prop) (by fun_prop), charFun_apply]
    apply integral_congr_ae
    filter_upwards [] with z
    congr 3
    exact LinearMap.adjoint_inner_left (euclideanMap U) t z
  rw [heq, charFun_stdGaussian, charFun_stdGaussian,
    SpectralStacking.norm_map_of_orthonormal_columns U hU]

def compressVector {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℝ)
    (z : Fin n → ℝ) : Fin k → ℝ := ofLp ((euclideanMap U).adjoint (toLp 2 z))

theorem compressVector_measurable {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℝ) :
    Measurable (compressVector U) := by
  unfold compressVector
  fun_prop

theorem gaussian_compressVector {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℝ)
    (hU : Uᴴ * U = 1) :
    (gaussianVector n).map (compressVector U) = gaussianVector k := by
  have h := stdGaussian_adjoint U hU
  rw [← map_pi_eq_stdGaussian, ← map_pi_eq_stdGaussian] at h
  have hh := congrArg (fun μ : Measure (E k) => μ.map ofLp) h
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at hh
  change (gaussianVector n).map (fun z => ofLp ((euclideanMap U).adjoint (toLp 2 z))) = gaussianVector k
  simpa [Function.comp_def, gaussianVector] using hh

def compressRows {n k p : ℕ} (U : Matrix (Fin n) (Fin k) ℝ)
    (G : RectMat p n) : RectMat p k := fun i => compressVector U (G i)

theorem compressRows_measurePreserving {n k p : ℕ} (U : Matrix (Fin n) (Fin k) ℝ)
    (hU : Uᴴ * U = 1) :
    MeasurePreserving (compressRows (p := p) U) (gaussianRect p n) (gaussianRect p k) := by
  exact measurePreserving_pi (fun _ : Fin p => gaussianVector n) (fun _ : Fin p => gaussianVector k)
    (fun _ => ⟨compressVector_measurable U, gaussian_compressVector U hU⟩)

def compress {n k p : ℕ} (U : Matrix (Fin n) (Fin k) ℝ)
    (G : RectMat n p) : RectMat k p := fun i j => (Uᴴ * Matrix.of G) i j

theorem compress_eq_transpose {n k p : ℕ} (U : Matrix (Fin n) (Fin k) ℝ)
    (G : RectMat n p) : compress U G = GaussianRegression.transpose (compressRows U (GaussianRegression.transpose G)) := by
  funext i j
  simp only [compress, GaussianRegression.transpose, compressRows, compressVector, euclideanMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rfl

theorem compress_measurePreserving {n k p : ℕ} (U : Matrix (Fin n) (Fin k) ℝ)
    (hU : Uᴴ * U = 1) :
    MeasurePreserving (compress (p := p) U) (gaussianRect n p) (gaussianRect k p) := by
  have ht (a b : ℕ) : MeasurePreserving (@GaussianRegression.transpose a b) (gaussianRect a b) (gaussianRect b a) :=
    ⟨by unfold GaussianRegression.transpose; fun_prop, gaussian_transpose a b⟩
  convert (ht p k).comp ((compressRows_measurePreserving U hU).comp (ht n p)) using 1
  funext G
  exact compress_eq_transpose U G

#assert_trust kernel stdGaussian_adjoint
#assert_trust kernel compressVector
#assert_trust kernel compressVector_measurable
#assert_trust kernel gaussian_compressVector
#assert_trust kernel compressRows
#assert_trust kernel compressRows_measurePreserving
#assert_trust kernel compress
#assert_trust kernel compress_eq_transpose
#assert_trust kernel compress_measurePreserving
#print axioms stdGaussian_adjoint
#print axioms compress_measurePreserving
end NLA.IE06.GaussianCompression
