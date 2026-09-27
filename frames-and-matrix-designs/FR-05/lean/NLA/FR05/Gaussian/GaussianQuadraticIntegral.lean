import NLA.FR05.Gaussian.GaussianPolarLaw

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Complex Real Matrix
open scoped ComplexOrder

namespace NLA.FR05


theorem integral_scalarGaussian_exp_neg {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, Real.exp (-t * Complex.normSq z) ∂scalarComplexGaussian) = (1 + t)⁻¹ := by
  rw [← integral_map (φ := Complex.normSq) (f := fun s : ℝ ↦ Real.exp (-t * s))
    (by fun_prop) (by fun_prop), scalarComplexGaussian_map_normSq,
    integral_expMeasure_one]
  simp_rw [← Real.exp_add, show ∀ s : ℝ, -s + -t * s = -(1 + t) * s by intro s; ring]
  rw [integral_exp_mul_Ioi (by linarith : -(1 + t) < 0)]
  simp only [mul_zero, Real.exp_zero]
  field_simp

def gaussianQuadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : Signal n) : ℝ :=
  (star z ⬝ᵥ (A *ᵥ z)).re

@[fun_prop] theorem continuous_gaussianQuadratic {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : Continuous (gaussianQuadratic A) := by
  unfold gaussianQuadratic
  fun_prop

theorem gaussianQuadratic_mulVec {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℂ) (z : Signal n) :
    gaussianQuadratic A (U *ᵥ z) = gaussianQuadratic (Uᴴ * A * U) z := by
  unfold gaussianQuadratic
  symm
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]

theorem gaussianQuadratic_diagonal {n : ℕ} (d : Fin n → ℝ) (z : Signal n) :
    gaussianQuadratic (diagonal (fun i ↦ (d i : ℂ))) z =
      ∑ i, d i * Complex.normSq (z i) := by
  unfold gaussianQuadratic dotProduct
  simp only [mulVec_diagonal, Pi.star_apply]
  change Complex.reAddGroupHom (∑ x, star (z x) * ((d x : ℂ) * z x)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem gaussianQuadratic_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (z : Signal n) : 0 ≤ gaussianQuadratic A z :=
  (hA.dotProduct_mulVec_nonneg z).1

theorem integral_gaussianQuadratic_exp {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) :
    (∫ z, Real.exp (-gaussianQuadratic A z) ∂standardComplexGaussianTail n) =
      ∏ i, (1 + hA.1.eigenvalues i)⁻¹ := by
  let U : Matrix (Fin n) (Fin n) ℂ := hA.1.eigenvectorUnitary
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.1.eigenvectorUnitary
  have he : Uᴴ * A * U = diagonal (fun i ↦ (hA.1.eigenvalues i : ℂ)) := by
    simpa [Unitary.conjStarAlgAut_apply, U, Matrix.star_eq_conjTranspose, Function.comp_def] using hA.1.conjStarAlgAut_star_eigenvectorUnitary
  rw [← standardComplexGaussianTail_map_unitary_mulVec U hU,
    integral_map (by fun_prop) (by fun_prop)]
  have hp (z : Signal n) : Real.exp (-gaussianQuadratic A (U *ᵥ z)) =
      ∏ i, Real.exp (-hA.1.eigenvalues i * Complex.normSq (z i)) := by
    rw [gaussianQuadratic_mulVec, he, gaussianQuadratic_diagonal,
      ← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    rw [neg_mul]
  simp_rw [hp]
  rw [standardComplexGaussianTail_eq_pi,
    integral_fintype_prod_eq_prod
      (f := fun i (z : ℂ) ↦ Real.exp (-hA.1.eigenvalues i * Complex.normSq z))]
  congr 1
  funext i
  exact integral_scalarGaussian_exp_neg (hA.eigenvalues_nonneg i)

/-- The determinant of an affine function of a Hermitian matrix is the product
of the same affine function of its eigenvalues. -/
theorem _root_.Matrix.IsHermitian.det_one_add_smul_eq_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (q : ℝ) :
    det (1 + (q : ℂ) • A) = ((∏ i, (1 + q * hA.eigenvalues i) : ℝ) : ℂ) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_one (Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary),
    ← map_smul, ← map_add, Unitary.conjStarAlgAut_apply, det_mul, det_mul]
  have hdet : det (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      det (star (hA.eigenvectorUnitary : Matrix ι ι ℂ)) = 1 := by
    rw [← det_mul, ← Unitary.coe_star, Unitary.coe_mul_star_self, det_one]
  have hdiag : (1 : Matrix ι ι ℂ) + (q : ℂ) •
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) =
      diagonal (fun i ↦ ((1 + q * hA.eigenvalues i : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [hij]
  rw [hdiag, det_diagonal, mul_right_comm, hdet, one_mul, Complex.ofReal_prod]

/-- The determinant factor in the Gaussian quadratic integral. -/
theorem det_one_add_eigenvalues {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) :
    det (1 + A) = ((∏ i, (1 + hA.eigenvalues i) : ℝ) : ℂ) := by
  simpa using hA.det_one_add_smul_eq_prod 1

theorem integral_gaussianQuadratic_exp_det {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) :
    (∫ z, Real.exp (-gaussianQuadratic A z) ∂standardComplexGaussianTail n) =
      (det (1 + A)).re⁻¹ := by
  rw [integral_gaussianQuadratic_exp hA, det_one_add_eigenvalues hA.1, Complex.ofReal_re,
    Finset.prod_inv_distrib]

end NLA.FR05
