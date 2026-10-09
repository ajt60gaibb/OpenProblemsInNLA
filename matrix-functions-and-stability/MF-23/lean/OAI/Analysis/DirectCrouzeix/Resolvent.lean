import OAI.Analysis.DirectCrouzeix.PositiveBlocks

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

def quadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) : ℂ :=
  inner ℂ u (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u)

theorem quadratic_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) :
    quadratic (A + B) u = quadratic A u + quadratic B u := by
  simp [quadratic]

theorem quadratic_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) :
    quadratic (A - B) u = quadratic A u - quadratic B u := by
  simp [quadratic]

theorem quadratic_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) :
    quadratic (c • A) u = c * quadratic A u := by
  simp [quadratic]

theorem quadratic_one {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) :
    quadratic 1 u = (‖u‖ : ℂ) ^ 2 := by
  simp [quadratic, inner_self_eq_norm_sq_to_K]

theorem quadratic_star {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) :
    quadratic Aᴴ u = star (quadratic A u) := by
  simp only [quadratic, ← Matrix.star_eq_conjTranspose, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

theorem quadratic_vector_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) (c : ℂ) :
    quadratic A (c • u) = (star c * c) * quadratic A u := by
  simp [quadratic]
  ring

theorem quadratic_toLp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : Fin n → ℂ) :
    quadratic A (WithLp.toLp 2 u) = star u ⬝ᵥ (A *ᵥ u) := by
  simp [quadratic, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct_comm]

theorem posSemidef_of_unit_quadratic {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian)
    (hu : ∀ u : EuclideanSpace ℂ (Fin n), ‖u‖ = 1 → 0 ≤ (quadratic H u).re) :
    H.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro x
  refine Complex.nonneg_iff.mpr ⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩
  rw [← quadratic_toLp]
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
  change 0 ≤ (quadratic H v).re
  by_cases hv : v = 0
  · simp [hv, quadratic]
  let u : EuclideanSpace ℂ (Fin n) := ((‖v‖ : ℂ)⁻¹) • v
  have hun : ‖u‖ = 1 := norm_smul_inv_norm hv
  have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hv
  have he : (‖v‖ : ℂ) • u = v := by
    simp [u, smul_smul, hn]
  have hp := hu u hun
  rw [← he, quadratic_vector_smul]
  simpa [pow_two] using mul_nonneg (sq_nonneg ‖v‖) hp

theorem supported_matrix_posSemidef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z q : ℂ)
    (hs : ∀ w ∈ numericalRange A, 0 ≤ (star q * (z - w)).re) :
    (star q • (z • 1 - A) + q • (z • 1 - A)ᴴ).PosSemidef := by
  apply posSemidef_of_unit_quadratic
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      add_comm]
  intro u hu
  have hp := hs (quadratic A u) ⟨u, hu, rfl⟩
  rw [quadratic_add, quadratic_smul, quadratic_smul, quadratic_star,
    quadratic_sub, quadratic_smul, quadratic_one, hu]
  simp only [Complex.ofReal_one, one_pow, mul_one]
  have he : (star q * (z - quadratic A u) + q * star (z - quadratic A u)).re =
      2 * (star q * (z - quadratic A u)).re := by
    simp [Complex.mul_re]
    ring
  rw [he]
  linarith

theorem resolvent_congruence {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsUnit B) (q : ℂ) :
    Bᴴ * ((q • B⁻¹) + (q • B⁻¹)ᴴ) * B = star q • B + q • Bᴴ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det B).mp hB
  have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
  have hstar : Bᴴ * (B⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.conjTranspose_smul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [← Matrix.mul_assoc Bᴴ, hstar, Matrix.one_mul]
  exact add_comm _ _

theorem positive_resolvent_of_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z q : ℂ) (hB : IsUnit (z • 1 - A))
    (hs : ∀ w ∈ numericalRange A, 0 ≤ (star q * (z - w)).re) :
    (q • (z • 1 - A)⁻¹ + (q • (z • 1 - A)⁻¹)ᴴ).PosSemidef := by
  apply (Matrix.IsUnit.posSemidef_star_left_conjugate_iff hB).mp
  rw [Matrix.star_eq_conjTranspose, resolvent_congruence _ hB]
  exact supported_matrix_posSemidef A z q hs

theorem mem_numericalRange_of_eigenvector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {z : ℂ} {x : Fin n → ℂ} (hx : x ≠ 0) (he : A *ᵥ x = z • x) :
    z ∈ numericalRange A := by
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
  have hv : v ≠ 0 := by simpa [v] using hx
  have he' : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A v = z • v := by
    simpa [v, Matrix.toEuclideanCLM_toLp] using congrArg (WithLp.toLp 2) he
  let u : EuclideanSpace ℂ (Fin n) := (‖v‖ : ℂ)⁻¹ • v
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hv
  have heu : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u = z • u := by
    simp [u, he', smul_smul, mul_comm]
  refine ⟨u, hu, ?_⟩
  rw [heu, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
  simp

theorem isUnit_resolvent_of_not_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {z : ℂ} (hz : z ∉ numericalRange A) : IsUnit (z • 1 - A) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  by_contra hh
  have hv : x - y ≠ 0 := sub_ne_zero.mpr hh
  have hzero : (z • 1 - A) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have he : A *ᵥ (x - y) = z • (x - y) := by
    symm
    apply sub_eq_zero.mp
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hzero
  exact hz (mem_numericalRange_of_eigenvector A hv he)

theorem positive_resolvent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z q : ℂ) (hz : z ∉ numericalRange A)
    (hs : ∀ w ∈ numericalRange A, 0 ≤ (star q * (z - w)).re) :
    (q • (z • 1 - A)⁻¹ + (q • (z • 1 - A)⁻¹)ᴴ).PosSemidef :=
  positive_resolvent_of_isUnit A z q (isUnit_resolvent_of_not_mem A hz) hs

end DirectCrouzeix

end

end OAI
