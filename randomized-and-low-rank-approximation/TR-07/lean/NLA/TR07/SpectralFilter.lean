import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# A covariance polynomial estimate

The estimate is proved for a symmetric positive semidefinite matrix. The
generally nonsymmetric transition matrix will be handled by diagonal
conjugation, not by assuming it contracts the Euclidean norm.
-/

noncomputable section
open scoped BigOperators
open Matrix Unitary
attribute [local instance] Classical.propDecidable

namespace NLA.TR07

theorem scalar_filter_bound {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) (hxs : x ≤ s)
    (n : ℕ) : x * (1 - x / s) ^ n ≤ s / (n + 1) := by
  let q := 1 - x / s
  have hq0 : 0 ≤ q := by dsimp [q]; exact sub_nonneg.mpr ((div_le_one hs).mpr hxs)
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [div_nonneg hx hs.le]
  have hsum : ((n : ℝ) + 1) * q ^ n ≤ ∑ i ∈ Finset.range (n + 1), q ^ i := by
    calc
      _ = ∑ _i ∈ Finset.range (n + 1), q ^ n := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi =>
        pow_le_pow_of_le_one hq0 hq1 (by have := Finset.mem_range.mp hi; omega)
  have hg := geom_sum_mul_neg q (n + 1)
  have hm := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hq1)
  rw [hg] at hm
  have hp := pow_nonneg hq0 (n + 1)
  have hn : 0 < (n : ℝ) + 1 := by positivity
  apply (le_div_iff₀ hn).mpr
  have he : (1 - q) * s = x := by dsimp [q]; field_simp; ring
  have hb : (((n : ℝ) + 1) * q ^ n * (1 - q)) * s ≤ s := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (show ((n : ℝ) + 1) * q ^ n * (1 - q) ≤ 1 by linarith) hs.le
  calc
    x * (1 - x / s) ^ n * ((n : ℝ) + 1) =
      (((n : ℝ) + 1) * q ^ n * (1 - q)) * s := by
        change x * q ^ n * ((n : ℝ) + 1) = _
        nth_rw 1 [← he]
        ring
    _ ≤ s := hb

theorem eigenvalue_le_of_cap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℝ} (hR : R.PosSemidef) {s : ℝ}
    (hcap : (s • (1 : Matrix ι ι ℝ) - R).PosSemidef) (i : ι) :
    hR.isHermitian.eigenvalues i ≤ s := by
  let v := hR.isHermitian.eigenvectorBasis i
  have hv : (⇑v) ⬝ᵥ (⇑v) = 1 := by
    have hn : inner ℝ v v = 1 := by
      rw [real_inner_self_eq_norm_sq, hR.isHermitian.eigenvectorBasis.orthonormal.1 i]
      norm_num
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hn
  have hh := hcap.dotProduct_mulVec_nonneg (⇑v)
  simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_smul, v, hR.isHermitian.mulVec_eigenvectorBasis, hv, smul_eq_mul, mul_one] at hh
  linarith

theorem spectral_filter_psd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℝ} (hR : R.PosSemidef) {s : ℝ} (hs : 0 < s)
    (hcap : (s • (1 : Matrix ι ι ℝ) - R).PosSemidef) (n : ℕ) :
    ((s / (n + 1)) • (1 : Matrix ι ι ℝ) - R * (1 - s⁻¹ • R) ^ n).PosSemidef := by
  let U := hR.isHermitian.eigenvectorUnitary
  let F := conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  let d : ι → ℝ := hR.isHermitian.eigenvalues
  have hR' : R = F (diagonal d) := by simpa [F, U, d] using hR.isHermitian.spectral_theorem
  have hd : (diagonal (fun i => s / (n + 1) - d i * (1 - s⁻¹ * d i) ^ n)).PosSemidef := by
    rw [posSemidef_diagonal_iff]
    intro i
    apply sub_nonneg.mpr
    simpa [d, div_eq_mul_inv, mul_comm] using
      scalar_filter_bound hs (hR.eigenvalues_nonneg i) (eigenvalue_le_of_cap hR hcap i) n
  have hF : ∀ A : Matrix ι ι ℝ, A.PosSemidef → (F A).PosSemidef := by
    intro A hA
    simpa [F, conjStarAlgAut_apply, star_eq_conjTranspose] using
      hA.mul_mul_conjTranspose_same (U : Matrix ι ι ℝ)
  convert hF _ hd using 1
  rw [hR']
  have hdiag : (diagonal (fun i => s / (n + 1) - d i * (1 - s⁻¹ * d i) ^ n)) =
      (s / (n + 1)) • (1 : Matrix ι ι ℝ) - diagonal d * (1 - s⁻¹ • diagonal d) ^ n := by
    have hbase : (1 : Matrix ι ι ℝ) - s⁻¹ • diagonal d =
        diagonal (fun i => 1 - s⁻¹ * d i) := by
      ext i j
      by_cases h : i = j <;> simp [h, one_apply]
    rw [hbase, diagonal_pow, diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j <;> simp [h, one_apply]
  rw [hdiag]
  simp only [map_sub, map_mul, map_pow, map_smul, map_one]

end NLA.TR07
