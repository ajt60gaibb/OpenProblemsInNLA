/-
Gaussian inverse principal-minor union estimate. The exact unconditional
contract was independently approved before code in
reviews/gaussian-principal-tail-specification.md.
-/
import NLA.IE06.GaussianPrincipalMoments
import NLA.IE06.GaussianOvercrowdingScalars

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators
namespace NLA.IE06.GaussianPrincipalTail
open GaussianNull GaussianRegression GaussianPrincipalMoments
local instance gaussianRect_probability (m n : ℕ) : IsProbabilityMeasure (gaussianRect m n) := by
  unfold gaussianRect
  infer_instance

def principalDet {m n : ℕ} (S : Finset (Fin m)) (G : RectMat m n) : ℝ :=
  ((gram G)⁻¹.submatrix (Subtype.val : S → Fin m) Subtype.val).det

theorem principalDet_nonneg {m n : ℕ} (S : Finset (Fin m)) (G : RectMat m n) :
    0 ≤ principalDet S G :=
  ((Matrix.posSemidef_self_mul_conjTranspose (Matrix.of G)).inv.submatrix Subtype.val).det_nonneg

theorem principal_moment_bound {m n r q : ℕ} (S : Finset (Fin m)) (hS : S.card = r)
    (hq : 0 < q) (hn : m + 2 * q ≤ n) :
    Integrable (fun G : RectMat m n => principalDet S G ^ q) (gaussianRect m n) ∧
    (∫ G : RectMat m n, principalDet S G ^ q ∂gaussianRect m n) ≤
      (Real.exp 1 / q) ^ (r * q) := by
  obtain ⟨hi, he⟩ := gaussian_principal_subset_moment S hn
  refine ⟨hi, he.le.trans ?_⟩
  rw [hS]
  have hrm : r ≤ m := by simpa only [hS, Fintype.card_fin] using S.card_le_univ
  calc
    _ ≤ ∏ _a ∈ Finset.range r, (Real.exp 1 / q) ^ q := by
      apply Finset.prod_le_prod
      · intro a ha
        apply Finset.prod_nonneg
        intro b hb
        exact inv_nonneg.mpr (GaussianSmallest.inverse_moment_factor_pos (n - (m - r) - a) q b
          (by have := Finset.mem_range.mp ha; omega) (Finset.mem_range.mp hb)).le
      · intro a ha
        rw [Finset.prod_inv_distrib]
        exact GaussianOvercrowdingScalars.inverse_moment_denominator_le hq
          (by have := Finset.mem_range.mp ha; omega)
    _ = _ := by simp [pow_mul, Nat.mul_comm r q]

theorem principal_single_tail {m n r q : ℕ} (S : Finset (Fin m)) (hS : S.card = r)
    (hq : 0 < q) (hn : m + 2 * q ≤ n) {a : ℝ} (ha : 0 < a) :
    gaussianRect m n {G | a ≤ principalDet S G} ≤
      ENNReal.ofReal ((Real.exp 1 / q) ^ (r * q) / a ^ q) := by
  obtain ⟨hi, he⟩ := principal_moment_bound S hS hq hn
  have hap : 0 < a ^ q := pow_pos ha q
  have hmkv := mul_meas_ge_le_integral_of_nonneg
    (μ := gaussianRect m n) (f := fun G : RectMat m n => principalDet S G ^ q)
    (Filter.Eventually.of_forall fun G => pow_nonneg (principalDet_nonneg S G) q) hi (a ^ q)
  have hR : 0 ≤ (Real.exp 1 / q) ^ (r * q) / a ^ q := by positivity
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hR).mpr
  change (gaussianRect m n).real {G | a ≤ principalDet S G} ≤ _
  calc
    _ ≤ (gaussianRect m n).real {G | a ^ q ≤ principalDet S G ^ q} :=
      measureReal_mono (fun G hG => pow_le_pow_left₀ ha.le hG q)
    _ ≤ (Real.exp 1 / q) ^ (r * q) / a ^ q := by
      apply (le_div_iff₀ hap).mpr
      simpa only [mul_comm] using hmkv.trans he

/-- Exact finite union bound over all size-r principal subsets. -/
theorem principal_union_tail {m n r q : ℕ} (hq : 0 < q) (_hrm : r ≤ m)
    (hn : m + 2 * q ≤ n) {a : ℝ} (ha : 0 < a) :
    gaussianRect m n {G | ∃ S ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
      a ≤ principalDet S G} ≤
      ENNReal.ofReal ((m.choose r : ℝ) * (Real.exp 1 / q) ^ (r * q) / a ^ q) := by
  let I := (Finset.univ : Finset (Fin m)).powersetCard r
  have hset : {G : RectMat m n | ∃ S ∈ I, a ≤ principalDet S G} =
      ⋃ S ∈ I, {G : RectMat m n | a ≤ principalDet S G} := by ext G; simp
  change gaussianRect m n {G | ∃ S ∈ I, a ≤ principalDet S G} ≤ _
  rw [hset]
  calc
    _ ≤ ∑ S ∈ I, gaussianRect m n {G | a ≤ principalDet S G} := measure_biUnion_finset_le I _
    _ ≤ ∑ _S ∈ I, ENNReal.ofReal ((Real.exp 1 / q) ^ (r * q) / a ^ q) := by
      apply Finset.sum_le_sum
      intro S hS
      exact principal_single_tail S (Finset.mem_powersetCard.mp hS).2 hq hn ha
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, I, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring

#assert_trust kernel principalDet
#assert_trust kernel principalDet_nonneg
#assert_trust kernel principal_moment_bound
#assert_trust kernel principal_single_tail
#assert_trust kernel principal_union_tail
#print axioms principal_union_tail
end NLA.IE06.GaussianPrincipalTail
