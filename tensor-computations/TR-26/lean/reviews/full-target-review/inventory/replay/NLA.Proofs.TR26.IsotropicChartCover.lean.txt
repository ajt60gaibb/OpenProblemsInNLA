import NLA.Proofs.TR26.BinaryScaling
import NLA.Proofs.TR26.TangentRank
import NLA.Proofs.TR26.IsotropicFamilyFactor

/-! Every actual isotropic point of the unweighted curve lies in the first
affine chart. No isotropic point at infinity is discarded: the actual binary
denominator evaluates to one at (0,1). -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem denominator_smul (d : ℕ) (c : ℂ) (z : CurveVector d) :
    denominator (c • z) = c^2 * denominator z := by
  unfold denominator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

theorem denominator_affineChartVector (d : ℕ) (c t : ℂ) :
    denominator (affineChartVector d c t) = c^2 * (affineDenominator d).eval t := by
  have hz : affineChartVector d c t = c • veronese d 1 t := by
    ext i
    simp [affineChartVector,veronese]
  rw [hz,denominator_smul,← binaryDenominator_eval,binaryDenominator_eval_one_eq_affine]

theorem isotropic_onCurve_affine_cover (d : ℕ) (z : CurveVector d)
    (hzcurve : OnCurve z) (hziso : denominator z = 0) :
    ∃ c t : ℂ, c ≠ 0 ∧ z = affineChartVector d c t ∧
      (affineDenominator d).eval t = 0 := by
  rcases hzcurve with ⟨a,b,c,hab,hc,hz⟩
  have hzscale : z = c • veronese d a b := by
    ext i
    exact hz i
  have hD : binaryEval (binaryDenominator d) a b = 0 := by
    have hden : denominator z = c^2 * binaryEval (binaryDenominator d) a b := by
      rw [hzscale,denominator_smul,binaryDenominator_eval]
    rw [hziso] at hden
    exact (mul_eq_zero.mp hden.symm).resolve_left (pow_ne_zero 2 hc)
  have ha : a ≠ 0 := by
    intro ha
    have hb : b ≠ 0 := by simpa [ha] using hab
    have he := binaryEval_homogeneous_smul (2*d) (binaryDenominator d)
      (binaryDenominatorOver_homogeneous ℂ d) 0 1 b
    simp only [mul_zero,mul_one,binaryDenominator_eval_zero_one] at he
    rw [ha,he] at hD
    exact pow_ne_zero (2*d) hb hD
  have hc' : c*a^d ≠ 0 := mul_ne_zero hc (pow_ne_zero d ha)
  have hchart : z = affineChartVector d (c*a^d) (b/a) := by
    ext i
    rw [hz i]
    simp only [veronese,affineChartVector,div_pow]
    rw [← mul_div_assoc]
    apply (eq_div_iff (pow_ne_zero i.val ha)).mpr
    calc
      _ = c*(a^(d-i.val)*a^i.val)*b^i.val := by ring
      _ = _ := by rw [← pow_add,Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt)]
  refine ⟨c*a^d,b/a,hc',hchart,?_⟩
  have hh := denominator_affineChartVector d (c*a^d) (b/a)
  rw [← hchart,hziso] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero 2 hc')

#assert_trust kernel denominator_smul
#assert_trust kernel denominator_affineChartVector
#assert_trust kernel isotropic_onCurve_affine_cover
#print axioms isotropic_onCurve_affine_cover
end NLA.Proofs.TR26
