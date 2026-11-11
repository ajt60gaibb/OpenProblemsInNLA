import NLA.Proofs.TR26.TangentRank

/-! The two chart cover of the literal unweighted cone includes every
projective representative, with its nonzero scalar retained. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem veronese_affine_normalization (d : ℕ) (a b c : ℂ) (ha : a ≠ 0) :
    c • veronese d a b = affineChartVector d (c*a^d) (b/a) := by
  ext i
  simp only [Pi.smul_apply,smul_eq_mul,veronese,affineChartVector,div_pow]
  rw [← mul_div_assoc]
  apply (eq_div_iff (pow_ne_zero i.val ha)).mpr
  calc
    _ = c*(a^(d-i.val)*a^i.val)*b^i.val := by ring
    _ = _ := by rw [← pow_add,Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt)]

theorem veronese_reverse_normalization (d : ℕ) (a b c : ℂ) (hb : b ≠ 0) :
    c • veronese d a b = reverseChartVector d (c*b^d) (a/b) := by
  ext i
  simp only [Pi.smul_apply,smul_eq_mul,veronese,reverseChartVector,div_pow]
  rw [← mul_div_assoc]
  apply (eq_div_iff (pow_ne_zero (d-i.val) hb)).mpr
  calc
    _ = c*(b^i.val*b^(d-i.val))*a^(d-i.val) := by ring
    _ = _ := by
      rw [← pow_add,Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]

theorem onCurve_chart_cover (d : ℕ) (z : CurveVector d) (hz : OnCurve z) :
    (∃ c t : ℂ, c ≠ 0 ∧ z = affineChartVector d c t) ∨
      (∃ c t : ℂ, c ≠ 0 ∧ z = reverseChartVector d c t) := by
  rcases hz with ⟨a,b,c,hab,hc,hz⟩
  have he : z = c • veronese d a b := funext hz
  rcases hab with ha | hb
  · exact Or.inl ⟨c*a^d,b/a,mul_ne_zero hc (pow_ne_zero d ha),
      he.trans (veronese_affine_normalization d a b c ha)⟩
  · exact Or.inr ⟨c*b^d,a/b,mul_ne_zero hc (pow_ne_zero d hb),
      he.trans (veronese_reverse_normalization d a b c hb)⟩

#assert_trust kernel veronese_affine_normalization
#assert_trust kernel veronese_reverse_normalization
#assert_trust kernel onCurve_chart_cover
#print axioms onCurve_chart_cover
end NLA.Proofs.TR26
