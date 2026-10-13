import NLA.Statements.RA10
import Mathlib.Tactic.Ring

/-! RA-10 exact real-number composition of the source's ridge estimates
(15)–(21). The matrix estimates remain open; this module does not prove the
frozen constant-eleven transfer target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA10

theorem ridgeExcess_le_eleven
    {g e e₀ r F τs : ℝ}
    (hg : 0 ≤ g) (hr : r ≤ e) (he₀ : e₀ ≤ e + r)
    (hfive : F - τs ≤ 5 * g * e₀ + g * r) :
    F - τs ≤ 11 * g * e := by
  have hnumerical : 5 * e₀ + r ≤ 11 * e := by linarith
  have hscaled : g * (5 * e₀ + r) ≤ g * (11 * e) :=
    mul_le_mul_of_nonneg_left hnumerical hg
  nlinarith

theorem ridgeTransfer_of_excess
    {F τs g e ε τ : ℝ}
    (hg : 0 ≤ g) (hε : 0 ≤ ε)
    (hexcess : F - τs ≤ 11 * g * e)
    (he : e ≤ ε * τ) (htail : g * τ ≤ τs) :
    F ≤ (1 + 11 * ε) * τs := by
  have h11g : 0 ≤ 11 * g := mul_nonneg (by norm_num) hg
  have h11ε : 0 ≤ 11 * ε := mul_nonneg (by norm_num) hε
  have hscaled_error : 11 * g * e ≤ 11 * g * (ε * τ) :=
    mul_le_mul_of_nonneg_left he h11g
  have hscaled_tail : 11 * ε * (g * τ) ≤ 11 * ε * τs :=
    mul_le_mul_of_nonneg_left htail h11ε
  nlinarith

#assert_trust kernel ridgeExcess_le_eleven
#assert_trust kernel ridgeTransfer_of_excess
#print axioms ridgeTransfer_of_excess

end NLA.Proofs.RA10
