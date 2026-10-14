import LeanCert.Tactic.Verification
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The exact scalar step in source RA-10 Lemma 2, Equation (7).
This does not establish the single-eigenvector or positive-part trace bounds. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA10

theorem ridgeCompression_eq7_scalar
    {s c lam : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hlam : 0 < lam) (hlam1 : lam < 1) :
    let μ := lam / (1 + lam)
    lam * (s + c) / 2 ≤
      μ * s + (μ * (2 - μ) * c) / (2 * (1 - μ)) := by
  dsimp
  have hden : 0 < 1 + lam := by linarith
  have hden_ne : (1 + lam : ℝ) ≠ 0 := ne_of_gt hden
  have h_one_sub : 1 - lam / (1 + lam) = 1 / (1 + lam) := by
    field_simp
    ring
  have hcore : 0 ≤ (1 - lam) * s + c := by
    have hnonneg : 0 ≤ (1 - lam) * s :=
      mul_nonneg (by linarith) (le_of_lt hs)
    linarith
  have hgap : 0 ≤ lam * ((1 - lam) * s + c) / (2 * (1 + lam)) :=
    div_nonneg (mul_nonneg (le_of_lt hlam) hcore)
      (by positivity)
  have hidentity :
      lam / (1 + lam) * s +
          ((lam / (1 + lam)) * (2 - lam / (1 + lam)) * c) /
            (2 * (1 - lam / (1 + lam))) =
        lam * (s + c) / 2 +
          lam * ((1 - lam) * s + c) / (2 * (1 + lam)) := by
    rw [h_one_sub]
    field_simp
    ring
  linarith

#assert_trust kernel ridgeCompression_eq7_scalar
#print axioms ridgeCompression_eq7_scalar

end NLA.Proofs.RA10
