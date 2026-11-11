import NLA.Proofs.TR26.RamificationCharts
import NLA.Proofs.TR26.CurveChartCover
import NLA.Proofs.TR26.IsotropicChartCover

/-! Both charts give an exact characterization for every original projective
representative, with the actual nonisotropic projection retained. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem binaryWronskian_partial_affine_zero_iff {d : ℕ}
    (H : Parameter d) (i : Fin 2) (a b : ℂ) (ha : a ≠ 0) :
    binaryEval (MvPolynomial.pderiv i (binaryWronskian H)) a b = 0 ↔
      binaryEval (MvPolynomial.pderiv i (binaryWronskian H)) 1 (b/a) = 0 := by
  rw [binaryEval_affine_ratio (4*d-2-1) _
    ((binaryWronskianOver_homogeneous H).pderiv (i := i)) a b ha]
  exact mul_eq_zero_iff_left (pow_ne_zero _ ha)

theorem binaryWronskian_partial_reverse_zero_iff {d : ℕ}
    (H : Parameter d) (i : Fin 2) (a b : ℂ) (hb : b ≠ 0) :
    binaryEval (MvPolynomial.pderiv i (binaryWronskian H)) a b = 0 ↔
      binaryEval (MvPolynomial.pderiv i (binaryWronskian H)) (a/b) 1 = 0 := by
  rw [binaryEval_reverse_ratio (4*d-2-1) _
    ((binaryWronskianOver_homogeneous H).pderiv (i := i)) a b hb]
  exact mul_eq_zero_iff_left (pow_ne_zero _ hb)

theorem ramification_original_representative_iff {d : ℕ} (hd : 2 ≤ d)
    (H : Parameter d) (hH : H ≠ 0) (a b c : ℂ)
    (hab : a ≠ 0 ∨ b ≠ 0) (hc : c ≠ 0) :
    Ramification d (c • veronese d a b) H ↔
      binaryEval (MvPolynomial.pderiv 0 (binaryWronskian H)) a b = 0 ∧
      binaryEval (MvPolynomial.pderiv 1 (binaryWronskian H)) a b = 0 := by
  rcases hab with ha | hb
  · rw [veronese_affine_normalization d a b c ha,
      affineChart_ramification_iff_binary_partials hd (c*a^d) (b/a)
        (mul_ne_zero hc (pow_ne_zero d ha)) H hH]
    exact (and_congr (binaryWronskian_partial_affine_zero_iff H 0 a b ha)
      (binaryWronskian_partial_affine_zero_iff H 1 a b ha)).symm
  · rw [veronese_reverse_normalization d a b c hb,
      reverseChart_ramification_iff_binary_partials hd (c*b^d) (a/b)
        (mul_ne_zero hc (pow_ne_zero d hb)) H hH]
    exact (and_congr (binaryWronskian_partial_reverse_zero_iff H 0 a b hb)
      (binaryWronskian_partial_reverse_zero_iff H 1 a b hb)).symm

theorem nonisotropicImage_iff_binary_partials {d : ℕ} (hd : 2 ≤ d)
    (H : Parameter d) :
    H ∈ NonisotropicImage d ↔ H ≠ 0 ∧ ∃ a b : ℂ,
      (a ≠ 0 ∨ b ≠ 0) ∧ binaryEval (binaryDenominator d) a b ≠ 0 ∧
      binaryEval (MvPolynomial.pderiv 0 (binaryWronskian H)) a b = 0 ∧
      binaryEval (MvPolynomial.pderiv 1 (binaryWronskian H)) a b = 0 := by
  constructor
  · rintro ⟨z,hR,hD⟩
    have hH := hR.1.2.1
    rcases hR.1.2.2.1 with ⟨a,b,c,hab,hc,hz⟩
    have hrep : z = c • veronese d a b := funext hz
    have hDab : binaryEval (binaryDenominator d) a b ≠ 0 := by
      intro hzD
      apply hD
      rw [hrep,denominator_smul,← binaryDenominator_eval,hzD,mul_zero]
    have hparts := (ramification_original_representative_iff hd H hH a b c hab hc).mp
      (by rwa [← hrep])
    exact ⟨hH,a,b,hab,hDab,hparts⟩
  · rintro ⟨hH,a,b,hab,hD,ha,hb⟩
    refine ⟨veronese d a b,?_,?_⟩
    · simpa only [one_smul] using
        (ramification_original_representative_iff hd H hH a b 1 hab one_ne_zero).mpr ⟨ha,hb⟩
    · rwa [← binaryDenominator_eval]

theorem exists_ramification_iff_binary_partials {d : ℕ} (hd : 2 ≤ d)
    (H : Parameter d) :
    (∃ z : CurveVector d, Ramification d z H) ↔ H ≠ 0 ∧ ∃ a b : ℂ,
      (a ≠ 0 ∨ b ≠ 0) ∧
      binaryEval (MvPolynomial.pderiv 0 (binaryWronskian H)) a b = 0 ∧
      binaryEval (MvPolynomial.pderiv 1 (binaryWronskian H)) a b = 0 := by
  constructor
  · rintro ⟨z,hR⟩
    have hH := hR.1.2.1
    rcases hR.1.2.2.1 with ⟨a,b,c,hab,hc,hz⟩
    have hrep : z = c • veronese d a b := funext hz
    exact ⟨hH,a,b,hab,(ramification_original_representative_iff hd H hH a b c hab hc).mp
      (by rwa [← hrep])⟩
  · rintro ⟨hH,a,b,hab,ha,hb⟩
    refine ⟨veronese d a b,?_⟩
    simpa only [one_smul] using
      (ramification_original_representative_iff hd H hH a b 1 hab one_ne_zero).mpr ⟨ha,hb⟩

#assert_trust kernel ramification_original_representative_iff
#assert_trust kernel nonisotropicImage_iff_binary_partials
#assert_trust kernel exists_ramification_iff_binary_partials
#print axioms nonisotropicImage_iff_binary_partials
end NLA.Proofs.TR26
