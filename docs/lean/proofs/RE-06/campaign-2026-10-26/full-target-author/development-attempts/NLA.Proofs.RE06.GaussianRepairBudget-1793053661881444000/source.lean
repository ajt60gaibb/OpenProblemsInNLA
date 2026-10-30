import NLA.Proofs.RE06.QueryCount

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.RE06.Repair
open NLA.Computation.NonadaptiveMatrixQuery

def oversampledWidth (j : ℕ) (η : ℝ) : ℕ :=
  j+1+Nat.ceil (256*(j:ℝ)/η)

theorem oversampledWidth_strict (j : ℕ) (hj : 0<j) (η : ℝ) (hη : 0<η) :
    j+1<oversampledWidth j η := by
  have hjr : 0<(j:ℝ) := by exact_mod_cast hj
  have hc : 0<Nat.ceil (256*(j:ℝ)/η) := Nat.ceil_pos.mpr (by positivity)
  dsimp only [oversampledWidth]
  omega

theorem oversampledWidth_ratio (j : ℕ) (hj : 0<j) (η : ℝ) (hη : 0<η) :
    0≤(j:ℝ)/((oversampledWidth j η:ℝ)-(j:ℝ)-1) ∧
      (j:ℝ)/((oversampledWidth j η:ℝ)-(j:ℝ)-1)≤η/256 := by
  have hk := oversampledWidth_strict j hj η hη
  have hkr : (j:ℝ)+1<(oversampledWidth j η:ℝ) := by exact_mod_cast hk
  have hden : 0<(oversampledWidth j η:ℝ)-(j:ℝ)-1 := by linarith
  refine ⟨div_nonneg (Nat.cast_nonneg _) hden.le,?_⟩
  have hc := Nat.le_ceil (256*(j:ℝ)/η)
  have he : (Nat.ceil (256*(j:ℝ)/η):ℝ)=(oversampledWidth j η:ℝ)-(j:ℝ)-1 := by
    simp only [oversampledWidth, Nat.cast_add, Nat.cast_one]
    ring
  rw [he] at hc
  have hm := (div_le_iff₀ hη).mp hc
  apply (div_le_iff₀ hden).mpr
  nlinarith

theorem actual_widths_strict (m : ℕ) (ε : ℝ) (hε : 0<ε) :
    rootWidth m+1<secondWidth m ε ∧ secondWidth m ε+1<thirdWidth m ε := by
  have hη : 0<ε/4 := by positivity
  have hk := oversampledWidth_strict (rootWidth m) (Counts.rootWidth_pos m) (ε/4) hη
  have hkp : 0<secondWidth m ε := by
    change rootWidth m+1<secondWidth m ε at hk
    omega
  exact ⟨hk,oversampledWidth_strict (secondWidth m ε) hkp (ε/4) hη⟩

theorem actual_width_ratios (m : ℕ) (ε : ℝ) (hε : 0<ε) :
    0≤(rootWidth m:ℝ)/((secondWidth m ε:ℝ)-(rootWidth m:ℝ)-1) ∧
    (rootWidth m:ℝ)/((secondWidth m ε:ℝ)-(rootWidth m:ℝ)-1)≤(ε/4)/256 ∧
    0≤(secondWidth m ε:ℝ)/((thirdWidth m ε:ℝ)-(secondWidth m ε:ℝ)-1) ∧
    (secondWidth m ε:ℝ)/((thirdWidth m ε:ℝ)-(secondWidth m ε:ℝ)-1)≤(ε/4)/256 := by
  have hη : 0<ε/4 := by positivity
  have hk := oversampledWidth_ratio (rootWidth m) (Counts.rootWidth_pos m) (ε/4) hη
  have hkp : 0<secondWidth m ε := by have h := (actual_widths_strict m ε hε).1; omega
  have hell := oversampledWidth_ratio (secondWidth m ε) hkp (ε/4) hη
  exact ⟨hk.1,hk.2,hell.1,hell.2⟩

theorem repair_failure_ratio_bound (a b η : ℝ) (hη : 0<η) (hηh : η≤1/8)
    (ha : 0≤a) (hb : 0≤b) (haη : a≤η/256) (hbη : b≤η/256) :
    (a+b+a*b)/η ≤ 1/128+1/524288 := by
  have hab : a*b≤(η/256)*(η/256) := mul_le_mul haη hbη hb (by positivity)
  apply (div_le_iff₀ hη).mpr
  nlinarith

#assert_trust kernel oversampledWidth_strict
#assert_trust kernel oversampledWidth_ratio
#assert_trust kernel actual_widths_strict
#assert_trust kernel actual_width_ratios
#assert_trust kernel repair_failure_ratio_bound
#print axioms repair_failure_ratio_bound
end NLA.Proofs.RE06.Repair
