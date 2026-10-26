import NLA.Proofs.RE06.QueryCount

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 2000

namespace NLA.Proofs.RE06.Counts
open NLA.Computation.NonadaptiveMatrixQuery

theorem scaled_self_le_div {r η : ℝ} (hr : 0 ≤ r) (hη : 0 < η) (hη1 : η ≤ 1) :
    r ≤ r / η := by
  apply (le_div_iff₀ hη).mpr
  nlinarith

theorem step_ceil_bound (j : ℕ) (hj : 1 ≤ j) (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ 1) :
    ((j + 1 + Nat.ceil (256 * (j : ℝ) / η) : ℕ) : ℝ) ≤ 259 * (j : ℝ) / η := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hdiv : (j : ℝ) ≤ (j : ℝ) / η :=
    scaled_self_le_div (Nat.cast_nonneg j) hη hη1
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ 256 * (j : ℝ) / η by positivity)).le
  have hid : 259 * (j : ℝ) / η = 256 * (j : ℝ) / η + 3 * ((j : ℝ) / η) := by ring
  push_cast
  linarith

theorem firstWidth_bound (m : ℕ) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    (Nat.ceil (32 * (logWidth m : ℝ) / ((rootWidth m : ℝ) * η) + 64 / η ^ 2) : ℝ) ≤
      97 * (rootWidth m : ℝ) / η ^ 2 := by
  let r : ℝ := rootWidth m
  have hr : 1 ≤ r := by
    dsimp [r]
    exact_mod_cast (show 1 ≤ rootWidth m from rootWidth_pos m)
  have hrp : 0 < r := by linarith
  have hL : (logWidth m : ℝ) ≤ r ^ 2 := by
    dsimp [r]
    exact_mod_cast logWidth_le_root_sq m
  have hηsq : 0 < η ^ 2 := sq_pos_of_pos hη
  have hηs : η ^ 2 ≤ η := by nlinarith
  have hηs1 : η ^ 2 ≤ 1 := by nlinarith
  have hfirst : 32 * (logWidth m : ℝ) / (r * η) ≤ 32 * r / η := by
    apply (div_le_div_iff₀ (mul_pos hrp hη) hη).mpr
    have hh := mul_le_mul_of_nonneg_right hL hη.le
    nlinarith
  have hfirst' : 32 * r / η ≤ 32 * r / η ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) hηsq hηs
  have h64 : 64 / η ^ 2 ≤ 64 * r / η ^ 2 := by
    exact div_le_div_of_nonneg_right (by nlinarith) hηsq.le
  have h1 : 1 ≤ r / η ^ 2 := by
    apply (le_div_iff₀ hηsq).mpr
    nlinarith
  have hc := (Nat.ceil_lt_add_one
    (show 0 ≤ 32 * (logWidth m : ℝ) / (r * η) + 64 / η ^ 2 by positivity)).le
  change (Nat.ceil (32 * (logWidth m : ℝ) / (r * η) + 64 / η ^ 2) : ℝ) ≤
    97 * r / η ^ 2
  calc
    _ ≤ 32 * (logWidth m : ℝ) / (r * η) + 64 / η ^ 2 + 1 := hc
    _ ≤ 32 * r / η ^ 2 + 64 * r / η ^ 2 + r / η ^ 2 := by linarith
    _ = 97 * r / η ^ 2 := by ring

theorem total_width_bound (m : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hεh : ε < 1 / 2) :
    ((firstWidth m ε + secondWidth m ε + thirdWidth m ε : ℕ) : ℝ) ≤
      67437 * (rootWidth m : ℝ) / (ε / 4) ^ 2 := by
  let η := ε / 4
  let r : ℝ := rootWidth m
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by dsimp [η]; linarith
  have hr : 1 ≤ rootWidth m := rootWidth_pos m
  have hs := firstWidth_bound m η hη hη1
  have hk := step_ceil_bound (rootWidth m) hr η hη hη1
  have hkn : 1 ≤ secondWidth m ε := by
    dsimp only [secondWidth]
    omega
  have he := step_ceil_bound (secondWidth m ε) hkn η hη hη1
  change (firstWidth m ε : ℝ) ≤ 97 * r / η ^ 2 at hs
  change (secondWidth m ε : ℝ) ≤ 259 * r / η at hk
  change (thirdWidth m ε : ℝ) ≤ 259 * (secondWidth m ε : ℝ) / η at he
  have hk' : (secondWidth m ε : ℝ) ≤ 259 * r / η ^ 2 := by
    have hh : 259 * r / η ≤ 259 * r / η ^ 2 :=
      div_le_div_of_nonneg_left (by dsimp [r]; positivity) (sq_pos_of_pos hη) (by nlinarith)
    exact hk.trans hh
  have he' : (thirdWidth m ε : ℝ) ≤ 67081 * r / η ^ 2 := by
    calc
      _ ≤ 259 * (secondWidth m ε : ℝ) / η := he
      _ ≤ 259 * (259 * r / η) / η := by gcongr
      _ = 67081 * r / η ^ 2 := by ring
  change ((firstWidth m ε + secondWidth m ε + thirdWidth m ε : ℕ) : ℝ) ≤ 67437 * r / η ^ 2
  push_cast
  have hid : 67437 * r / η ^ 2 = 97 * r / η ^ 2 + 259 * r / η ^ 2 + 67081 * r / η ^ 2 := by ring
  linarith

#assert_trust kernel total_width_bound
#print axioms total_width_bound
end NLA.Proofs.RE06.Counts
