import NLA.Proofs.SP14.PositivePacketInvisibility
import Mathlib.Data.Nat.Choose.Sum

/-!
Finite negative restoration packet and exact Toeplitz frequency cutoffs.
The raw negative correction is visible at its selected order; only the
restoring term is invisible there. The full restored correction preserves
earlier sections under the source's stage separation.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

noncomputable def negativeL (m q : ℕ) (v : Fin q → ℂ) (s : Circle) : ℂ :=
  ∑ d : Fin q, v d * (s : ℂ) ^ ((d.val : ℤ) - (m : ℤ))

noncomputable def restoringCoeff (m r : ℕ) : ℂ :=
  (-1 : ℂ) ^ (m + 1 + r) * (Nat.choose m r : ℂ) / (2 : ℂ) ^ m

noncomputable def restoringK (m : ℕ) (s : Circle) : ℂ :=
  ∑ r ∈ Finset.range (m + 1), restoringCoeff m r *
    (s : ℂ) ^ (-((m + 1 + r : ℕ) : ℤ))

noncomputable def restoredD (m q : ℕ) (v : Fin q → ℂ) (s : Circle) : ℂ :=
  negativeL m q v s - negativeL m q v (-1) * restoringK m s

noncomputable def restoredNegativePacket (m q : ℕ) (v : Fin q → ℂ)
    (z : Circle) : ℂ :=
  (z : ℂ) * restoredD m q v (z ^ 2)

private theorem restoringK_term_at_neg_one (m r : ℕ) :
    restoringCoeff m r *
        (((-1 : Circle) : ℂ) ^ (-((m + 1 + r : ℕ) : ℤ))) =
      (Nat.choose m r : ℂ) / (2 : ℂ) ^ m := by
  have hp : (-1 : ℂ) ^ (-((m + 1 + r : ℕ) : ℤ)) =
      (-1 : ℂ) ^ (m + 1 + r) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    norm_num
  have hcoe : (((-1 : Circle) : ℂ)) = -1 := by norm_num
  rw [hcoe, hp]
  have hsign : (-1 : ℂ) ^ (m + 1 + r) * (-1 : ℂ) ^ (m + 1 + r) = 1 := by
    rw [← pow_two, ← pow_mul]
    norm_num
  unfold restoringCoeff
  calc
    (-1 : ℂ) ^ (m + 1 + r) * (Nat.choose m r : ℂ) / (2 : ℂ) ^ m *
        (-1 : ℂ) ^ (m + 1 + r) =
      ((-1 : ℂ) ^ (m + 1 + r) * (-1 : ℂ) ^ (m + 1 + r)) *
        ((Nat.choose m r : ℂ) / (2 : ℂ) ^ m) := by ring
    _ = (Nat.choose m r : ℂ) / (2 : ℂ) ^ m := by rw [hsign]; ring

theorem restoringK_at_neg_one (m : ℕ) : restoringK m (-1) = 1 := by
  unfold restoringK
  simp_rw [restoringK_term_at_neg_one]
  rw [← Finset.sum_div]
  norm_cast
  rw [Nat.sum_range_choose]
  norm_num

theorem restoredD_at_neg_one (m q : ℕ) (v : Fin q → ℂ) :
    restoredD m q v (-1) = 0 := by
  simp [restoredD, restoringK_at_neg_one]

private theorem continuous_circle_mode (e : ℤ) :
    Continuous (fun z : Circle => (z : ℂ) ^ e) := by
  have hp : Continuous (fun z : Circle => (z : Circle) ^ e) := continuous_zpow _
  apply (continuous_subtype_val.comp hp).congr
  intro z
  exact Circle.coe_zpow z e

private theorem FourierCoefficient_add_of_continuous
    (a b : Circle → ℂ) (ha : Continuous a) (hb : Continuous b) (k : ℤ) :
    FourierCoefficient (fun z => a z + b z) k =
      FourierCoefficient a k + FourierCoefficient b k := by
  have hca : Continuous (fun t : ℝ =>
      a (Circle.exp t) * Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ)))) := by
    fun_prop
  have hcb : Continuous (fun t : ℝ =>
      b (Circle.exp t) * Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ)))) := by
    fun_prop
  unfold FourierCoefficient
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add
    (hca.intervalIntegrable 0 (2 * Real.pi))
    (hcb.intervalIntegrable 0 (2 * Real.pi))]
  ring

private theorem FourierCoefficient_const_mul (c : ℂ) (b : Circle → ℂ) (k : ℤ) :
    FourierCoefficient (fun z => c * b z) k = c * FourierCoefficient b k := by
  unfold FourierCoefficient
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem FourierCoefficient_sub_of_continuous
    (a b : Circle → ℂ) (ha : Continuous a) (hb : Continuous b) (k : ℤ) :
    FourierCoefficient (fun z => a z - b z) k =
      FourierCoefficient a k - FourierCoefficient b k := by
  have hca : Continuous (fun t : ℝ =>
      a (Circle.exp t) * Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ)))) := by
    fun_prop
  have hcb : Continuous (fun t : ℝ =>
      b (Circle.exp t) * Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ)))) := by
    fun_prop
  unfold FourierCoefficient
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub
    (hca.intervalIntegrable 0 (2 * Real.pi))
    (hcb.intervalIntegrable 0 (2 * Real.pi))]
  ring

private theorem continuous_mode_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (c : α → ℂ) (e : α → ℤ) :
    Continuous (fun z : Circle => ∑ r ∈ s, c r * (z : ℂ) ^ (e r)) := by
  induction s using Finset.induction_on with
  | empty => simpa using (continuous_const : Continuous (fun _ : Circle => (0 : ℂ)))
  | @insert x s hx ih =>
      simp only [Finset.sum_insert hx]
      exact (continuous_const.mul (continuous_circle_mode (e x))).add ih

private theorem FourierCoefficient_mode_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (c : α → ℂ) (e : α → ℤ) (k : ℤ) :
    FourierCoefficient
        (fun z : Circle => ∑ r ∈ s, c r * (z : ℂ) ^ (e r)) k =
      ∑ r ∈ s, c r * (if e r = k then 1 else 0) := by
  induction s using Finset.induction_on with
  | empty =>
      simp [FourierCoefficient]
  | @insert x s hx ih =>
      simp only [Finset.sum_insert hx]
      have hc : Continuous (fun z : Circle => c x * (z : ℂ) ^ (e x)) :=
        continuous_const.mul (continuous_circle_mode (e x))
      have hs := continuous_mode_sum s c e
      rw [FourierCoefficient_add_of_continuous _ _ hc hs k]
      rw [FourierCoefficient_const_mul]
      rw [FourierCoefficient_circle_mode, ih]

private theorem circle_mode_product (z : Circle) (e : ℤ) :
    (z : ℂ) * (((z ^ 2 : Circle) : ℂ) ^ e) =
      (z : ℂ) ^ (1 + 2 * e) := by
  rw [← Circle.coe_zpow, ← Circle.coe_mul]
  calc
    (((z : Circle) * (z ^ 2) ^ e : Circle) : ℂ) =
        ((z : Circle) ^ (1 + 2 * e) : ℂ) := by
          exact congrArg (fun x : Circle => (x : ℂ))
            (show (z : Circle) * (z ^ 2) ^ e = z ^ (1 + 2 * e) by group)
    _ = (z : ℂ) ^ (1 + 2 * e) := by
      rfl

private theorem restoringK_circle_modes (m : ℕ) :
    (fun z : Circle => (z : ℂ) * restoringK m (z ^ 2)) =
      (fun z : Circle => ∑ r ∈ Finset.range (m + 1),
        restoringCoeff m r *
          (z : ℂ) ^ (1 - 2 * ((m + 1 + r : ℕ) : ℤ))) := by
  funext z
  simp only [restoringK, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    (z : ℂ) *
        (restoringCoeff m r *
          (((z ^ 2 : Circle) : ℂ) ^ (-((m + 1 + r : ℕ) : ℤ)))) =
      restoringCoeff m r *
        ((z : ℂ) * (((z ^ 2 : Circle) : ℂ) ^ (-((m + 1 + r : ℕ) : ℤ)))) := by ring
    _ = restoringCoeff m r *
        (z : ℂ) ^ (1 - 2 * ((m + 1 + r : ℕ) : ℤ)) := by
      rw [circle_mode_product]
      ring_nf

private theorem negativeL_circle_modes (m q : ℕ) (v : Fin q → ℂ) :
    (fun z : Circle => (z : ℂ) * negativeL m q v (z ^ 2)) =
      (fun z : Circle => ∑ d : Fin q,
        v d * (z : ℂ) ^ (1 + 2 * ((d.val : ℤ) - (m : ℤ)))) := by
  funext z
  simp only [negativeL, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    (z : ℂ) *
        (v d * (((z ^ 2 : Circle) : ℂ) ^ ((d.val : ℤ) - (m : ℤ)))) =
      v d * ((z : ℂ) *
        (((z ^ 2 : Circle) : ℂ) ^ ((d.val : ℤ) - (m : ℤ)))) := by ring
    _ = v d * (z : ℂ) ^ (1 + 2 * ((d.val : ℤ) - (m : ℤ))) := by
      rw [circle_mode_product]

private theorem continuous_restoring_circle_packet (m : ℕ) :
    Continuous (fun z : Circle => (z : ℂ) * restoringK m (z ^ 2)) := by
  rw [restoringK_circle_modes]
  exact continuous_mode_sum _ _ _

private theorem continuous_negativeL_circle_packet (m q : ℕ) (v : Fin q → ℂ) :
    Continuous (fun z : Circle => (z : ℂ) * negativeL m q v (z ^ 2)) := by
  rw [negativeL_circle_modes]
  exact continuous_mode_sum _ _ _

private theorem restoringPacket_fourier_zero_below (m : ℕ) (k : ℤ)
    (hk : -((2 * m : ℕ) : ℤ) ≤ k) :
    FourierCoefficient (fun z : Circle => (z : ℂ) * restoringK m (z ^ 2)) k = 0 := by
  rw [restoringK_circle_modes, FourierCoefficient_mode_sum]
  apply Finset.sum_eq_zero
  intro r hr
  have hmode : 1 - 2 * ((m + 1 + r : ℕ) : ℤ) ≠ k := by omega
  have hmode' : 1 - 2 * ((m : ℤ) + 1 + (r : ℤ)) ≠ k := by
    simpa only [Nat.cast_add, Nat.cast_one] using hmode
  simp [hmode']

private theorem negativeL_fourier_zero_earlier (m q p : ℕ) (v : Fin q → ℂ)
    (hm : 8 * p ≤ m) (hq : 2 * q ≤ m) (k : ℤ)
    (hk : -((2 * p : ℕ) : ℤ) ≤ k) :
    FourierCoefficient (fun z : Circle => (z : ℂ) * negativeL m q v (z ^ 2)) k = 0 := by
  rw [negativeL_circle_modes, FourierCoefficient_mode_sum]
  apply Finset.sum_eq_zero
  intro d hd
  have hmode : 1 + 2 * ((d.val : ℤ) - (m : ℤ)) ≠ k := by
    have hdi := d.isLt
    omega
  simp [hmode]

/-- The localized restoring term alone has frequencies strictly below the
diagonals of its matching odd Toeplitz section. -/
theorem toeplitz_add_restoration_invisible (a : Circle → ℂ)
    (ha : Continuous a) (τ : ℂ) (m n : ℕ) (hn : n ≤ 2 * m + 1) :
    Toeplitz (fun z => a z + τ * (z : ℂ) * restoringK m (z ^ 2)) n =
      Toeplitz a n := by
  ext i j
  change FourierCoefficient
      (fun z => a z + τ * (z : ℂ) * restoringK m (z ^ 2))
        ((i.val : ℤ) - (j.val : ℤ)) =
      FourierCoefficient a ((i.val : ℤ) - (j.val : ℤ))
  have hk : -((2 * m : ℕ) : ℤ) ≤ (i.val : ℤ) - (j.val : ℤ) := by
    have hj := j.isLt
    omega
  have hcont : Continuous (fun z : Circle =>
      τ * ((z : ℂ) * restoringK m (z ^ 2))) :=
    continuous_const.mul (continuous_restoring_circle_packet m)
  simp only [mul_assoc]
  rw [FourierCoefficient_add_of_continuous a _ ha hcont]
  rw [FourierCoefficient_const_mul]
  rw [restoringPacket_fourier_zero_below m _ hk]
  simp

private theorem restoredNegativePacket_fourier_zero_earlier
    (m q p : ℕ) (v : Fin q → ℂ)
    (hm : 8 * p ≤ m) (hq : 2 * q ≤ m) (k : ℤ)
    (hk : -((2 * p : ℕ) : ℤ) ≤ k) :
    FourierCoefficient (restoredNegativePacket m q v) k = 0 := by
  have hshape : restoredNegativePacket m q v =
      fun z : Circle => (z : ℂ) * negativeL m q v (z ^ 2) -
        negativeL m q v (-1) * ((z : ℂ) * restoringK m (z ^ 2)) := by
    funext z
    simp [restoredNegativePacket, restoredD]
    ring
  rw [hshape]
  rw [FourierCoefficient_sub_of_continuous
    (fun z => (z : ℂ) * negativeL m q v (z ^ 2))
    (fun z => negativeL m q v (-1) * ((z : ℂ) * restoringK m (z ^ 2)))
    (continuous_negativeL_circle_packet m q v)
    (continuous_const.mul (continuous_restoring_circle_packet m)) k]
  rw [FourierCoefficient_const_mul]
  rw [negativeL_fourier_zero_earlier m q p v hm hq k hk]
  have hkK : -((2 * m : ℕ) : ℤ) ≤ k := by omega
  rw [restoringPacket_fourier_zero_below m k hkK]
  simp

/-- A later full restored correction preserves an earlier Toeplitz section
under the exact stage-separation and raw-support bounds. -/
theorem toeplitz_add_restoredNegativePacket_invisible
    (a : Circle → ℂ) (ha : Continuous a)
    (m q p n : ℕ) (v : Fin q → ℂ)
    (hm : 8 * p ≤ m) (hq : 2 * q ≤ m) (hn : n ≤ 2 * p + 1) :
    Toeplitz (fun z => a z + restoredNegativePacket m q v z) n =
      Toeplitz a n := by
  ext i j
  change FourierCoefficient (fun z => a z + restoredNegativePacket m q v z)
      ((i.val : ℤ) - (j.val : ℤ)) =
    FourierCoefficient a ((i.val : ℤ) - (j.val : ℤ))
  have hk : -((2 * p : ℕ) : ℤ) ≤ (i.val : ℤ) - (j.val : ℤ) := by
    have hj := j.isLt
    omega
  have hcont : Continuous (restoredNegativePacket m q v) := by
    have hshape : restoredNegativePacket m q v =
        fun z : Circle => (z : ℂ) * negativeL m q v (z ^ 2) -
          negativeL m q v (-1) * ((z : ℂ) * restoringK m (z ^ 2)) := by
      funext z
      simp [restoredNegativePacket, restoredD]
      ring
    rw [hshape]
    exact (continuous_negativeL_circle_packet m q v).sub
      (continuous_const.mul (continuous_restoring_circle_packet m))
  rw [FourierCoefficient_add_of_continuous a _ ha hcont]
  rw [restoredNegativePacket_fourier_zero_earlier m q p v hm hq _ hk]
  simp

/-- The source's `q = 3m/8` automatically satisfies the raw-support bound. -/
theorem toeplitz_add_restoredNegativePacket_source_stage
    (a : Circle → ℂ) (ha : Continuous a)
    (m p n : ℕ) (v : Fin (3 * m / 8) → ℂ)
    (hm : 8 * p ≤ m) (hn : n ≤ 2 * p + 1) :
    Toeplitz (fun z => a z + restoredNegativePacket m (3 * m / 8) v z) n =
      Toeplitz a n := by
  apply toeplitz_add_restoredNegativePacket_invisible a ha m (3 * m / 8) p n v hm
  · omega
  · exact hn

private theorem restoringCoeff_mode_eq (m r : ℕ) (x : ℂ) :
    restoringCoeff m r * x ^ (-((m + 1 + r : ℕ) : ℤ)) =
      (-(x)) ^ (-((m + 1 : ℕ) : ℤ)) *
        ((-x⁻¹) ^ r * (Nat.choose m r : ℂ)) / (2 : ℂ) ^ m := by
  have hpow (y : ℂ) (n : ℕ) : y ^ (-((n : ℕ) : ℤ)) = (y⁻¹) ^ n := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]
  rw [hpow x (m + 1 + r), hpow (-x) (m + 1)]
  rw [inv_neg]
  unfold restoringCoeff
  calc
    (-1 : ℂ) ^ (m + 1 + r) * (Nat.choose m r : ℂ) / (2 : ℂ) ^ m *
        (x⁻¹) ^ (m + 1 + r) =
      ((-x⁻¹) ^ (m + 1 + r) * (Nat.choose m r : ℂ)) / (2 : ℂ) ^ m := by
        rw [neg_eq_neg_one_mul, mul_pow]
        ring
    _ = (-x⁻¹) ^ (m + 1) *
        ((-x⁻¹) ^ r * (Nat.choose m r : ℂ)) / (2 : ℂ) ^ m := by
          rw [pow_add]
          ring

private theorem finite_binomial_minus (m : ℕ) (x : ℂ) :
    (1 - x) ^ m =
      ∑ r ∈ Finset.range (m + 1),
        (-x) ^ r * (Nat.choose m r : ℂ) := by
  simpa [sub_eq_add_neg, add_comm, mul_comm] using
    (add_pow (-x) (1 : ℂ) m)

/-- The finite coefficient packet is exactly the localized source formula. -/
theorem restoringK_source_formula (m : ℕ) (s : Circle) :
    restoringK m s =
      (-(s : ℂ)) ^ (-((m + 1 : ℕ) : ℤ)) *
        ((1 - (s : ℂ) ^ (-1 : ℤ)) / 2) ^ m := by
  unfold restoringK
  simp_rw [restoringCoeff_mode_eq]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  have hpow : (s : ℂ) ^ (-1 : ℤ) = (s : ℂ)⁻¹ := by simp
  rw [hpow]
  rw [← finite_binomial_minus m ((s : ℂ)⁻¹)]
  rw [div_pow]
  ring

#assert_trust kernel restoringK_source_formula
#assert_trust kernel restoringK_at_neg_one
#assert_trust kernel restoredD_at_neg_one
#assert_trust kernel toeplitz_add_restoration_invisible
#assert_trust kernel toeplitz_add_restoredNegativePacket_invisible
#assert_trust kernel toeplitz_add_restoredNegativePacket_source_stage
#print axioms restoringK_source_formula
#print axioms toeplitz_add_restoredNegativePacket_invisible
#print axioms toeplitz_add_restoredNegativePacket_source_stage

end NLA.Proofs.SP14
