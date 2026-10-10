import NLA.Proofs.SP14.OddFrequencyToeplitzCharpoly
import NLA.Proofs.SP14.NegativeRestorationInvisibility
import NLA.Proofs.SP14.BaseExteriorPattern

/-!
Every finite corrected SP-14 symbol built from the exterior base and the
source's positive and restored negative packets has only odd Fourier modes.
This supplies the exact support premise of the generic odd Toeplitz
characteristic-polynomial theorem, but no jet vanishing or selected vector.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral
open scoped Polynomial

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

theorem oddSupport_baseExterior : OddFourierSupport baseExteriorSymbol :=
  baseExteriorSymbol_fourier_pattern.1

theorem oddSupport_positivePacket (τ : ℂ) (m : ℕ) :
    OddFourierSupport (positivePacket τ m) := by
  intro p
  rw [positivePacket_fourier]
  have h1 : ((2 * m + 1 : ℕ) : ℤ) ≠ 2 * p := by omega
  have h2 : ((2 * m + 3 : ℕ) : ℤ) ≠ 2 * p := by omega
  have h1' : 2 * (m : ℤ) + 1 ≠ 2 * p := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h1
  have h2' : 2 * (m : ℤ) + 3 ≠ 2 * p := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h2
  simp [h1', h2']

private theorem continuous_circle_mode (e : ℤ) :
    Continuous (fun z : Circle => (z : ℂ) ^ e) := by
  have hp : Continuous (fun z : Circle => (z : Circle) ^ e) := continuous_zpow _
  apply (continuous_subtype_val.comp hp).congr
  intro z
  exact Circle.coe_zpow z e

private theorem continuous_mode_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (c : α → ℂ) (e : α → ℤ) :
    Continuous (fun z : Circle => ∑ r ∈ s, c r * (z : ℂ) ^ (e r)) := by
  induction s using Finset.induction_on with
  | empty => simpa using (continuous_const : Continuous (fun _ : Circle => (0 : ℂ)))
  | @insert x s hx ih =>
      simp only [Finset.sum_insert hx]
      exact (continuous_const.mul (continuous_circle_mode (e x))).add ih

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

private theorem FourierCoefficient_const_mul (c : ℂ) (b : Circle → ℂ) (k : ℤ) :
    FourierCoefficient (fun z => c * b z) k = c * FourierCoefficient b k := by
  unfold FourierCoefficient
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem FourierCoefficient_mode_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (c : α → ℂ) (e : α → ℤ) (k : ℤ) :
    FourierCoefficient
        (fun z : Circle => ∑ r ∈ s, c r * (z : ℂ) ^ (e r)) k =
      ∑ r ∈ s, c r * (if e r = k then 1 else 0) := by
  induction s using Finset.induction_on with
  | empty => simp [FourierCoefficient]
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
    _ = (z : ℂ) ^ (1 + 2 * e) := by rfl

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

theorem continuous_restoredNegativePacket (m q : ℕ) (v : Fin q → ℂ) :
    Continuous (restoredNegativePacket m q v) := by
  have hshape : restoredNegativePacket m q v =
      fun z : Circle => (z : ℂ) * negativeL m q v (z ^ 2) -
        negativeL m q v (-1) * ((z : ℂ) * restoringK m (z ^ 2)) := by
    funext z
    simp [restoredNegativePacket, restoredD]
    ring
  rw [hshape]
  exact (continuous_negativeL_circle_packet m q v).sub
    (continuous_const.mul (continuous_restoring_circle_packet m))

private theorem FourierCoefficient_restoring_even_zero (m : ℕ) (p : ℤ) :
    FourierCoefficient (fun z : Circle => (z : ℂ) * restoringK m (z ^ 2))
      (2 * p) = 0 := by
  rw [restoringK_circle_modes, FourierCoefficient_mode_sum]
  apply Finset.sum_eq_zero
  intro r hr
  have hmode : 1 - 2 * ((m + 1 + r : ℕ) : ℤ) ≠ 2 * p := by omega
  have hmode' : 1 - 2 * ((m : ℤ) + 1 + (r : ℤ)) ≠ 2 * p := by
    simpa only [Nat.cast_add, Nat.cast_one] using hmode
  simp [hmode']

private theorem FourierCoefficient_negativeL_even_zero (m q : ℕ)
    (v : Fin q → ℂ) (p : ℤ) :
    FourierCoefficient (fun z : Circle => (z : ℂ) * negativeL m q v (z ^ 2))
      (2 * p) = 0 := by
  rw [negativeL_circle_modes, FourierCoefficient_mode_sum]
  apply Finset.sum_eq_zero
  intro d hd
  have hmode : 1 + 2 * ((d.val : ℤ) - (m : ℤ)) ≠ 2 * p := by omega
  simp [hmode]

theorem oddSupport_restoredNegativePacket (m q : ℕ) (v : Fin q → ℂ) :
    OddFourierSupport (restoredNegativePacket m q v) := by
  intro p
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
    (continuous_const.mul (continuous_restoring_circle_packet m))]
  rw [FourierCoefficient_const_mul]
  rw [FourierCoefficient_negativeL_even_zero, FourierCoefficient_restoring_even_zero]
  simp

noncomputable def finiteCorrectedSymbol (u vCount : ℕ)
    (pM : Fin u → ℕ) (pτ : Fin u → ℂ)
    (nM nQ : Fin vCount → ℕ)
    (nv : ∀ j : Fin vCount, Fin (nQ j) → ℂ)
    (z : Circle) : ℂ :=
  baseExteriorSymbol z +
    (∑ i : Fin u, positivePacket (pτ i) (pM i) z) +
    (∑ j : Fin vCount, restoredNegativePacket (nM j) (nQ j) (nv j) z)

theorem restoredNegativePacket_q_zero (m : ℕ) (v : Fin 0 → ℂ) :
    restoredNegativePacket m 0 v = fun _ => 0 := by
  funext z
  simp [restoredNegativePacket, restoredD, negativeL]

theorem finiteCorrectedSymbol_empty
    (pM : Fin 0 → ℕ) (pτ : Fin 0 → ℂ)
    (nM nQ : Fin 0 → ℕ)
    (nv : ∀ j : Fin 0, Fin (nQ j) → ℂ) :
    finiteCorrectedSymbol 0 0 pM pτ nM nQ nv = baseExteriorSymbol := by
  funext z
  simp [finiteCorrectedSymbol]

private theorem continuous_positivePacket (τ : ℂ) (m : ℕ) :
    Continuous (positivePacket τ m) := by
  unfold positivePacket
  fun_prop

private theorem oddSupport_add_of_continuous (a b : Circle → ℂ)
    (ha : Continuous a) (hb : Continuous b)
    (hOddA : OddFourierSupport a) (hOddB : OddFourierSupport b) :
    OddFourierSupport (fun z => a z + b z) := by
  intro p
  rw [FourierCoefficient_add_of_continuous a b ha hb]
  rw [hOddA p, hOddB p]
  simp

private theorem continuous_odd_finset_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → Circle → ℂ) :
    (∀ i ∈ s, Continuous (f i)) →
    (∀ i ∈ s, OddFourierSupport (f i)) →
    Continuous (fun z : Circle => ∑ i ∈ s, f i z) ∧
      OddFourierSupport (fun z : Circle => ∑ i ∈ s, f i z) := by
  induction s using Finset.induction_on with
  | empty =>
      intro hc ho
      constructor
      · simpa using (continuous_const : Continuous (fun _ : Circle => (0 : ℂ)))
      · intro p
        simp [FourierCoefficient]
  | @insert x s hx ih =>
      intro hc ho
      have hcx : Continuous (f x) := hc x (by simp)
      have hox : OddFourierSupport (f x) := ho x (by simp)
      have hcs : ∀ i ∈ s, Continuous (f i) := by
        intro i hi
        exact hc i (Finset.mem_insert_of_mem hi)
      have hos : ∀ i ∈ s, OddFourierSupport (f i) := by
        intro i hi
        exact ho i (Finset.mem_insert_of_mem hi)
      obtain ⟨hcont, hodd⟩ := ih hcs hos
      simp only [Finset.sum_insert hx]
      exact ⟨hcx.add hcont,
        oddSupport_add_of_continuous _ _ hcx hcont hox hodd⟩

private theorem finiteCorrectedSymbol_cont_odd (u vCount : ℕ)
    (pM : Fin u → ℕ) (pτ : Fin u → ℂ)
    (nM nQ : Fin vCount → ℕ)
    (nv : ∀ j : Fin vCount, Fin (nQ j) → ℂ) :
    Continuous (finiteCorrectedSymbol u vCount pM pτ nM nQ nv) ∧
      OddFourierSupport (finiteCorrectedSymbol u vCount pM pτ nM nQ nv) := by
  classical
  have hpos := continuous_odd_finset_sum Finset.univ
    (fun i : Fin u => positivePacket (pτ i) (pM i))
    (by intro i hi; exact continuous_positivePacket _ _)
    (by intro i hi; exact oddSupport_positivePacket _ _)
  have hneg := continuous_odd_finset_sum Finset.univ
    (fun j : Fin vCount => restoredNegativePacket (nM j) (nQ j) (nv j))
    (by intro j hj; exact continuous_restoredNegativePacket _ _ _)
    (by intro j hj; exact oddSupport_restoredNegativePacket _ _ _)
  unfold finiteCorrectedSymbol
  constructor
  · exact (continuous_baseExteriorSymbol.add hpos.1).add hneg.1
  · exact oddSupport_add_of_continuous _ _
      (continuous_baseExteriorSymbol.add hpos.1) hneg.1
      (oddSupport_add_of_continuous _ _
        continuous_baseExteriorSymbol hpos.1 oddSupport_baseExterior hpos.2)
      hneg.2

theorem continuous_finiteCorrectedSymbol (u vCount : ℕ)
    (pM : Fin u → ℕ) (pτ : Fin u → ℂ)
    (nM nQ : Fin vCount → ℕ)
    (nv : ∀ j : Fin vCount, Fin (nQ j) → ℂ) :
    Continuous (finiteCorrectedSymbol u vCount pM pτ nM nQ nv) :=
  (finiteCorrectedSymbol_cont_odd u vCount pM pτ nM nQ nv).1

theorem oddSupport_finiteCorrectedSymbol (u vCount : ℕ)
    (pM : Fin u → ℕ) (pτ : Fin u → ℂ)
    (nM nQ : Fin vCount → ℕ)
    (nv : ∀ j : Fin vCount, Fin (nQ j) → ℂ) :
    OddFourierSupport (finiteCorrectedSymbol u vCount pM pτ nM nQ nv) :=
  (finiteCorrectedSymbol_cont_odd u vCount pM pτ nM nQ nv).2

theorem finiteCorrectedSymbol_odd_charpoly_in_jet (u vCount m : ℕ)
    (pM : Fin u → ℕ) (pτ : Fin u → ℂ)
    (nM nQ : Fin vCount → ℕ)
    (nv : ∀ j : Fin vCount, Fin (nQ j) → ℂ) :
    (Toeplitz (finiteCorrectedSymbol u vCount pM pτ nM nQ nv)
      (2 * m + 1)).charpoly =
      Polynomial.X *
        (oddJetPolynomial (finiteCorrectedSymbol u vCount pM pτ nM nQ nv) m).comp
          (Polynomial.X ^ 2 - 1) := by
  exact toeplitz_odd_charpoly_in_jet _ m
    (oddSupport_finiteCorrectedSymbol u vCount pM pτ nM nQ nv)

#assert_trust kernel oddSupport_baseExterior
#assert_trust kernel oddSupport_positivePacket
#assert_trust kernel continuous_restoredNegativePacket
#assert_trust kernel oddSupport_restoredNegativePacket
#assert_trust kernel continuous_finiteCorrectedSymbol
#assert_trust kernel oddSupport_finiteCorrectedSymbol
#assert_trust kernel restoredNegativePacket_q_zero
#assert_trust kernel finiteCorrectedSymbol_empty
#assert_trust kernel finiteCorrectedSymbol_odd_charpoly_in_jet
#print axioms finiteCorrectedSymbol_odd_charpoly_in_jet

end NLA.Proofs.SP14
