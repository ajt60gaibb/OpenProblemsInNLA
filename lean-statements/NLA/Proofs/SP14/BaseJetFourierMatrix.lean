import NLA.Proofs.SP14.BaseJetCorner

/-!
The actual frozen Fourier coefficients of the exterior base plus one
current restored negative packet, at the frequencies seen by its selected
odd Toeplitz section. Only the restoring K term is invisible there.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

noncomputable def baseJetSymbol (m q : ℕ) (v : Fin q → ℂ) (z : Circle) : ℂ :=
  baseExteriorSymbol z + restoredNegativePacket m q v z

noncomputable def baseJetG (m q : ℕ) (v : Fin q → ℂ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  fun i j => baseG m i j +
    ∑ d : Fin q, if j.val = i.val + (m - d.val) then v d else 0

theorem continuous_baseJetSymbol (m q : ℕ) (v : Fin q → ℂ) :
    Continuous (baseJetSymbol m q v) := by
  exact continuous_baseExteriorSymbol.add (continuous_restoredNegativePacket m q v)

private theorem FourierCoefficient_add_continuous
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

private theorem FourierCoefficient_sub_continuous
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

theorem oddSupport_baseJetSymbol (m q : ℕ) (v : Fin q → ℂ) :
    OddFourierSupport (baseJetSymbol m q v) := by
  intro p
  unfold baseJetSymbol
  rw [FourierCoefficient_add_continuous _ _ continuous_baseExteriorSymbol
    (continuous_restoredNegativePacket m q v)]
  rw [oddSupport_baseExterior p, oddSupport_restoredNegativePacket m q v p]
  simp

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
      rw [FourierCoefficient_add_continuous _ _ hc hs k]
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

private theorem raw_negative_modes (m q : ℕ) (v : Fin q → ℂ) :
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

private theorem restoring_modes (m : ℕ) :
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

private theorem continuous_raw_negative (m q : ℕ) (v : Fin q → ℂ) :
    Continuous (fun z : Circle => (z : ℂ) * negativeL m q v (z ^ 2)) := by
  rw [raw_negative_modes]
  exact continuous_mode_sum _ _ _

private theorem continuous_restoring (m : ℕ) :
    Continuous (fun z : Circle => (z : ℂ) * restoringK m (z ^ 2)) := by
  rw [restoring_modes]
  exact continuous_mode_sum _ _ _

private theorem raw_negative_fourier (m q : ℕ) (v : Fin q → ℂ) (p : ℤ) :
    FourierCoefficient (fun z : Circle => (z : ℂ) * negativeL m q v (z ^ 2))
      (1 - 2 * p) =
      ∑ d : Fin q, if p = (m : ℤ) - (d.val : ℤ) then v d else 0 := by
  rw [raw_negative_modes, FourierCoefficient_mode_sum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases heq : p = (m : ℤ) - (d.val : ℤ)
  · have hmode : 1 + 2 * ((d.val : ℤ) - (m : ℤ)) = 1 - 2 * p := by omega
    simp [heq, hmode]
  · have hmode : 1 + 2 * ((d.val : ℤ) - (m : ℤ)) ≠ 1 - 2 * p := by omega
    simp [heq, hmode]

private theorem restoring_fourier_zero_selected (m : ℕ) (p : ℤ)
    (hp : p ≤ (m : ℤ)) :
    FourierCoefficient (fun z : Circle => (z : ℂ) * restoringK m (z ^ 2))
      (1 - 2 * p) = 0 := by
  rw [restoring_modes, FourierCoefficient_mode_sum]
  apply Finset.sum_eq_zero
  intro r hr
  have hneq : (m : ℤ) + 1 + (r : ℤ) ≠ p := by omega
  simp [hneq]

theorem baseJetSymbol_fourier_selected (m q : ℕ)
    (_hq : 2 * q ≤ m + 1) (v : Fin q → ℂ) (p : ℤ)
    (hp : p ≤ (m : ℤ)) :
    FourierCoefficient (baseJetSymbol m q v) (1 - 2 * p) =
      (if 0 ≤ p then baseCoeff p.toNat else 0) +
        ∑ d : Fin q, if p = (m : ℤ) - (d.val : ℤ) then v d else 0 := by
  let raw : Circle → ℂ := fun z => (z : ℂ) * negativeL m q v (z ^ 2)
  let rest : Circle → ℂ := fun z => (z : ℂ) * restoringK m (z ^ 2)
  have hshape : baseJetSymbol m q v =
      fun z => baseExteriorSymbol z +
        (raw z - negativeL m q v (-1) * rest z) := by
    funext z
    simp [baseJetSymbol, restoredNegativePacket, restoredD, raw, rest]
    ring
  rw [hshape]
  rw [FourierCoefficient_add_continuous baseExteriorSymbol
    (fun z => raw z - negativeL m q v (-1) * rest z) continuous_baseExteriorSymbol
    ((continuous_raw_negative m q v).sub
      (continuous_const.mul (continuous_restoring m)))]
  rw [FourierCoefficient_sub_continuous raw
    (fun z => negativeL m q v (-1) * rest z)
    (continuous_raw_negative m q v)
    (continuous_const.mul (continuous_restoring m))]
  rw [FourierCoefficient_const_mul]
  rw [baseExteriorSymbol_fourier_pattern.2 p,
    raw_negative_fourier m q v p,
    restoring_fourier_zero_selected m p hp]
  simp

private theorem baseJetSymbol_fourier_matrix_entry (m q : ℕ)
    (hq : 2 * q ≤ m + 1) (v : Fin q → ℂ)
    (i j : Fin (m + 1)) :
    FourierCoefficient (baseJetSymbol m q v)
      (1 - 2 * ((j.val : ℤ) - (i.val : ℤ))) = baseJetG m q v i j := by
  let p : ℤ := (j.val : ℤ) - (i.val : ℤ)
  have hp : p ≤ (m : ℤ) := by
    have hj := j.isLt
    dsimp [p]
    omega
  rw [baseJetSymbol_fourier_selected m q hq v p hp]
  have hsum :
      (∑ d : Fin q, if p = (m : ℤ) - (d.val : ℤ) then v d else 0) =
      ∑ d : Fin q, if j.val = i.val + (m - d.val) then v d else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdle : d.val ≤ m := by
      have hdlt := d.isLt
      omega
    have hcast : ((m - d.val : ℕ) : ℤ) = (m : ℤ) - (d.val : ℤ) := by
      omega
    have heq : p = (m : ℤ) - (d.val : ℤ) ↔
        j.val = i.val + (m - d.val) := by
      dsimp [p]
      omega
    simp only [heq]
  rw [hsum]
  by_cases hij : i.val ≤ j.val
  · have hp0 : 0 ≤ p := by dsimp [p]; omega
    have hnat : p.toNat = j.val - i.val := by dsimp [p]; omega
    simp [baseJetG, baseG, hij, hp0, hnat]
  · have hp0 : ¬ 0 ≤ p := by dsimp [p]; omega
    simp [baseJetG, baseG, hij, hp0]

theorem oddB_baseJetSymbol (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) :
    oddB (baseJetSymbol m q v) m =
      (baseJetG m q v).submatrix id Fin.succ := by
  ext i j
  have hfreq :
      2 * (i.val : ℤ) - (2 * (j.val : ℤ) + 1) =
        1 - 2 * (((Fin.succ j).val : ℤ) - (i.val : ℤ)) := by
    simp
    ring
  simp only [oddB, Matrix.submatrix_apply]
  rw [hfreq]
  exact baseJetSymbol_fourier_matrix_entry m q hq v i (Fin.succ j)

theorem oddC_baseJetSymbol (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) :
    oddC (baseJetSymbol m q v) m =
      (baseJetG m q v).submatrix Fin.castSucc id := by
  ext i j
  have hfreq :
      (2 * (i.val : ℤ) + 1) - 2 * (j.val : ℤ) =
        1 - 2 * ((j.val : ℤ) - ((Fin.castSucc i).val : ℤ)) := by
    simp
    ring
  simp only [oddC, Matrix.submatrix_apply]
  rw [hfreq]
  exact baseJetSymbol_fourier_matrix_entry m q hq v (Fin.castSucc i) j

#assert_trust kernel continuous_baseJetSymbol
#assert_trust kernel oddSupport_baseJetSymbol
#assert_trust kernel baseJetSymbol_fourier_selected
#assert_trust kernel oddB_baseJetSymbol
#assert_trust kernel oddC_baseJetSymbol

end NLA.Proofs.SP14
