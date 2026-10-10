import NLA.Proofs.SP14.FiniteLaurentBackground

/-!
Exact finite endpoint division for the source's negative Laurent correction.
The quotient has the same coefficient range and zero first coefficient.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

private def sourceCoeff (u : ℕ) (p : Fin u → ℝ) (j : ℕ) : ℝ :=
  if hj : j < u then p ⟨j, hj⟩ else 0

private def quotientCoeff (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => p j - quotientCoeff p j

private theorem quotientCoeff_zero (p : ℕ → ℝ) : quotientCoeff p 0 = 0 := rfl

private theorem quotientCoeff_succ (p : ℕ → ℝ) (j : ℕ) :
    quotientCoeff p (j + 1) = p j - quotientCoeff p j := rfl

private noncomputable def laurentRange (p : ℕ → ℝ) (u : ℕ) (s : Circle) : ℂ :=
  ∑ j ∈ Finset.range u, (p j : ℂ) * (s : ℂ) ^ (-((j + 1 : ℕ) : ℤ))

private theorem laurentRange_succ (p : ℕ → ℝ) (u : ℕ) (s : Circle) :
    laurentRange p (u + 1) s =
      laurentRange p u s + (p u : ℂ) * (s : ℂ) ^ (-((u + 1 : ℕ) : ℤ)) := by
  simp [laurentRange, Finset.sum_range_succ]

private theorem laurentRange_identity (p : ℕ → ℝ) (u : ℕ) (s : Circle) :
    laurentRange p u s =
      (1 + (s : ℂ)) * laurentRange (quotientCoeff p) u s +
        (quotientCoeff p u : ℂ) * (s : ℂ) ^ (-(u : ℤ)) := by
  induction u with
  | zero => simp [laurentRange, quotientCoeff]
  | succ u ih =>
      rw [laurentRange_succ, laurentRange_succ, ih]
      have hs : (s : ℂ) ≠ 0 := Circle.coe_ne_zero s
      have hpow : (s : ℂ) * (s : ℂ) ^ (-((u + 1 : ℕ) : ℤ)) =
          (s : ℂ) ^ (-(u : ℤ)) := by
        have he : (1 : ℤ) + -((u + 1 : ℕ) : ℤ) = -(u : ℤ) := by omega
        calc
          (s : ℂ) * (s : ℂ) ^ (-((u + 1 : ℕ) : ℤ)) =
              (s : ℂ) ^ (1 : ℤ) * (s : ℂ) ^ (-((u + 1 : ℕ) : ℤ)) := by simp
          _ = (s : ℂ) ^ (-(u : ℤ)) := by rw [← zpow_add₀ hs, he]
      rw [quotientCoeff_succ]
      push_cast
      simp only [Nat.cast_add, Nat.cast_one] at hpow ⊢
      rw [← hpow]
      ring

private theorem negativeLaurent_eq_laurentRange (u : ℕ) (p : Fin u → ℝ)
    (s : Circle) :
    negativeLaurent u p s = laurentRange (sourceCoeff u p) u s := by
  unfold negativeLaurent laurentRange
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hju : j < u := Finset.mem_range.mp hj
  simp [sourceCoeff, hju]

theorem negativeLaurent_endpoint_factor (u : ℕ) (p : Fin u → ℝ)
    (hcontact : negativeLaurent u p (-1 : Circle) = 0) :
    ∃ q : Fin u → ℝ,
      (∀ j : Fin u, j.val = 0 → q j = 0) ∧
      (∀ s : Circle,
        negativeLaurent u p s =
          (1 + (s : ℂ)) * negativeLaurent u q s) := by
  let pn := sourceCoeff u p
  let qn := quotientCoeff pn
  let q : Fin u → ℝ := fun j => qn j.val
  refine ⟨q, ?_, ?_⟩
  · intro j hj
    simp [q, hj, qn, quotientCoeff]
  · intro s
    have hterminal : qn u = 0 := by
      have hident := laurentRange_identity pn u (-1 : Circle)
      have hP : laurentRange pn u (-1 : Circle) = 0 := by
        rw [← negativeLaurent_eq_laurentRange]
        exact hcontact
      rw [hP] at hident
      have hcoef : (qn u : ℂ) * ((-1 : Circle) : ℂ) ^ (-(u : ℤ)) = 0 := by
        simpa [qn, pn] using hident.symm
      have hpow : (((-1 : Circle) : ℂ) ^ (-(u : ℤ))) ≠ 0 :=
        zpow_ne_zero _ (Circle.coe_ne_zero _)
      have hqc : (qn u : ℂ) = 0 := (mul_eq_zero.mp hcoef).resolve_right hpow
      exact_mod_cast hqc
    rw [negativeLaurent_eq_laurentRange]
    have hq : negativeLaurent u q s = laurentRange qn u s := by
      rw [negativeLaurent_eq_laurentRange]
      apply Finset.sum_congr rfl
      intro j hj
      have hju : j < u := Finset.mem_range.mp hj
      simp [sourceCoeff, q, qn, hju]
    rw [hq]
    simpa [pn, qn, hterminal] using laurentRange_identity pn u s

#assert_trust kernel negativeLaurent_endpoint_factor

end NLA.Proofs.SP14
