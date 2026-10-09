import ProofProject.FiniteToeplitz

/-!
# The boundary case for finite Toeplitz contractions

Testing on the first coordinate controls the squared norm of the whole first
column. If its first entry has norm one, all remaining entries in the finite
prefix vanish. The polynomial consequence is a congruence modulo a power of
`X`; no restriction is imposed on coefficients beyond the tested prefix.
-/

noncomputable section

namespace ProofProject

lemma finiteToeplitzApply_firstCoordinate (c : ℕ → ℂ) {m : ℕ} (i : Fin (m + 1)) :
    finiteToeplitzApply c (fun j : Fin (m + 1) => if j = 0 then 1 else 0) i =
      c i.val := by
  classical
  unfold finiteToeplitzApply
  rw [Finset.sum_eq_single (0 : Fin (m + 1))]
  · simp
  · intro j hj hj0
    simp [hj0]
  · simp

namespace HasFiniteToeplitzBound

theorem firstColumn_energy_le {c : ℕ → ℂ} {m : ℕ}
    (h : HasFiniteToeplitzBound c (m + 1) 1) :
    (∑ i : Fin (m + 1), ‖c i.val‖ ^ 2) ≤ 1 := by
  have ht := h (fun j : Fin (m + 1) => if j = 0 then 1 else 0)
  simpa [finiteToeplitzApply_firstCoordinate, apply_ite] using ht

theorem coeff_zero_norm_le_one {c : ℕ → ℂ} {m : ℕ}
    (h : HasFiniteToeplitzBound c (m + 1) 1) : ‖c 0‖ ≤ 1 := by
  have he := h.firstColumn_energy_le
  have hs : ‖c 0‖ ^ 2 ≤ ∑ i : Fin (m + 1), ‖c i.val‖ ^ 2 := by
    simpa only [Fin.val_zero] using
      Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => sq_nonneg ‖c i.val‖)
        (Finset.mem_univ (0 : Fin (m + 1)))
  nlinarith [norm_nonneg (c 0)]

/-- Only the tested prefix must be constant; higher coefficients are free. -/
theorem coeff_eq_zero_of_norm_zero_eq_one {c : ℕ → ℂ} {m : ℕ}
    (h : HasFiniteToeplitzBound c (m + 1) 1) (hzero : ‖c 0‖ = 1)
    {j : ℕ} (hj0 : 0 < j) (hjm : j < m + 1) : c j = 0 := by
  have he := h.firstColumn_energy_le
  rw [Fin.sum_univ_succ] at he
  simp only [Fin.val_zero, Fin.val_succ, hzero, one_pow] at he
  have hsum : (∑ i : Fin m, ‖c (i.val + 1)‖ ^ 2) = 0 := by
    have hn : 0 ≤ ∑ i : Fin m, ‖c (i.val + 1)‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  let i : Fin m := ⟨j - 1, by omega⟩
  have hi : ‖c (i.val + 1)‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsum i
      (Finset.mem_univ i)
  have hij : i.val + 1 = j := by dsimp [i]; omega
  rw [hij] at hi
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)

/-- A unit constant coefficient of a finite Toeplitz contraction forces
agreement with that constant through the complete tested prefix. -/
theorem X_pow_dvd_sub_C_of_norm_zero_eq_one {P : Polynomial ℂ} {m : ℕ}
    (h : HasFiniteToeplitzBound P.coeff (m + 1) 1) (hzero : ‖P.coeff 0‖ = 1) :
    Polynomial.X ^ (m + 1) ∣ P - Polynomial.C (P.coeff 0) := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro j hj
  by_cases hj0 : j = 0
  · simp [hj0]
  · rw [Polynomial.coeff_sub, Polynomial.coeff_C]
    rw [if_neg hj0, sub_zero]
    exact h.coeff_eq_zero_of_norm_zero_eq_one hzero (Nat.pos_of_ne_zero hj0) hj

end HasFiniteToeplitzBound

end ProofProject
