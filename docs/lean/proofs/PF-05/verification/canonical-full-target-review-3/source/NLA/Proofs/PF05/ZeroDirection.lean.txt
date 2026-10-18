import NLA.Proofs.PF05.ZeroCanonical

/-! The actual uniformly feasible canonical direction, and exact scalar
rigidity of its parameters using the actual rank-three trace separation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
open NLA.Statements.PF05
noncomputable section

/-- The two actual alternative PSD endpoints give one interval for the
entire finite family. No rank-one or flat boundary case is excluded. -/
theorem zeroDirection_feasible {p q : ℕ} (α β γ : ℝ) (hγ : γ ≠ 0)
    (A : Fin p → Sym2) (B : Fin q → Sym2)
    (hA : ∀ i, PositiveSemidefinite (A i))
    (hB : ∀ j, PositiveSemidefinite (B j))
    (hAt : ∀ i, PositiveSemidefinite (zeroCanonicalPrimal α β γ (A i)))
    (hBt : ∀ j, PositiveSemidefinite (zeroCanonicalDual α β γ (B j))) :
    FeasibleDirection A (fun i => zeroPrimalDirection α β γ (A i))
      B (fun j => zeroDualDirection α β γ (B j)) := by
  have hs : 0 < (γ ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_ne_zero hγ)
  refine ⟨(fun i => zeroPrimalDirection_symmetric α β γ (A i)),
    (fun j => zeroDualDirection_symmetric α β γ (B j)),
    (fun i j => zeroDirection_trace α β γ (A i) (B j) (hA i).1 (hB j).1),
    min 1 (γ ^ 2)⁻¹, lt_min (by norm_num) hs, ?_⟩
  intro t ht hth
  have ht1 : t ≤ 1 := (lt_of_lt_of_le hth (min_le_left _ _)).le
  have hts : t ≤ (γ ^ 2)⁻¹ := (lt_of_lt_of_le hth (min_le_right _ _)).le
  constructor
  · intro i
    apply psd_line_of_endpoint (A i) _ _ hs (hA i) _ t ht hts
    rw [zeroPrimalDirection_endpoint α β γ hγ (A i) (hA i).1]
    exact primalCongruence_psd _ _ (hAt i)
  · intro j
    apply psd_line_of_endpoint (B j) _ 1 (by norm_num) (hB j) _ t ht ht1
    simpa only [one_smul, zeroDualDirection_endpoint α β γ hγ (B j) (hB j).1] using
      primalCongruence_psd (!![γ, 0; 0, 1]) _ (hBt j)

/-- If the actual canonical primal direction is a common scalar on an
actual rank-three factor family, then its three parameters vanish. -/
theorem zeroPrimalDirection_scalar_parameters {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → Sym2) (B : Fin q → Sym2)
    (hfact : Factorization M A B) (hrank : M.rank = 3)
    (α β γ d : ℝ) (hd : ∀ i, zeroPrimalDirection α β γ (A i) = d • A i) :
    γ ^ 2 = 1 ∧ α = 0 ∧ β = 0 := by
  have hd0 : d = 0 := by
    by_contra hdne
    have hdiag (i : Fin p) : A i 1 1 = 0 := by
      have hi := congrArg (fun C : Sym2 => C 1 1) (hd i)
      have hmul : d * A i 1 1 = 0 := by
        simpa [zeroPrimalDirection, smul_eq_mul] using hi.symm
      exact (mul_eq_zero.mp hmul).resolve_left hdne
    have hQsym : Symmetric (!![0, 0; 0, 1] : Sym2) := by
      intro i j
      fin_cases i <;> fin_cases j <;> rfl
    have hQzero := trace_pairing_left_nondegenerate_of_rank_three M A B hfact hrank
      (!![0, 0; 0, 1]) hQsym (by
        intro i
        simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hdiag i])
    have h := congrArg (fun C : Sym2 => C 1 1) hQzero
    norm_num at h
  let C : Sym2 := !![-(γ ^ 2 - 1), α / 2; α / 2, β]
  have hCs : Symmetric C := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have htrace (i : Fin p) : Matrix.trace (A i * C) = 0 := by
    have hi := congrArg (fun X : Sym2 => X 0 0) (hd i)
    have hz : -(γ ^ 2 - 1) * A i 0 0 + α * A i 0 1 + β * A i 1 1 = 0 := by
      simpa [zeroPrimalDirection, hd0] using hi
    calc
      Matrix.trace (A i * C) =
          -(γ ^ 2 - 1) * A i 0 0 + α * A i 0 1 + β * A i 1 1 := by
        simp [C, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, (hfact.1 i).1 1 0]
        ring
      _ = 0 := hz
  have hC0 := trace_pairing_left_nondegenerate_of_rank_three M A B hfact hrank C hCs htrace
  have hc00 := congrArg (fun X : Sym2 => X 0 0) hC0
  have hc01 := congrArg (fun X : Sym2 => X 0 1) hC0
  have hc11 := congrArg (fun X : Sym2 => X 1 1) hC0
  simp only [C, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one,
    Matrix.zero_apply] at hc00 hc01 hc11
  exact ⟨by linarith, by linarith, hc11⟩

/-- Actual straight rigidity forces the normalized alternative parameters
onto the genuine congruence case; no nonscalar-direction premise is supplied. -/
theorem rigid_zeroCanonical_parameters {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → Sym2) (B : Fin q → Sym2)
    (hfact : Factorization M A B) (hrank : M.rank = 3)
    (α β γ : ℝ) (hγ : γ ≠ 0)
    (hAt : ∀ i, PositiveSemidefinite (zeroCanonicalPrimal α β γ (A i)))
    (hBt : ∀ j, PositiveSemidefinite (zeroCanonicalDual α β γ (B j)))
    (hrigid : InfinitesimallyRigid A B) : γ ^ 2 = 1 ∧ α = 0 ∧ β = 0 := by
  obtain ⟨d, hdA, _⟩ := hrigid _ _
    (zeroDirection_feasible α β γ hγ A B hfact.1 hfact.2.1 hAt hBt)
  exact zeroPrimalDirection_scalar_parameters M A B hfact hrank α β γ d hdA

#assert_trust kernel zeroDirection_feasible
#assert_trust kernel zeroPrimalDirection_scalar_parameters
#assert_trust kernel rigid_zeroCanonical_parameters
#print axioms zeroDirection_feasible
#print axioms rigid_zeroCanonical_parameters
end
end NLA.Proofs.PF05
