import NLA.MI27.PositivePartLipschitz
import NLA.MI27.UnitaryConjugation

/-!
The frozen C10 cutoff is derived from positive spectral lower bounds and
uniform scalar upper bounds. It works simultaneously for every unitary
conjugate. Continuity is a consequence of C07, with no spectral simplicity
assumption.

Analytic resolution: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
-/

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

private lemma real_matrix_algebraMap {n : ℕ} (r : ℝ) :
    algebraMap ℝ (Mat n) r = (r : ℂ) • (1 : Mat n) := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) r (1 : Mat n)

private lemma hermitian_real_smul {n : ℕ} (X : Mat n) (hX : X.IsHermitian) (r : ℝ) :
    ((r : ℂ) • X).IsHermitian :=
  hX.smul (by simp [IsSelfAdjoint])

lemma hockey_stick_continuous_gamma {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Continuous (fun γ : ℝ => E γ A B) := by
  apply (LipschitzWith.of_dist_le' (K := (n : ℝ) * opNorm B) ?_).continuous
  intro x y
  rw [Real.dist_eq, Real.dist_eq]
  have hd : (A - (x : ℂ) • B) - (A - (y : ℂ) • B) =
      ((y - x : ℝ) : ℂ) • B := by
    rw [Complex.ofReal_sub, sub_smul]
    abel
  calc
    |E x A B - E y A B| ≤ (n : ℝ) * opNorm
        ((A - (x : ℂ) • B) - (A - (y : ℂ) • B)) :=
      positive_part_trace_lipschitz hn _ _
        (hA.sub (hermitian_real_smul B hB x))
        (hA.sub (hermitian_real_smul B hB y))
    _ = ((n : ℝ) * opNorm B) * |x - y| := by
      rw [hd]
      simp only [opNorm_eq_l2, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_sub_comm y x]
      ring

private lemma hockey_stick_zero_of_le {n : ℕ} (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (γ : ℝ)
    (hAB : A ≤ (γ : ℂ) • B) : E γ A B = 0 := by
  apply le_antisymm ?_ (tracePos_nonneg _)
  have hh := tracePos_le_trR_of_le (A - (γ : ℂ) • B) (0 : Mat n)
    (hA.sub (hermitian_real_smul B hB γ)) Matrix.PosSemidef.zero
    (sub_nonpos.mpr hAB)
  simpa only [E, trR, Matrix.trace_zero, Complex.zero_re] using hh

private lemma unitary_conjugate_algebraMap {n : ℕ} (U : unitary (Mat n)) (r : ℝ) :
    (U : Mat n) * algebraMap ℝ (Mat n) r * (U : Mat n)ᴴ =
      algebraMap ℝ (Mat n) r := by
  have hu : (U : Mat n) * (U : Mat n)ᴴ = 1 := Unitary.coe_mul_star_self U
  rw [real_matrix_algebraMap, mul_smul_comm, smul_mul_assoc, mul_one, hu]

/-- C10: a single finite cutoff for all unitary conjugates, with no added
conditioning hypothesis and no omitted eigenvalue multiplicities. -/
theorem uniform_hockey_stick_cutoff {n : ℕ} (hn : 1 ≤ n) (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) :
    ∃ R : ℝ, 1 < R ∧
      ∀ U : unitary (Mat n),
        ρ ≤ (R : ℂ) • ((U : Mat n) * σ * (U : Mat n)ᴴ) ∧
        (U : Mat n) * σ * (U : Mat n)ᴴ ≤ (R : ℂ) • ρ ∧
        (∀ γ : ℝ, R ≤ γ →
          E γ ρ ((U : Mat n) * σ * (U : Mat n)ᴴ) = 0 ∧
          E γ ((U : Mat n) * σ * (U : Mat n)ᴴ) ρ = 0) ∧
        ContinuousOn (fun γ : ℝ => E γ ρ ((U : Mat n) * σ * (U : Mat n)ᴴ))
          (Set.Icc 1 R) ∧
        ContinuousOn (fun γ : ℝ => E γ ((U : Mat n) * σ * (U : Mat n)ᴴ) ρ)
          (Set.Icc 1 R) := by
  letI : Nonempty (Fin n) := ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩⟩
  obtain ⟨r, hr, hrρ⟩ :=
    (CFC.exists_pos_algebraMap_le_iff hρ.1.isHermitian.isSelfAdjoint).2
      (fun x hx => hρ.1.isStrictlyPositive.spectrum_pos hx)
  obtain ⟨s, hs, hsσ⟩ :=
    (CFC.exists_pos_algebraMap_le_iff hσ.1.isHermitian.isSelfAdjoint).2
      (fun x hx => hσ.1.isStrictlyPositive.spectrum_pos hx)
  let ε : ℝ := min r s
  have hε : 0 < ε := lt_min hr hs
  have hερ : algebraMap ℝ (Mat n) ε ≤ ρ :=
    (algebraMap_mono (Mat n) (min_le_left r s)).trans hrρ
  have hεσ : algebraMap ℝ (Mat n) ε ≤ σ :=
    (algebraMap_mono (Mat n) (min_le_right r s)).trans hsσ
  let M : ℝ := ‖ρ‖ + ‖σ‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hρM : ρ ≤ algebraMap ℝ (Mat n) M :=
    hρ.1.isHermitian.isSelfAdjoint.le_algebraMap_norm_self.trans
      (algebraMap_mono (Mat n) (by dsimp [M]; linarith [norm_nonneg σ]))
  have hσM : σ ≤ algebraMap ℝ (Mat n) M :=
    hσ.1.isHermitian.isSelfAdjoint.le_algebraMap_norm_self.trans
      (algebraMap_mono (Mat n) (by dsimp [M]; linarith [norm_nonneg ρ]))
  let R : ℝ := 1 + M / ε
  have hR : 1 < R := by dsimp [R]; linarith [div_pos hM hε]
  have hR0 : 0 ≤ R := (lt_trans zero_lt_one hR).le
  have hMR : M ≤ R * ε := by
    dsimp [R]
    rw [add_mul, one_mul, div_mul_cancel₀ M hε.ne']
    linarith
  have hscale (X : Mat n) (hX : algebraMap ℝ (Mat n) ε ≤ X) :
      algebraMap ℝ (Mat n) M ≤ (R : ℂ) • X := by
    apply (algebraMap_mono (Mat n) hMR).trans
    have h := smul_le_smul_of_nonneg_left hX (Complex.zero_le_real.mpr hR0)
    simpa only [real_matrix_algebraMap, smul_smul, Complex.ofReal_mul] using h
  refine ⟨R, hR, ?_⟩
  intro U
  let τ : Mat n := (U : Mat n) * σ * (U : Mat n)ᴴ
  have hτ : τ.IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose (U : Mat n) hσ.1.isHermitian
  have hτ0 : 0 ≤ τ :=
    (hσ.1.posSemidef.mul_mul_conjTranspose_same (U : Mat n)).nonneg
  have hετ : algebraMap ℝ (Mat n) ε ≤ τ := by
    have h := star_right_conjugate_le_conjugate hεσ (U : Mat n)
    simpa only [Matrix.star_eq_conjTranspose, unitary_conjugate_algebraMap, τ] using h
  have hτM : τ ≤ algebraMap ℝ (Mat n) M := by
    have h := star_right_conjugate_le_conjugate hσM (U : Mat n)
    simpa only [Matrix.star_eq_conjTranspose, unitary_conjugate_algebraMap, τ] using h
  have hρτ : ρ ≤ (R : ℂ) • τ := hρM.trans (hscale τ hετ)
  have hτρ : τ ≤ (R : ℂ) • ρ := hτM.trans (hscale ρ hερ)
  refine ⟨hρτ, hτρ, ?_,
    (hockey_stick_continuous_gamma hn ρ τ hρ.1.isHermitian hτ).continuousOn,
    (hockey_stick_continuous_gamma hn τ ρ hτ hρ.1.isHermitian).continuousOn⟩
  intro γ hγ
  have hγC : (R : ℂ) ≤ (γ : ℂ) := by exact_mod_cast hγ
  exact ⟨hockey_stick_zero_of_le ρ τ hρ.1.isHermitian hτ γ
      (hρτ.trans (smul_le_smul_of_nonneg_right hγC hτ0)),
    hockey_stick_zero_of_le τ ρ hτ hρ.1.isHermitian γ
      (hτρ.trans (smul_le_smul_of_nonneg_right hγC hρ.1.posSemidef.nonneg))⟩

#print axioms uniform_hockey_stick_cutoff

end NLA.MI27
