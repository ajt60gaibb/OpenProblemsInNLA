import ProofProject.ProjectionHankel

/-!
# Finite Toeplitz contraction from a finitely supported Hankel sequence

Reversing rows turns the Hankel matrix into a lower triangular Toeplitz matrix
when all moments at index at least the dimension vanish. The reversal is an
isometry for the actual Euclidean energy, including in dimension zero.
-/

noncomputable section

namespace ProofProject

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Lower triangular Toeplitz synthesis, with no conjugation of coefficients. -/
def finiteToeplitzApply (c : ℕ → ℂ) {m : ℕ} (a : Fin m → ℂ) (i : Fin m) : ℂ :=
  ∑ j : Fin m, if j.val ≤ i.val then c (i.val - j.val) * a j else 0

/-- A bound in Euclidean squared norms, rather than a default matrix norm. -/
def HasFiniteToeplitzBound (c : ℕ → ℂ) (m : ℕ) (ρ : ℝ) : Prop :=
  ∀ a : Fin m → ℂ, (∑ i, ‖finiteToeplitzApply c a i‖ ^ 2) ≤
    ρ ^ 2 * ∑ j, ‖a j‖ ^ 2

/-- Only the first `m` entries are used by the associated Toeplitz matrix. -/
def reversedMomentCoefficients (γ : ℕ → ℂ) (m : ℕ) (k : ℕ) : ℂ :=
  γ (m - 1 - k)

lemma finiteToeplitzApply_congr_prefix {m : ℕ} {c d : ℕ → ℂ}
    (h : ∀ k, k < m → c k = d k) (a : Fin m → ℂ) (i : Fin m) :
    finiteToeplitzApply c a i = finiteToeplitzApply d a i := by
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hji
  · rw [h _ (by omega)]
  · rfl

lemma HasFiniteToeplitzBound.congr_prefix {m : ℕ} {c d : ℕ → ℂ} {ρ : ℝ}
    (hc : HasFiniteToeplitzBound c m ρ) (h : ∀ k, k < m → c k = d k) :
    HasFiniteToeplitzBound d m ρ := by
  intro a
  simpa only [← finiteToeplitzApply_congr_prefix h] using hc a

/-- The exact row reversal. No transpose or conjugation is involved. -/
lemma finiteToeplitzApply_reversedMoment {m : ℕ} (γ : ℕ → ℂ)
    (hγ : ∀ k, m ≤ k → γ k = 0) (a : Fin m → ℂ) (i : Fin m) :
    finiteToeplitzApply (reversedMomentCoefficients γ m) a i =
      ∑ j : Fin m, γ ((Fin.rev i).val + j.val) * a j := by
  apply Finset.sum_congr rfl
  intro j _
  simp only [reversedMomentCoefficients, Fin.val_rev]
  split_ifs with hji
  · congr 2
    omega
  · rw [hγ _ (by omega), zero_mul]

/-- Permuting the rows preserves the full Euclidean energy. -/
lemma finiteToeplitz_reversedMoment_energy {m : ℕ} (γ : ℕ → ℂ)
    (hγ : ∀ k, m ≤ k → γ k = 0) (a : Fin m → ℂ) :
    (∑ i : Fin m, ‖finiteToeplitzApply (reversedMomentCoefficients γ m) a i‖ ^ 2) =
      ∑ i : Fin m, ‖∑ j : Fin m, γ (i.val + j.val) * a j‖ ^ 2 := by
  simp_rw [finiteToeplitzApply_reversedMoment γ hγ]
  exact Equiv.sum_comp Fin.revPerm (fun i : Fin m =>
    ‖∑ j : Fin m, γ (i.val + j.val) * a j‖ ^ 2)

lemma hasFiniteToeplitzBound_of_hankel {m : ℕ} {γ : ℕ → ℂ} {ρ : ℝ}
    (hγ : ∀ k, m ≤ k → γ k = 0)
    (hH : ∀ a : Fin m → ℂ, (∑ i : Fin m, ‖∑ j : Fin m, γ (i.val + j.val) * a j‖ ^ 2) ≤
      ρ ^ 2 * ∑ j, ‖a j‖ ^ 2) :
    HasFiniteToeplitzBound (reversedMomentCoefficients γ m) m ρ := by
  intro a
  rw [finiteToeplitz_reversedMoment_energy γ hγ]
  exact hH a

lemma finiteToeplitzApply_scale (s : ℂ) (c : ℕ → ℂ) {m : ℕ} (a : Fin m → ℂ)
    (i : Fin m) :
    finiteToeplitzApply (fun k => s * c k) a i = s * finiteToeplitzApply c a i := by
  simp only [finiteToeplitzApply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [mul_assoc, mul_zero]

/-- Positive scalar normalization gives a genuine finite contraction. -/
lemma HasFiniteToeplitzBound.normalize {m : ℕ} {c : ℕ → ℂ} {ρ : ℝ}
    (h : HasFiniteToeplitzBound c m ρ) (hρ : 0 < ρ) :
    HasFiniteToeplitzBound (fun k => (ρ : ℂ)⁻¹ * c k) m 1 := by
  intro a
  simp only [finiteToeplitzApply_scale, norm_mul, mul_pow, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hρ, one_pow, one_mul, ← Finset.mul_sum]
  have he := mul_le_mul_of_nonneg_left (h a) (sq_nonneg ρ⁻¹)
  simpa only [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hρ.ne', one_pow, one_mul] using he

/-- The finite Toeplitz bound for the actual rational phase, assuming its tail
moments vanish. The analytic vanishing theorem can be supplied separately. -/
theorem polynomialCirclePhase_toeplitz_bound {h : Polynomial ℂ} {K : ℝ}
    (hh : ∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0)
    (hproj : HasPolynomialCircleProjectionBound h K) (hK : 1 ≤ K)
    {m : ℕ} (hvan : ∀ k, m ≤ k → phaseNegativeMoment (polynomialCirclePhase h) k = 0) :
    HasFiniteToeplitzBound
      (reversedMomentCoefficients (phaseNegativeMoment (polynomialCirclePhase h)) m) m
      (Real.sqrt (1 - K⁻¹ ^ 2)) := by
  apply hasFiniteToeplitzBound_of_hankel hvan
  intro a
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hi0 : 0 ≤ K⁻¹ := inv_nonneg.mpr hKpos.le
  have hi1 : K⁻¹ ≤ 1 := (inv_le_one₀ hKpos).2 hK
  rw [Real.sq_sqrt (by nlinarith : 0 ≤ 1 - K⁻¹ ^ 2)]
  exact polynomialCirclePhase_hankel_energy_le hh hproj hK a

end ProofProject
