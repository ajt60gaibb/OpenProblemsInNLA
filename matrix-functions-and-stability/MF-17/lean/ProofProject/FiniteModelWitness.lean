import ProofProject.RoundedSemigroupBound
import ProofProject.DiagonalWitness
import ProofProject.PeakClock

/-!
# From a finite model to an admissible witness

A unit family with the elementary-pattern bound and a nonzero sign-gain vector
produces a finite-dimensional witness in the exact bound-M semigroup class.
The scalar smallness inequality is explicit; it holds eventually for the
source choices N = r n and κ = n³.
-/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The conditional finite-model construction, including its actual witness time.
The input norm and the rounded witness norm live on distinct Hilbert spaces. -/
theorem finiteModel_finiteWitness {N : ℕ} (f : Fin N → H) {M : ℝ}
    (hM : 1 < M) (hN : 0 < N) (hf : ∀ j, ‖f j‖ = 1)
    (hpattern : ∀ (c : Fin N → ℂ) (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖)
    (p : ℕ → Bool) {κ : ℕ} (hκ : 1 ≤ κ)
    (hsmall : (N : ℝ) * Real.exp (-(metricGamma M N / (12 * M ^ 2)) * κ) ≤
      metricGamma M N / (12 * M ^ 2))
    {a : ℝ} (ha : 0 ≤ a) {c : Fin N → ℂ} (hc : c ≠ 0)
    (hgain : a * ‖finiteSynthesis f c‖ ^ 2 ≤
      ‖finiteSynthesis f ((fun i => if p i.val then (-1 : ℂ) else 1) * c)‖ ^ 2) :
    HasFiniteWitness.{u} M (peakTime M N (separatedInteger κ p (N - 1)))
      (Real.exp (-Real.pi) * Real.sqrt (a / 2) - 1) := by
  cases N with
  | zero => omega
  | succ n =>
    let y : Fin (n + 1) → ℕ := fun i => separatedInteger κ p i.val
    let b := roundedBasis f (metricEta_pos hM (Nat.succ_pos n))
    have hy : ∀ i, 0 < (y i : ℝ) := by
      intro i
      have := two_le_separatedInteger hκ p i.val
      dsimp [y]
      exact_mod_cast (by omega : 0 < separatedInteger κ p i.val)
    have hgap : ∀ j : Fin n,
        (κ : ℝ) * (1 + (y j.castSucc : ℝ) ^ 2) ≤ (y j.succ : ℝ) := by
      intro j
      dsimp [y]
      exact_mod_cast (separatedInteger_succ_bounds κ p j.val).1
    have hκr : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
    have hsmall' : (n + 1 : ℝ) *
        Real.exp (-(metricGamma M (n + 1) / (12 * M ^ 2)) * κ) ≤
          metricGamma M (n + 1) / (12 * M ^ 2) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hsmall
    have hfwd : ∀ s : ℝ, 0 ≤ s →
        ‖basisDiagonal b (fun i => Complex.exp ((s : ℂ) * scalarLambda (y i)))‖ ≤ M :=
      norm_rounded_exponential_diagonal_le n f hM hf hpattern (fun i => (y i : ℝ))
        hy κ hκr hgap hsmall'
    have hY : ∀ i, (y i : ℝ) ≤ (separatedInteger κ p n : ℝ) := by
      intro i
      exact_mod_cast (separatedInteger_strictMono hκ p).monotone (by omega : i.val ≤ n)
    have hw := diagonalPeak_finiteWitness_unit_error b (by linarith : 0 < M)
      (Nat.succ_pos n) y hY (norm_roundedCoordinate_le f hM (Nat.succ_pos n) hf hpattern) hfwd
    have hsign : (fun i : Fin (n + 1) => (-1 : ℂ) ^ y i) =
        (fun i => if p i.val then (-1 : ℂ) else 1) := by
      funext i
      exact separatedInteger_neg_one_pow κ p i.val
    have hnorm : Real.sqrt (a / 2) ≤ ‖basisDiagonal b (fun i => (-1 : ℂ) ^ y i)‖ := by
      rw [hsign]
      exact roundedDiagonal_norm_lower f hM (Nat.succ_pos n) hf hpattern _ ha hc hgain
    change HasFiniteWitness M (peakTime M (n + 1) (separatedInteger κ p n)) _
    exact hw.mono_lower (sub_le_sub_right
      (mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le) 1)

end ProofProject
