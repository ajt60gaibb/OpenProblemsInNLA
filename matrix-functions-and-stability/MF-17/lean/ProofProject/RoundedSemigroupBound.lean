import ProofProject.ScalarSeparation
import ProofProject.RoundedOperators

/-!
# The exact semigroup bound after rounding the Hilbert metric

The scalar approximation error is summed using the coordinate bounds in the
new Hilbert norm. The strict pattern margin then absorbs the error while
retaining the original constant `M`.
-/

noncomputable section

open scoped BigOperators

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {N : ℕ}

/-- A total scalar error `3ε` is absorbed by the strict rounded metric margin. -/
theorem norm_roundedDiagonal_le_of_pattern_approximation (f : Fin N → H) {M : ℝ}
    (hM : 1 < M) (hN : 0 < N) (hf : ∀ j, ‖f j‖ = 1)
    (hpattern : ∀ (c : Fin N → ℂ) (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖)
    (a : Fin N → ℂ)
    (happrox : ∃ (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 ∧
      ∑ j, ‖a j - elementaryPattern i z (fun _ => 1) j‖ ≤
        3 * (metricGamma M N / (12 * M ^ 2))) :
    ‖basisDiagonal (roundedBasis f (metricEta_pos hM hN)) a‖ ≤ M := by
  obtain ⟨i, z, hz, herr⟩ := happrox
  let b := roundedBasis f (metricEta_pos hM hN)
  have hd : ‖basisDiagonal b a - basisPattern b i z‖ ≤
      6 * M * (metricGamma M N / (12 * M ^ 2)) := by
    calc
      _ ≤ (2 * M) * ∑ j, ‖a j - elementaryPattern i z (fun _ => 1) j‖ :=
        norm_basisDiagonal_sub_le b a _ (norm_roundedCoordinate_le f hM hN hf hpattern)
      _ ≤ (2 * M) * (3 * (metricGamma M N / (12 * M ^ 2))) :=
        mul_le_mul_of_nonneg_left herr (by linarith)
      _ = _ := by ring
  have hp := norm_roundedPattern_le f hM hN hf hpattern i z hz
  calc
    _ ≤ ‖basisPattern b i z‖ + ‖basisDiagonal b a - basisPattern b i z‖ := by
      have heq : basisDiagonal b a = basisPattern b i z +
          (basisDiagonal b a - basisPattern b i z) := by abel
      calc
        _ = ‖basisPattern b i z + (basisDiagonal b a - basisPattern b i z)‖ := congrArg norm heq
        _ ≤ _ := norm_add_le _ _
    _ ≤ Real.sqrt (M ^ 2 - metricGamma M N) +
        6 * M * (metricGamma M N / (12 * M ^ 2)) := add_le_add hp hd
    _ ≤ M := metricMargin_absorbs_source_error hM

/-- Separated frequencies give a bounded diagonal semigroup with exactly the
original constant `M`, on the rounded finite-dimensional Hilbert space. -/
theorem norm_rounded_exponential_diagonal_le (n : ℕ) (f : Fin (n + 1) → H) {M : ℝ}
    (hM : 1 < M) (hf : ∀ j, ‖f j‖ = 1)
    (hpattern : ∀ (c : Fin (n + 1) → ℂ) (i : Fin (n + 1)) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖)
    (y : Fin (n + 1) → ℝ) (hy : ∀ j, 0 < y j) (κ : ℝ) (hκ : 1 ≤ κ)
    (hgap : ∀ j : Fin n, κ * (1 + (y j.castSucc) ^ 2) ≤ y j.succ)
    (hsmall : (n + 1 : ℝ) *
      Real.exp (-(metricGamma M (n + 1) / (12 * M ^ 2)) * κ) ≤
        metricGamma M (n + 1) / (12 * M ^ 2))
    (s : ℝ) (hs : 0 ≤ s) :
    ‖basisDiagonal (roundedBasis f (metricEta_pos hM (Nat.succ_pos n)))
      (fun j => Complex.exp ((s : ℂ) * scalarLambda (y j)))‖ ≤ M := by
  apply norm_roundedDiagonal_le_of_pattern_approximation f hM (Nat.succ_pos n) hf hpattern
  apply scalar_pattern_approximation_of_separation n y hy _ κ _ hκ hgap hsmall s hs
  have hM0 : 0 < M := by linarith
  exact div_pos (metricGamma_pos hM) (by positivity)

end ProofProject
