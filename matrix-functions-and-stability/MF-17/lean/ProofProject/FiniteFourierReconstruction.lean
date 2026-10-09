import ProofProject.AveragedFourierFactor
import ProofProject.AveragedFourierEstimate
import ProofProject.SemigroupKernelOperator
import ProofProject.TrianglePartition

/-!
# Finite Fourier reconstruction of the actual semigroup kernel operator

The scalar windows are smooth and compactly supported. Their inverse transforms
are integrable before any uniform frequency estimate is assumed. The triangular
partition and bilinear inversion then reconstruct the actual strong integral.
Only the final norm corollary assumes a bound on the sum of scalar transforms.
-/

noncomputable section

open MeasureTheory Set FourierTransform
open scoped ContDiff

namespace ProofProject.BoundedSemigroup

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A finite partition by arbitrary smooth windows suffices for the exact
reconstruction; neither a scalar oscillatory estimate nor a supremum is used. -/
theorem kernelOperator_finite_fourier_reconstruction (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (J : Finset ℕ) (k : ℝ → ℂ) (hk : Integrable k)
    (hsupp : ∀ s < 0, k s = 0) (f : ℕ → ℝ → ℂ)
    (hf : ∀ j ∈ J, ContDiff ℝ ∞ (f j))
    (hcompact : ∀ j ∈ J, HasCompactSupport (f j))
    (hpartition : ∀ s, ∑ j ∈ J, f j (s - (j : ℝ) * N) *
      (averagingTriangle N (s - (j : ℝ) * N) : ℂ) = k s) (x y : H) :
    inner ℂ y (S.kernelOperator k hk x) =
      ∫ ξ, ∑ j ∈ J, 𝓕⁻ (f j) ξ *
        inner ℂ (star (S.averagedFourierOperator N hN ξ) y)
          (S.op ((j : ℝ) * N) (S.averagedFourierOperator N hN ξ x)) := by
  let F (j : ℕ) (v : ℝ) : ℂ :=
    (averagingTriangle N v : ℂ) * inner ℂ y (S.op (v + (j : ℝ) * N) x)
  have hF (j : ℕ) : Integrable (F j) :=
    S.integrable_averagingTriangle_pairing hN (show 0 ≤ (j : ℝ) * N by positivity) x y
  have hprod (j : ℕ) (hj : j ∈ J) : Integrable (fun v => f j v * F j v) :=
    compactSmooth_mul_integrable (hf j hj) (hcompact j hj) (hF j)
  have hshift (j : ℕ) (hj : j ∈ J) :
      Integrable (fun s => f j (s - (j : ℝ) * N) * F j (s - (j : ℝ) * N)) := by
    simpa only [sub_eq_add_neg] using (hprod j hj).comp_add_right (-((j : ℝ) * N))
  have hfreq (j : ℕ) (hj : j ∈ J) :
      Integrable (fun ξ => 𝓕⁻ (f j) ξ * 𝓕 (F j) ξ) :=
    compactSmooth_fourierInv_mul_fourier_integrable (hf j hj) (hcompact j hj) (hF j)
  have hpair (j : ℕ) (ξ : ℝ) :
      inner ℂ (star (S.averagedFourierOperator N hN ξ) y)
        (S.op ((j : ℝ) * N) (S.averagedFourierOperator N hN ξ x)) = 𝓕 (F j) ξ :=
    S.averagedFourierOperator_pairing_fourier N hN ξ ((j : ℝ) * N)
      (by positivity) x y
  calc
    _ = ∫ s, k s * inner ℂ y (S.op s x) :=
      S.kernelOperator_inner_of_nonneg_support k hk hsupp x y
    _ = ∫ s, ∑ j ∈ J, f j (s - (j : ℝ) * N) * F j (s - (j : ℝ) * N) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s => by
        simp only [F, sub_add_cancel, ← mul_assoc, ← Finset.sum_mul, hpartition]
    _ = ∑ j ∈ J, ∫ s, f j (s - (j : ℝ) * N) * F j (s - (j : ℝ) * N) :=
      integral_finsetSum J hshift
    _ = ∑ j ∈ J, ∫ v, f j v * F j v := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_sub_right_eq_self (μ := volume) (fun v => f j v * F j v) _
    _ = ∑ j ∈ J, ∫ ξ, 𝓕⁻ (f j) ξ * 𝓕 (F j) ξ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (compactSmooth_fourierInv_mul_fourier_integral
        (hf j hj) (hcompact j hj) (hF j)).symm
    _ = ∫ ξ, ∑ j ∈ J, 𝓕⁻ (f j) ξ * 𝓕 (F j) ξ := (integral_finsetSum J hfreq).symm
    _ = _ := by simp only [hpair]

/-- The exact source windows reconstruct the operator on a finite support
interval. The upper endpoint chooses the finite number of translates. -/
theorem kernelOperator_triangular_reconstruction (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (n : ℕ) (k ζ : ℝ → ℂ) (hk : Integrable k)
    (hkd : ContDiff ℝ ∞ k) (hζd : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (hζ : ∀ v ∈ Icc (1 : ℝ) 3, ζ v = 1)
    (hsupp : ∀ s, s ∉ Icc (2 * N) (((n : ℝ) + 1) * N) → k s = 0) (x y : H) :
    inner ℂ y (S.kernelOperator k hk x) =
      ∫ ξ, ∑ j ∈ Finset.range n, triangularKernelCoefficient N k ζ j ξ *
        inner ℂ (star (S.averagedFourierOperator N hN ξ) y)
          (S.op ((j : ℝ) * N) (S.averagedFourierOperator N hN ξ x)) := by
  apply S.kernelOperator_finite_fourier_reconstruction N hN (Finset.range n) k hk
    (fun s hs => hsupp s (by intro hm; linarith [hm.1]))
    (triangularKernelWindow N k ζ)
    (fun j _ => triangularKernelWindow_contDiff N hkd hζd j)
    (fun j _ => triangularKernelWindow_hasCompactSupport hN k hζc j)
  exact triangularKernelWindow_partition hN hζ n hsupp

/-- The finite frequency integrand is integrable independently of a uniform
bound on its scalar coefficients. -/
theorem triangular_reconstruction_integrable (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (n : ℕ) (k ζ : ℝ → ℂ)
    (hkd : ContDiff ℝ ∞ k) (hζd : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (x y : H) :
    Integrable (fun ξ => ∑ j ∈ Finset.range n, triangularKernelCoefficient N k ζ j ξ *
      inner ℂ (star (S.averagedFourierOperator N hN ξ) y)
        (S.op ((j : ℝ) * N) (S.averagedFourierOperator N hN ξ x))) := by
  apply integrable_finsetSum
  intro j hj
  simp only [triangularKernelCoefficient, S.averagedFourierOperator_pairing_fourier
    N hN _ ((j : ℝ) * N) (by positivity) x y]
  exact compactSmooth_fourierInv_mul_fourier_integrable
    (triangularKernelWindow_contDiff N hkd hζd j)
    (triangularKernelWindow_hasCompactSupport hN k hζc j)
    (S.integrable_averagingTriangle_pairing hN (show 0 ≤ (j : ℝ) * N by positivity) x y)

/-- The source reduction: a uniform scalar frequency budget gives `M³ C`
for the actual strong kernel integral, with no dimension or piece-count loss. -/
theorem kernelOperator_norm_le_of_triangular_budget (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (n : ℕ) (k ζ : ℝ → ℂ) (hk : Integrable k)
    (hkd : ContDiff ℝ ∞ k) (hζd : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (hζ : ∀ v ∈ Icc (1 : ℝ) 3, ζ v = 1)
    (hsupp : ∀ s, s ∉ Icc (2 * N) (((n : ℝ) + 1) * N) → k s = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hbudget : ∀ ξ, ∑ j ∈ Finset.range n, ‖triangularKernelCoefficient N k ζ j ξ‖ ≤ C) :
    ‖S.kernelOperator k hk‖ ≤ M ^ 3 * C :=
  S.averagedFourier_reconstruction_norm_le N hN (Finset.range n)
    (triangularKernelCoefficient N k ζ) hC hbudget (S.kernelOperator k hk)
    (S.kernelOperator_triangular_reconstruction N hN n k ζ hk hkd hζd hζc hζ hsupp)

/-- Specialization to the fixed actual cutoff, leaving only the scalar
frequency estimate as the oscillatory obligation. -/
theorem kernelOperator_norm_le_of_source_budget (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (n : ℕ) (k : ℝ → ℂ) (hk : Integrable k)
    (hkd : ContDiff ℝ ∞ k)
    (hsupp : ∀ s, s ∉ Icc (2 * N) (((n : ℝ) + 1) * N) → k s = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hbudget : ∀ ξ, ∑ j ∈ Finset.range n,
      ‖triangularKernelCoefficient N k sourceTriangleCutoff j ξ‖ ≤ C) :
    ‖S.kernelOperator k hk‖ ≤ M ^ 3 * C :=
  S.kernelOperator_norm_le_of_triangular_budget N hN n k sourceTriangleCutoff hk hkd
    sourceTriangleCutoff_contDiff sourceTriangleCutoff_hasCompactSupport
    (fun _ hv => sourceTriangleCutoff_eq_one hv) hsupp hC hbudget

/-- A version stated directly for the original vector integral. Smoothness
and the finite support interval supply all its integrability automatically. -/
theorem norm_sourceKernelIntegral_le (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (n : ℕ) (k : ℝ → ℂ) (hkd : ContDiff ℝ ∞ k)
    (hsupp : ∀ s, s ∉ Icc (2 * N) (((n : ℝ) + 1) * N) → k s = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hbudget : ∀ ξ, ∑ j ∈ Finset.range n,
      ‖triangularKernelCoefficient N k sourceTriangleCutoff j ξ‖ ≤ C) (x : H) :
    ‖∫ s, k s • S.op s x‖ ≤ (M ^ 3 * C) * ‖x‖ := by
  have hc : HasCompactSupport k := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro s hs
    by_contra hn
    exact hs (hsupp s hn)
  have hk : Integrable k := hkd.continuous.integrable_of_hasCompactSupport hc
  rw [← S.kernelOperator_apply_of_nonneg_support k hk
    (fun s hs => hsupp s (by intro hm; linarith [hm.1]))]
  exact ((S.kernelOperator k hk).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (S.kernelOperator_norm_le_of_source_budget
      N hN n k hk hkd hsupp hC hbudget) (norm_nonneg x))

end ProofProject.BoundedSemigroup
