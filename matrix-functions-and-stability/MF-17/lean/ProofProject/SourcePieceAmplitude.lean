import ProofProject.DampedPowerDerivatives
import ProofProject.SourcePieceCutoff
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The actual damped source-piece amplitudes

The cutoff removes the singularity of the negative power at zero. Leibniz's
formula combines the two independently proved all-order derivative estimates,
retaining the exponential damping and choosing constants before the piece
index and time. A single constant is then selected for orders zero through
three, as required by the source pieces and their differentiated kernels.
-/

noncomputable section

open Set Filter Finset
open scoped ContDiff Topology

namespace ProofProject

def sourcePieceAmplitudeReal (q : ℕ) (t u : ℝ) : ℝ :=
  dampedPower (-3 / 4) t u * sourcePieceCutoff q u

/-- The source amplitude, regarded as complex-valued for the kernel operator. -/
def sourcePieceAmplitude (q : ℕ) (t u : ℝ) : ℂ :=
  (sourcePieceAmplitudeReal q t u : ℂ)

theorem sourcePieceAmplitudeReal_eq_zero_of_le (q : ℕ) (t : ℝ) {u : ℝ}
    (hu : u ≤ 2 * sourcePieceScale q) : sourcePieceAmplitudeReal q t u = 0 := by
  simp only [sourcePieceAmplitudeReal, sourcePieceCutoff_eq_zero_of_le q hu, mul_zero]

theorem sourcePieceAmplitudeReal_eq_zero_of_ge (q : ℕ) (t : ℝ) {u : ℝ}
    (hu : 4 * sourcePieceScale (q + 1) ≤ u) : sourcePieceAmplitudeReal q t u = 0 := by
  simp only [sourcePieceAmplitudeReal, sourcePieceCutoff_eq_zero_of_ge q hu, mul_zero]

theorem sourcePieceAmplitude_eq_zero_of_le (q : ℕ) (t : ℝ) {u : ℝ}
    (hu : u ≤ 2 * sourcePieceScale q) : sourcePieceAmplitude q t u = 0 := by
  simp only [sourcePieceAmplitude, sourcePieceAmplitudeReal_eq_zero_of_le q t hu,
    Complex.ofReal_zero]

theorem sourcePieceAmplitude_eq_zero_of_ge (q : ℕ) (t : ℝ) {u : ℝ}
    (hu : 4 * sourcePieceScale (q + 1) ≤ u) : sourcePieceAmplitude q t u = 0 := by
  simp only [sourcePieceAmplitude, sourcePieceAmplitudeReal_eq_zero_of_ge q t hu,
    Complex.ofReal_zero]

theorem sourcePieceAmplitudeReal_contDiff (q : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (sourcePieceAmplitudeReal q t) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : 0 < u
  · exact (dampedPower_contDiffAt (-3 / 4) t hu).mul
      (sourcePieceCutoff_contDiff q).contDiffAt
  · have hlow : u < 2 * sourcePieceScale q := by
      have := sourcePieceScale_pos q
      linarith
    have heq : sourcePieceAmplitudeReal q t =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
      filter_upwards [gt_mem_nhds hlow] with v hv
      exact sourcePieceAmplitudeReal_eq_zero_of_le q t hv.le
    exact contDiffAt_const.congr_of_eventuallyEq heq

theorem sourcePieceAmplitude_contDiff (q : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (sourcePieceAmplitude q t) :=
  Complex.ofRealCLM.contDiff.comp (sourcePieceAmplitudeReal_contDiff q t)

theorem sourcePieceAmplitude_support_subset (q : ℕ) (t : ℝ) :
    Function.support (sourcePieceAmplitude q t) ⊆
      Ioo (2 * sourcePieceScale q) (4 * sourcePieceScale (q + 1)) := by
  intro u hu
  constructor
  · by_contra h
    exact hu (sourcePieceAmplitude_eq_zero_of_le q t (le_of_not_gt h))
  · by_contra h
    exact hu (sourcePieceAmplitude_eq_zero_of_ge q t (le_of_not_gt h))

theorem sourcePieceAmplitude_tsupport_subset (q : ℕ) (t : ℝ) :
    tsupport (sourcePieceAmplitude q t) ⊆
      Icc (2 * sourcePieceScale q) (4 * sourcePieceScale (q + 1)) :=
  closure_minimal ((sourcePieceAmplitude_support_subset q t).trans Ioo_subset_Icc_self) isClosed_Icc

theorem sourcePieceAmplitude_hasCompactSupport (q : ℕ) (t : ℝ) :
    HasCompactSupport (sourcePieceAmplitude q t) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (sourcePieceAmplitude_tsupport_subset q t)

/-- Every complex iterated derivative is the real derivative with its value
cast into the complex numbers. -/
theorem iteratedDeriv_sourcePieceAmplitude (q : ℕ) (t : ℝ) (n : ℕ) :
    iteratedDeriv n (sourcePieceAmplitude q t) =
      fun u => ((iteratedDeriv n (sourcePieceAmplitudeReal q t) u : ℝ) : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iteratedDeriv_succ, ih]
      funext u
      exact (((sourcePieceAmplitudeReal_contDiff q t).differentiable_iteratedDeriv n
        (by exact_mod_cast (ENat.natCast_lt_top n)) u).hasDerivAt.ofReal_comp).deriv

@[simp] theorem norm_iteratedDeriv_sourcePieceAmplitude (q : ℕ) (t u : ℝ) (n : ℕ) :
    ‖iteratedDeriv n (sourcePieceAmplitude q t) u‖ =
      ‖iteratedDeriv n (sourcePieceAmplitudeReal q t) u‖ := by
  rw [iteratedDeriv_sourcePieceAmplitude, Complex.norm_real]

/-- All derivative orders vanish strictly below the piece's lower threshold. -/
theorem sourcePieceAmplitudeReal_iteratedDeriv_eq_zero_of_lt (q n : ℕ) (t : ℝ) {u : ℝ}
    (hu : u < 2 * sourcePieceScale q) :
    iteratedDeriv n (sourcePieceAmplitudeReal q t) u = 0 := by
  have heq : sourcePieceAmplitudeReal q t =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
    filter_upwards [gt_mem_nhds hu] with v hv
    exact sourcePieceAmplitudeReal_eq_zero_of_le q t hv.le
  rw [heq.iteratedDeriv_eq n]
  simp

theorem sourcePieceAmplitude_iteratedDeriv_eq_zero_of_lt (q n : ℕ) (t : ℝ) {u : ℝ}
    (hu : u < 2 * sourcePieceScale q) : iteratedDeriv n (sourcePieceAmplitude q t) u = 0 := by
  rw [iteratedDeriv_sourcePieceAmplitude]
  change ((iteratedDeriv n (sourcePieceAmplitudeReal q t) u : ℝ) : ℂ) = 0
  rw [sourcePieceAmplitudeReal_iteratedDeriv_eq_zero_of_lt q n t hu, Complex.ofReal_zero]

private theorem sourcePieceAmplitude_rpow_combine {u : ℝ} (hu : 0 < u)
    {i n : ℕ} (hi : i ≤ n) :
    u ^ (-3 / 4 - (i : ℝ)) * u ^ (-((n - i : ℕ) : ℝ)) =
      u ^ (-3 / 4 - (n : ℝ)) := by
  rw [← Real.rpow_add hu]
  congr 1
  rw [Nat.cast_sub hi]
  ring

/-- For every derivative order, the actual amplitude satisfies the original
weighted estimate with an absolute constant independent of piece and time. -/
theorem exists_sourcePieceAmplitude_derivative_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (t : ℝ), 0 < t → ∀ u : ℝ, 0 < u →
      ‖iteratedDeriv n (sourcePieceAmplitude q t) u‖ ≤
        C * Real.exp (-sourcePieceScale q / t) * u ^ (-3 / 4 - (n : ℝ)) := by
  choose D hDpos hD using exists_sourcePieceCutoff_weighted_derivative_bound
  let B : ℝ := ∑ i ∈ range (n + 1),
    (n.choose i : ℝ) * dampedPowerDerivativeBound (-3 / 4) i * D (n - i)
  have hB : 0 ≤ B := by
    apply sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (dampedPowerDerivativeBound_nonneg (-3 / 4) i)) (hDpos (n - i)).le
  refine ⟨B + 1, by linarith, fun q t ht u hu => ?_⟩
  rw [norm_iteratedDeriv_sourcePieceAmplitude]
  by_cases hNu : 2 * sourcePieceScale q ≤ u
  · have hpow : ContDiffAt ℝ n (dampedPower (-3 / 4) t) u :=
      (dampedPower_contDiffAt (-3 / 4) t hu).of_le
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    have hcut : ContDiffAt ℝ n (sourcePieceCutoff q) u :=
      (sourcePieceCutoff_contDiff q).contDiffAt.of_le
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    have heq : sourcePieceAmplitudeReal q t =
        dampedPower (-3 / 4) t * sourcePieceCutoff q := rfl
    rw [heq, iteratedDeriv_mul hpow hcut]
    calc
      _ ≤ ∑ i ∈ range (n + 1), ‖(n.choose i : ℝ) *
          iteratedDeriv i (dampedPower (-3 / 4) t) u *
          iteratedDeriv (n - i) (sourcePieceCutoff q) u‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range (n + 1),
          ((n.choose i : ℝ) * dampedPowerDerivativeBound (-3 / 4) i * D (n - i)) *
            Real.exp (-sourcePieceScale q / t) * u ^ (-3 / 4 - (n : ℝ)) := by
        apply sum_le_sum
        intro i hi
        have hin : i ≤ n := Nat.le_of_lt_succ (mem_range.mp hi)
        have hdb := norm_iteratedDeriv_dampedPower_le (-3 / 4) i ht hu hNu
        have hcb := hD (n - i) q u hu
        have hdb0 := dampedPowerDerivativeBound_nonneg (-3 / 4) i
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
        calc
          _ ≤ ((n.choose i : ℝ) * (dampedPowerDerivativeBound (-3 / 4) i *
              Real.exp (-sourcePieceScale q / t) * u ^ (-3 / 4 - (i : ℝ)))) *
                (D (n - i) * u ^ (-((n - i : ℕ) : ℝ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hdb (Nat.cast_nonneg _)) hcb
              (norm_nonneg _) (by positivity)
          _ = ((n.choose i : ℝ) * dampedPowerDerivativeBound (-3 / 4) i * D (n - i)) *
              Real.exp (-sourcePieceScale q / t) *
                (u ^ (-3 / 4 - (i : ℝ)) * u ^ (-((n - i : ℕ) : ℝ))) := by ring
          _ = _ := by rw [sourcePieceAmplitude_rpow_combine hu hin]
      _ = B * Real.exp (-sourcePieceScale q / t) * u ^ (-3 / 4 - (n : ℝ)) := by
        simp only [B, sum_mul]
      _ ≤ _ := by
        gcongr
        linarith
  · rw [sourcePieceAmplitudeReal_iteratedDeriv_eq_zero_of_lt q n t (lt_of_not_ge hNu), norm_zero]
    positivity

/-- One constant works simultaneously for orders zero through three. -/
theorem exists_sourcePieceAmplitude_weighted_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (t : ℝ), 0 < t → ∀ n : ℕ, n ≤ 3 →
      ∀ u : ℝ, 0 < u → ‖iteratedDeriv n (sourcePieceAmplitude q t) u‖ ≤
        C * Real.exp (-sourcePieceScale q / t) * u ^ (-3 / 4 - (n : ℝ)) := by
  choose C hCpos hC using exists_sourcePieceAmplitude_derivative_bound
  let B : ℝ := 1 + ∑ n ∈ range 4, C n
  have hsum : 0 ≤ ∑ n ∈ range 4, C n := sum_nonneg (fun n _ => (hCpos n).le)
  refine ⟨B, by dsimp [B]; linarith, fun q t ht n hn u hu => ?_⟩
  have hCn : C n ≤ B := by
    have h := single_le_sum (fun i (_ : i ∈ range 4) => (hCpos i).le)
      (show n ∈ range 4 by simp only [Finset.mem_range]; omega)
    dsimp only [B]
    linarith
  exact (hC n q t ht u hu).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCn (Real.exp_pos _).le) (Real.rpow_nonneg hu.le _))

/-- The same common constant in the derivative notation used by the source
one-interval theorem and its differentiated-amplitude application. -/
theorem exists_sourcePieceAmplitude_weighted_bounds_through_three :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (t : ℝ), 0 < t →
      (∀ u > 0, ‖sourcePieceAmplitude q t u‖ ≤
        C * Real.exp (-sourcePieceScale q / t) * u ^ (-3 / 4 : ℝ)) ∧
      (∀ u > 0, ‖deriv (sourcePieceAmplitude q t) u‖ ≤
        C * Real.exp (-sourcePieceScale q / t) * u ^ (-3 / 4 - 1 : ℝ)) ∧
      (∀ u > 0, ‖deriv (deriv (sourcePieceAmplitude q t)) u‖ ≤
        C * Real.exp (-sourcePieceScale q / t) * u ^ (-3 / 4 - 2 : ℝ)) ∧
      (∀ u > 0, ‖deriv (deriv (deriv (sourcePieceAmplitude q t))) u‖ ≤
        C * Real.exp (-sourcePieceScale q / t) * u ^ (-3 / 4 - 3 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := exists_sourcePieceAmplitude_weighted_bound
  refine ⟨C, hC, fun q t ht => ⟨?_, ?_, ?_, ?_⟩⟩
  · simpa only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] using hb q t ht 0 (by omega)
  · simpa only [iteratedDeriv_one, Nat.cast_one] using hb q t ht 1 (by omega)
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_ofNat] using
      hb q t ht 2 (by omega)
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_ofNat] using
      hb q t ht 3 (by omega)

end ProofProject
