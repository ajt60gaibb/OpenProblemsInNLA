import NLA.IE06.SelectedBlockExtensionCore
import NLA.IE06.SelectedBlockExtensionScalars
import NLA.IE06.GaussianSpectralRecursion

/-! Unconditional manuscript Lemma 5.4 with an explicit uniform constant. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
namespace NLA.IE06.SelectedBlockExtension

theorem failure_sum_le (n s : ℕ) {a b c L : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcb : c ≤ b) (hL : a+2*(n:ℝ)^s*b ≤ L) :
    ENNReal.ofReal a+(n:ℝ≥0∞)^s*(ENNReal.ofReal b+ENNReal.ofReal c) ≤ ENNReal.ofReal L := by
  calc
    _ ≤ ENNReal.ofReal a+(n:ℝ≥0∞)^s*(ENNReal.ofReal b+ENNReal.ofReal b) := by
      gcongr
    _ = ENNReal.ofReal (a+2*(n:ℝ)^s*b) := by
      rw [ENNReal.ofReal_add ha (by positivity),ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_pow (Nat.cast_nonneg n)]
      simp only [ENNReal.ofReal_ofNat,ENNReal.ofReal_natCast]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal hL

open GaussianNull Spectral TruncatedInverse SelectedBlockCandidates
open SelectedBlockExtensionScalars

/-- Manuscript Lemma 5.4 for the actual Gaussian matrix and its actual selected
pivot blocks, with a proved uniform explicit constant. -/
theorem extension_tail {n m k d : ℕ} (hn : m+4*k ≤ n) (hkm : k < m)
    (hd : 16 ≤ d) (hk : 100*d ≤ k) {β μ : ℝ} (hβ : 1 ≤ β) (hμ : 0 < μ)
    (hμk : μ < Real.sqrt k) :
    gaussianMatrix n {A |
      μ ≤ singularValue (actualBlock (by omega : m ≤ n) A) (m-k-1) ∧
      sigmaInvSum (actualBlock (by omega : m ≤ n) A) k ≤ 2*k*(μ⁻¹)^2 ∧
      singularValue (actualBlock hn A) (m+4*k-d-1) ≤
        (μ*d/k)*Real.exp (-extensionConstant β*(1+(k:ℝ)*Real.log n/(d:ℝ)^2))} ≤
      ENNReal.ofReal (Real.exp (-β*Real.log n)) := by
  obtain ⟨hk1600,h5n,hn4,hj8,h2j,hdj,hdj1,hj1k,h2js,hjm⟩ :=
    dimensions hn hkm hd hk
  have hk0 : 0 < k := by omega
  have hμsq : μ^2 ≤ (k:ℝ) := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    nlinarith [sq_nonneg (Real.sqrt k-μ)]
  obtain ⟨hx₀,hx⟩ := budgets_pos (k:=k) (show 1 < n by omega) hβ
  have hthreshold := source_threshold_le hn hkm hd hk hβ hμ hμk.le
  have hprob := SelectedBlockExtensionCore.extension_tail_of_threshold hn hk0 hkm
    (show 4 ≤ d/2 by omega) h2js hjm h2j hμ hμsq hx₀ hx
    (theta_pos n k d β) (theta_le_one (show 1 ≤ n by omega) hβ) hthreshold
  have hsum := failure_sum_le n (4*k) (by positivity : 0 ≤ 2*Real.exp (-firstBudget n β))
    (Real.exp_pos (-candidateBudget n k β)).le
    (overcrowding_term_le hn hkm hd hk hβ) (probability_accounting hn4 β)
  exact hprob.trans hsum

/-- The exact interface consumed by the scalar spectral recursion, now supplied
by the unconditional selected-block probability theorem. -/
theorem extension_bound (n : ℕ) {β : ℝ} (hβ : 1 ≤ β) :
    GaussianSpectralRecursion.ExtensionBound n β (extensionConstant β) := by
  intro m k d hn hkm hd hk μ hμ hμk
  exact extension_tail hn hkm hd hk hβ hμ hμk

#assert_trust kernel failure_sum_le
#print axioms failure_sum_le
#assert_trust kernel extension_tail
#print axioms extension_tail
#assert_trust kernel extension_bound
#print axioms extension_bound

end NLA.IE06.SelectedBlockExtension
