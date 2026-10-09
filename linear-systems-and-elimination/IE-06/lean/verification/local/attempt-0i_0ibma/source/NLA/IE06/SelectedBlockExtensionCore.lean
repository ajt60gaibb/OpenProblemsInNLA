import NLA.IE06.SelectedBlockAppend

/-! The complete probabilistic part of selected-block extension. Its scalar
inputs are explicit thresholds, not assumed probabilistic manuscript lemmas. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped ENNReal
namespace NLA.IE06.SelectedBlockExtensionCore
open GaussianNull Spectral KyFan TruncatedInverse GaussianCandidateStacking
open GaussianStackingTail SelectedBlockCandidates SelectedBlockAppend

theorem extension_tail_of_threshold {n m k d j : ℕ}
    (hp : m+4*k ≤ n) (hk : 0 < k) (hkm : k < m)
    (hj : 4 ≤ j) (hjs : 2*j < 4*k) (hjm : j < m) (hjd : 2*j ≤ d)
    {μ x₀ x θ δ : ℝ} (hμ : 0 < μ) (hμk : μ^2 ≤ k)
    (hx₀ : 0 < x₀) (hx : 0 < x) (hθ : 0 < θ) (hθone : θ ≤ 1)
    (hδ : δ ≤ stackingThreshold (4*k) j (appendScale k μ x₀)
      (Real.sqrt k*appendScale k μ x₀) x θ) :
    gaussianMatrix n {A |
      μ ≤ singularValue (Matrix.of (actualBlock (by omega : m ≤ n) A)) (m-k-1) ∧
      sigmaInvSum (Matrix.of (actualBlock (by omega : m ≤ n) A)) k ≤ 2*k*(μ⁻¹)^2 ∧
      singularValue (Matrix.of (actualBlock hp A)) (m+4*k-d-1) ≤ δ} ≤
      ENNReal.ofReal (2*Real.exp (-x₀))+
        (n:ℝ≥0∞)^(4*k)*(ENNReal.ofReal (Real.exp (-x))+
          ENNReal.ofReal (((4*k:ℕ):ℝ)^(j+1)*θ^((j:ℝ)^2/4))) := by
  let a := appendScale k μ x₀
  let f := Real.sqrt k*a
  let P : Set (Mat n) := {A | initialGood k μ (actualBlock (by omega : m ≤ n) A) ∧
    ¬inverseCap a f (Matrix.of (extendedBlock hp A))}
  let Q : Set (Mat n) := {A | A.det ≠ 0 ∧ inverseCap a f (Matrix.of (extendedBlock hp A)) ∧
    singularValue (Matrix.of (actualBlock hp A)) (m+4*k-2*j-1) ≤ stackingThreshold (4*k) j a f x θ}
  have hP : gaussianMatrix n P ≤ ENNReal.ofReal (2*Real.exp (-x₀)) :=
    actual_append_bad_tail hp hk hkm hμ hμk hx₀
  have ha : 0 < a := appendScale_pos k hμ x₀
  have hf : 0 ≤ f := mul_nonneg (Real.sqrt_nonneg _) ha.le
  have hQ := actual_stacking_union_tail hp hj hjs hjm ha hf hx hθ hθone
  have hnon : ∀ᵐ A : Mat n ∂gaussianMatrix n, A.det ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using gaussianMatrix_singular_null_proved n
  have hsub : {A : Mat n |
      μ ≤ singularValue (Matrix.of (actualBlock (by omega : m ≤ n) A)) (m-k-1) ∧
      sigmaInvSum (Matrix.of (actualBlock (by omega : m ≤ n) A)) k ≤ 2*k*(μ⁻¹)^2 ∧
      singularValue (Matrix.of (actualBlock hp A)) (m+4*k-d-1) ≤ δ}
      ≤ᵐ[gaussianMatrix n] (fun A => A∈P∪Q) := by
    filter_upwards [hnon] with A hA
    intro hbad
    have hT : (actualBlock (by omega : m ≤ n) A).det ≠ 0 :=
      SelectedBlockElimination.selectedBlock_det_ne_zero _ A hA
    by_cases hcap : inverseCap a f (Matrix.of (extendedBlock hp A))
    · apply Or.inr
      refine ⟨hA,hcap,?_⟩
      have hind : m+4*k-d-1 ≤ m+4*k-2*j-1 := by omega
      exact ((singularValue_antitone _ hind).trans hbad.2.2).trans hδ
    · exact Or.inl ⟨⟨hT,hbad.1,hbad.2.1⟩,hcap⟩
  calc
    _ ≤ gaussianMatrix n (P∪Q) := measure_mono_ae hsub
    _ ≤ gaussianMatrix n P+gaussianMatrix n Q := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2*Real.exp (-x₀))+
        (n:ℝ≥0∞)^(4*k)*(ENNReal.ofReal (Real.exp (-x))+
          ENNReal.ofReal (((4*k:ℕ):ℝ)^(j+1)*θ^((j:ℝ)^2/4))) := add_le_add hP hQ

#assert_trust kernel extension_tail_of_threshold
#print axioms extension_tail_of_threshold

end NLA.IE06.SelectedBlockExtensionCore
