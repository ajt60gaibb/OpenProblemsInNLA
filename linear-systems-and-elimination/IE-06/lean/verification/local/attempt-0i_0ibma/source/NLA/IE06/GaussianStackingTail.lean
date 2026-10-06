import NLA.IE06.SpectralMeasurability
import NLA.IE06.KernelFrame
import NLA.IE06.GaussianCompression
import NLA.IE06.GaussianSpectralTail
import NLA.IE06.GaussianOvercrowding

/-! Fixed-candidate stacking, before any adaptive row-set union bound.
Exact preimplementation contract: selected-block-extension-specification.md. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal
namespace NLA.IE06.GaussianStackingTail
open GaussianNull GaussianQuadratic Spectral SpectralStacking KyFan
open SpectralMeasurability GaussianCompression

def productThreshold (s j : ℕ) (a f x : ℝ) : ℝ :=
  16*f+(16*Real.sqrt s+Real.sqrt (2*x/(j+1)))*a

def compressionThreshold (s j : ℕ) (θ : ℝ) : ℝ :=
  j*θ/(4*Real.exp 1*Real.sqrt s)

def stackingThreshold (s j : ℕ) (a f x θ : ℝ) : ℝ :=
  (a+(1+productThreshold s j a f x)/compressionThreshold s j θ)⁻¹/2

theorem compressRows_eq_mul {s p q : ℕ} (Q : Matrix (Fin p) (Fin q) ℝ)
    (B : RectMat s p) : Matrix.of (compressRows Q B) = Matrix.of B*Q := by
  ext i j
  simp only [Matrix.of_apply,compressRows,compressVector,euclideanMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,Matrix.toLpLin_apply,
    Matrix.mulVec,Matrix.mul_apply,dotProduct,Matrix.conjTranspose_apply,
    RCLike.star_def,conj_trivial,ofLp_toLp]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- Intrinsic lower-tail stacking estimate. The nullspace frame is fixed
inside this proof and does not appear in the event or as a stochastic premise. -/
theorem gaussian_stacking_tail {m s j : ℕ}
    (M : Matrix (Fin m) (Fin (m+s)) ℝ)
    (hM : Function.Surjective (euclideanMap M))
    (hj : 4  ≤  j) (hjs : 2*j  <  s) (hjm : j  <  m)
    {a f x θ : ℝ} (ha : 0  <  a) (hf : 0  ≤  f)
    (hA : opNorm (pinv M) ≤ a) (hF : frobeniusNorm (pinv M) ≤ f)
    (hx : 0  <  x) (hθ : 0  <  θ) (hθone : θ  ≤  1) :
    gaussianRect s (m+s) {B |
      singularValue (Matrix.fromRows M (Matrix.of B)) (m+s-2*j-1)  ≤ 
        stackingThreshold s j a f x θ}  ≤ 
      ENNReal.ofReal (Real.exp (-x))+
        ENNReal.ofReal ((s:ℝ)^(j+1)*θ^((j:ℝ)^2/4)) := by
  obtain ⟨Q,hQ,hker⟩ := KernelFrame.exists_kernel_frame M hM
  let u := productThreshold s j a f x
  let ℓ := compressionThreshold s j θ
  have hℓ : 0 < ℓ := by
    dsimp [ℓ,compressionThreshold]
    have hjr : (0:ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hsr : (0:ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    positivity
  have hu : 0 ≤ u := by dsimp [u,productThreshold]; positivity
  let badP : Set (RectMat s (m+s)) := {B | u < singularValue (Matrix.of B*pinv M) j}
  let badQ : Set (RectMat s (m+s)) := {B | singularValue (Matrix.of B*Q) (s-j-1) ≤ ℓ}
  have hP : gaussianRect s (m+s) badP  ≤  ENNReal.ofReal (Real.exp (-x)) := by
    have h := GaussianSpectralTail.gaussian_singular_tail (m:=s) (k:=j+1)
      (by omega) (by omega) (by omega) (pinv M) x hx
    apply (measure_mono ?_).trans h
    intro B hB
    have hcap : 16*frobeniusNorm (pinv M)+
        (16*Real.sqrt s+Real.sqrt (2*x/(j+1)))*opNorm (pinv M) ≤ u := by
      dsimp [u,productThreshold]
      gcongr
    simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Set.mem_ofPred_eq] using hcap.trans_lt hB
  have hQtail : gaussianRect s (m+s) badQ  ≤ 
      ENNReal.ofReal ((s:ℝ)^(j+1)*θ^((j:ℝ)^2/4)) := by
    have hmp := compressRows_measurePreserving (p:=s) Q hQ
    have h := Measure.le_map_apply (μ := gaussianRect s (m+s)) hmp.measurable.aemeasurable
      {H : RectMat s s | singularValue (Matrix.of H) (s-j-1) ≤ ℓ}
    rw [hmp.map_eq] at h
    have ht := GaussianOvercrowding.gaussian_overcrowding (n:=s) hj (by omega) hθ hθone
    have he : badQ = compressRows Q ⁻¹'
        {H : RectMat s s | singularValue (Matrix.of H) (s-j-1) ≤ ℓ} := by
      ext B
      simp only [badQ,Set.mem_preimage,Set.mem_ofPred_eq,compressRows_eq_mul]
    rw [he]
    exact h.trans ht
  have hsub : {B : RectMat s (m+s) |
      singularValue (Matrix.fromRows M (Matrix.of B)) (m+s-2*j-1)  ≤ 
        stackingThreshold s j a f x θ} ⊆ badP∪badQ := by
    intro B hB
    change singularValue (Matrix.fromRows M (Matrix.of B)) (m+s-2*j-1) ≤
      stackingThreshold s j a f x θ at hB
    by_contra hn
    have hgood : singularValue (Matrix.of B*pinv M) j ≤ u ∧
        ℓ < singularValue (Matrix.of B*Q) (s-j-1) := by
      simpa only [Set.mem_union,badP,badQ,Set.mem_ofPred_eq,not_or,not_lt,not_le] using hn
    have hd : 0 < singularValue (Matrix.of B*Q) (s-j-1) := hℓ.trans hgood.2
    have hs := spectral_stacking M (Matrix.of B) Q hM hQ hker hjs hjm hd
    let C := a+(1+u)/ℓ
    have hC : 0 < C := by dsimp [C]; positivity
    have hD : 0 < opNorm (pinv M)+(1+singularValue (Matrix.of B*pinv M) j)/
        singularValue (Matrix.of B*Q) (s-j-1) := by
      have hnon := singularValue_nonneg (Matrix.of B*pinv M) j
      have hp := opNorm_nonneg (pinv M)
      positivity
    have hDC : opNorm (pinv M)+(1+singularValue (Matrix.of B*pinv M) j)/
        singularValue (Matrix.of B*Q) (s-j-1)  ≤  C := by
      dsimp [C]
      gcongr
      · exact hgood.1
      · exact hgood.2.le
    have hR : C⁻¹  ≤  singularValue (Matrix.fromRows M (Matrix.of B)) (m+s-2*j-1) := by
      apply le_trans ?_ hs
      simpa only [one_div] using one_div_le_one_div_of_le hD hDC
    have he : stackingThreshold s j a f x θ=C⁻¹/2 := rfl
    rw [he] at hB
    have hi : 0 < C⁻¹ := inv_pos.mpr hC
    linarith
  calc
    _  ≤  gaussianRect s (m+s) (badP∪badQ) := measure_mono hsub
    _  ≤  gaussianRect s (m+s) badP+gaussianRect s (m+s) badQ := measure_union_le _ _
    _  ≤  _ := add_le_add hP hQtail

#assert_trust kernel productThreshold
#assert_trust kernel compressionThreshold
#assert_trust kernel stackingThreshold
#assert_trust kernel compressRows_eq_mul
#assert_trust kernel gaussian_stacking_tail
#print axioms productThreshold
#print axioms compressionThreshold
#print axioms stackingThreshold
#print axioms compressRows_eq_mul
#print axioms gaussian_stacking_tail

end NLA.IE06.GaussianStackingTail
