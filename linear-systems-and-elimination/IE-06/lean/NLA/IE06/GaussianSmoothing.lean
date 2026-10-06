import NLA.IE06.EliminationSmoothing
import NLA.IE06.GaussianCompression
import NLA.IE06.GaussianOperatorInverse
import NLA.IE06.GaussianFrobenius

/-! Exact Gaussian smoothing of fixed discarded directions. The independent
preimplementation review is in reviews/gaussian-smoothing-specification.md. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators ENNReal
namespace NLA.IE06.GaussianSmoothing
open GaussianNull GaussianRegression GaussianFrobenius Spectral KyFan EliminationSmoothing

theorem row_squared_tail {n s : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    {ζ : ℝ} (_hζ : 0 ≤ ζ) (hX : rowNorm X i ≤ ζ) (x : ℝ) (hx : 0 < x) :
    gaussianRect n s {G | (2*(s:ℝ)+4*x)*ζ^2 < rowNorm (X*Matrix.of G) i^2} ≤
      ENNReal.ofReal (Real.exp (-x)) := by
  let M : Matrix (Fin n) (Fin 1) ℝ := fun j _ => X i j
  have hF : frobeniusSq M = rowNorm X i^2 := by
    rw [rowNorm_sq]
    simp [frobeniusSq,M]
  have hO : euclideanOpNorm M^2 ≤ rowNorm X i^2 := by
    calc
      _ ≤ frobeniusNorm M^2 := pow_le_pow_left₀ (opNorm_nonneg M)
        (opNorm_le_frobeniusNorm M) 2
      _ = rowNorm X i^2 := by rw [frobeniusNorm_sq]; exact hF
  have hcap : 2*(s:ℝ)*frobeniusSq M+4*x*euclideanOpNorm M^2 ≤ (2*(s:ℝ)+4*x)*ζ^2 := by
    have hh := pow_le_pow_left₀ (rowNorm_nonneg X i) hX 2
    rw [hF]
    calc
      _ ≤ (2*(s:ℝ)+4*x) * rowNorm X i^2 := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)
  let event : Set (RectMat s n) := {G | 2*(s:ℝ)*frobeniusSq M+
    4*x*euclideanOpNorm M^2 < frobeniusSq (Matrix.of G*M)}
  have ht : MeasurePreserving (@GaussianRegression.transpose n s)
      (gaussianRect n s) (gaussianRect s n) :=
    ⟨by unfold GaussianRegression.transpose; fun_prop, gaussian_transpose n s⟩
  have he (G : RectMat n s) : frobeniusSq (Matrix.of (GaussianRegression.transpose G)*M) =
      rowNorm (X*Matrix.of G) i^2 := by
    rw [rowNorm_sq]
    simp [frobeniusSq,M,Matrix.mul_apply,GaussianRegression.transpose,mul_comm]
  calc
    _ ≤ gaussianRect n s (GaussianRegression.transpose ⁻¹' event) := measure_mono (by
      intro G hG
      change 2*(s:ℝ)*frobeniusSq M+4*x*euclideanOpNorm M^2 < _
      rw [he]
      exact hcap.trans_lt hG)
    _ ≤ (gaussianRect n s).map GaussianRegression.transpose event :=
      Measure.le_map_apply ht.measurable.aemeasurable event
    _ = gaussianRect s n event := by rw [ht.map_eq]
    _ ≤ _ := centered_gaussian_frobenius_tail M x hx

theorem row_tail {n s : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hX : rowNorm X i ≤ ζ) (x : ℝ) (hx : 0 < x) :
    gaussianRect n s {G | Real.sqrt (2*(s:ℝ)+4*x)*ζ < rowNorm (X*Matrix.of G) i} ≤
      ENNReal.ofReal (Real.exp (-x)) := by
  apply (measure_mono (show {G : RectMat n s | Real.sqrt (2*(s:ℝ)+4*x)*ζ <
      rowNorm (X*Matrix.of G) i} ⊆
      {G | (2*(s:ℝ)+4*x)*ζ^2 < rowNorm (X*Matrix.of G) i^2} from ?_)).trans
    (row_squared_tail X i hζ hX x hx)
  intro G hG
  have hs : (Real.sqrt (2*(s:ℝ)+4*x)*ζ)^2 = (2*(s:ℝ)+4*x)*ζ^2 := by
    rw [mul_pow,Real.sq_sqrt (by positivity)]
  have hz : 0 ≤ Real.sqrt (2*(s:ℝ)+4*x)*ζ := mul_nonneg (Real.sqrt_nonneg _) hζ
  change (2*(s:ℝ)+4*x)*ζ^2 < _
  rw [← hs]
  exact pow_lt_pow_left₀ hG hz (by decide)

theorem rows_tail {n s : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hX : ∀ i, rowNorm X i ≤ ζ) (x : ℝ) (hx : 0 < x) :
    gaussianRect n s {G | ∃ i, Real.sqrt (2*(s:ℝ)+4*x)*ζ < rowNorm (X*Matrix.of G) i} ≤
      (n:ℝ≥0∞) * ENNReal.ofReal (Real.exp (-x)) := by
  rw [show {G : RectMat n s | ∃ i, Real.sqrt (2*(s:ℝ)+4*x)*ζ < rowNorm (X*Matrix.of G) i} =
    ⋃ i : Fin n, {G | Real.sqrt (2*(s:ℝ)+4*x)*ζ < rowNorm (X*Matrix.of G) i} from by ext G; simp]
  calc
    _ ≤ ∑ i : Fin n, gaussianRect n s {G | Real.sqrt (2*(s:ℝ)+4*x)*ζ < rowNorm (X*Matrix.of G) i} := by
      simpa only [tsum_fintype] using measure_iUnion_le (μ := gaussianRect n s)
        (fun i : Fin n => {G | Real.sqrt (2*(s:ℝ)+4*x)*ζ < rowNorm (X*Matrix.of G) i})
    _ ≤ ∑ _i : Fin n, ENNReal.ofReal (Real.exp (-x)) :=
      Finset.sum_le_sum (fun i _ => row_tail X i hζ (hX i) x hx)
    _ = _ := by simp

/-- Exact smoothing with any row-operation function. The bad event is bounded
as an outer measure, so no measurability of J is assumed or needed. -/
theorem gaussian_smoothing {n q r s : ℕ} (E X : Matrix (Fin n) (Fin n) ℝ)
    (Y Q : Matrix (Fin n) (Fin q) ℝ) (hE : E = X+Y*Qᴴ) (hQ : Qᴴ*Q = 1)
    (hr : 0 < r) (hqr : q ≤ r) (hrs : 3*r ≤ s)
    {ζ L : ℝ} (hζ : 0 ≤ ζ) (hL : 0 ≤ L) (hX : ∀ i, rowNorm X i ≤ ζ)
    (x : ℝ) (hx : 0 < x) (J : RectMat n s → Matrix (Fin n) (Fin n) ℝ) :
    gaussianRect n s {G | (∀ i, rowL1 (J G) i ≤ L) ∧
      (J G * E) * Matrix.of G = 0 ∧ ∃ i,
      L*ζ*(1+Real.sqrt (2*(s:ℝ)+4*x)*Real.sqrt (3*Real.exp (2+x/r)/r)) <
        rowNorm (J G*E) i} ≤
      ((n:ℝ≥0∞)+1)*ENNReal.ofReal (Real.exp (-x)) := by
  let R : Set (RectMat n s) := {G | ∃ i, Real.sqrt (2*(s:ℝ)+4*x)*ζ < rowNorm (X*Matrix.of G) i}
  let P : Set (RectMat n s) := {G | 3*Real.exp (2+x/r)/r < opNorm (pinv (Qᴴ*Matrix.of G))^2}
  have hR : gaussianRect n s R ≤ (n:ℝ≥0∞)*ENNReal.ofReal (Real.exp (-x)) := rows_tail X hζ hX x hx
  have hmp := GaussianCompression.compress_measurePreserving (p := s) Q hQ
  have hP : gaussianRect n s P ≤ ENNReal.ofReal (Real.exp (-x)) := by
    let S : Set (RectMat q s) := {G | 3*Real.exp (2+x/r)/r < opNorm (pinv (Matrix.of G))^2}
    have he : P = GaussianCompression.compress Q ⁻¹' S := rfl
    rw [he]
    calc
      _ ≤ (gaussianRect n s).map (GaussianCompression.compress Q) S :=
        Measure.le_map_apply hmp.measurable.aemeasurable S
      _ = gaussianRect q s S := by rw [hmp.map_eq]
      _ ≤ _ := GaussianOperatorInverse.gaussian_pinv_tail hr hqr hrs x
  have hqs : q ≤ s := by omega
  have hrank : ∀ᵐ G ∂gaussianRect n s,
      ((Qᴴ*Matrix.of G)*(Qᴴ*Matrix.of G)ᴴ).PosDef :=
    hmp.quasiMeasurePreserving.ae (gram_posDef_ae q s hqs)
  have hinc : {G : RectMat n s | (∀ i, rowL1 (J G) i ≤ L) ∧
      (J G*E)*Matrix.of G = 0 ∧ ∃ i,
      L*ζ*(1+Real.sqrt (2*(s:ℝ)+4*x)*Real.sqrt (3*Real.exp (2+x/r)/r)) <
        rowNorm (J G*E) i} ≤ᵐ[gaussianRect n s] (fun G => G ∈ R ∨ G ∈ P) := by
    filter_upwards [hrank] with G hG
    intro hbad
    by_contra hout
    have hnotR : G ∉ R := fun h => hout (Or.inl h)
    have hnotP : G ∉ P := fun h => hout (Or.inr h)
    have hrows : ∀ i, rowNorm (X*Matrix.of G) i ≤ Real.sqrt (2*(s:ℝ)+4*x)*ζ := by
      intro i
      exact le_of_not_gt (fun h => hnotR ⟨i,h⟩)
    have hopSq : opNorm (pinv (Qᴴ*Matrix.of G))^2 ≤ 3*Real.exp (2+x/r)/r :=
      le_of_not_gt hnotP
    have hop : opNorm (pinv (Qᴴ*Matrix.of G)) ≤ Real.sqrt (3*Real.exp (2+x/r)/r) :=
      (Real.le_sqrt (opNorm_nonneg _) (by positivity)).mpr hopSq
    obtain ⟨i,hi⟩ := hbad.2.2
    have hb := cancellation_pinv_row_bound E X Y Q (Matrix.of G) (J G) hE hQ hG
      hbad.2.1 hζ (mul_nonneg (Real.sqrt_nonneg _) hζ) hL hX hrows hbad.1 i
    have hbound : rowNorm (J G*E) i ≤
        L*ζ*(1+Real.sqrt (2*(s:ℝ)+4*x)*Real.sqrt (3*Real.exp (2+x/r)/r)) := by
      calc
        _ ≤ L*(ζ+(Real.sqrt (2*(s:ℝ)+4*x)*ζ)*opNorm (pinv (Qᴴ*Matrix.of G))) := hb
        _ ≤ L*(ζ+(Real.sqrt (2*(s:ℝ)+4*x)*ζ)*Real.sqrt (3*Real.exp (2+x/r)/r)) := by
          gcongr
        _ = _ := by ring
    exact (not_lt_of_ge hbound) hi
  calc
    _ ≤ gaussianRect n s (R ∪ P) := measure_mono_ae hinc
    _ ≤ gaussianRect n s R + gaussianRect n s P := measure_union_le _ _
    _ ≤ (n:ℝ≥0∞)*ENNReal.ofReal (Real.exp (-x)) + ENNReal.ofReal (Real.exp (-x)) := add_le_add hR hP
    _ = _ := by rw [add_mul,one_mul]

#assert_trust kernel row_squared_tail
#assert_trust kernel row_tail
#assert_trust kernel rows_tail
#assert_trust kernel gaussian_smoothing
#print axioms row_squared_tail
#print axioms row_tail
#print axioms rows_tail
#print axioms gaussian_smoothing
end NLA.IE06.GaussianSmoothing
