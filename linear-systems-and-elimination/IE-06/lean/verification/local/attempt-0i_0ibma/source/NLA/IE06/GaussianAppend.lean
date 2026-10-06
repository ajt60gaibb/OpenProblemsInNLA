/-
Gaussian append bounds with exact Euclidean norms and the actual iid law.
The independently approved preimplementation contract and numerical constants
are in reviews/gaussian-append-specification.md.
-/
import NLA.IE06.GaussianCompression
import NLA.IE06.RightInverseBounds
import NLA.IE06.GaussianOperatorInverse
import NLA.IE06.GaussianOperatorNet
import NLA.IE06.TruncatedInverse

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators
namespace NLA.IE06.GaussianAppend
open GaussianNull GaussianRegression Spectral KyFan RightInverseBounds

def appendConstant : ℝ := 2+98316*Real.exp 2

theorem appendConstant_pos : 0 < appendConstant := by unfold appendConstant; positivity

theorem append_scalar_bounds {k : ℕ} (hk : 0<k) {a l p x : ℝ}
    (ha : 0≤a) (_hl : 0≤l) (hp : 0≤p) (hx : 0<x)
    (hscale : 1≤(k:ℝ)*a) (hL : l≤8192*((k:ℝ)+x)*a)
    (hP : p≤3*Real.exp (2+x/k)/k) :
    2*a+4*(1+l)*p ≤ appendConstant*a*Real.exp (2*x/k) ∧
    2*k*a+k*(1+l)*p ≤ appendConstant*k*a*Real.exp (2*x/k) := by
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  have hbase : 1+l≤8193*((k:ℝ)+x)*a := by nlinarith only [hscale,hL,mul_nonneg hx.le ha]
  have hmul := mul_le_mul hbase hP hp (by positivity : 0≤8193*((k:ℝ)+x)*a)
  have heq : 8193*((k:ℝ)+x)*a*(3*Real.exp (2+x/k)/k) =
      24579*Real.exp 2*a*(1+x/k)*Real.exp (x/k) := by
    rw [Real.exp_add]
    field_simp
    ring
  have he : 1+x/(k:ℝ)≤Real.exp (x/k) := by
    simpa only [add_comm] using Real.add_one_le_exp (x/k)
  have hexp : Real.exp (x/k)*Real.exp (x/k)=Real.exp (2*x/k) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hbound : (1+l)*p ≤ 24579*Real.exp 2*a*Real.exp (2*x/k) := by
    calc
      _ ≤ _ := hmul.trans_eq heq
      _ ≤ 24579*Real.exp 2*a*Real.exp (x/k)*Real.exp (x/k) := by gcongr
      _ = _ := by rw [mul_assoc, hexp]
  have heone : 1≤Real.exp (2*x/(k:ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
  have hab := mul_le_mul_of_nonneg_left heone ha
  have hkbound := mul_le_mul_of_nonneg_left hbound hkr.le
  have hkbase := mul_le_mul_of_nonneg_left hab hkr.le
  have hbonus : 0≤Real.exp 2*(k:ℝ)*a*Real.exp (2*x/k) := by positivity
  unfold appendConstant
  constructor
  · nlinarith only [hbound,hab]
  · nlinarith only [hkbound,hkbase,hbonus]

/-- The net tail applied to a transposed matrix controls the exact RG product. -/
theorem retained_product_tail {n k : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    {a x : ℝ} (ha : 0≤a) (hx : 0<x) (hF : frobeniusNorm R^2≤2*k*a)
    (hR : opNorm R^2≤a) :
    gaussianRect n (4*k) {G | 8192*((k:ℝ)+x)*a < opNorm (R*Matrix.of G)^2} ≤
      ENNReal.ofReal (Real.exp (-x)) := by
  have ht := GaussianOperatorNet.operator_net_tail_shift (m:=4*k) Rᴴ x hx
  have hmp : MeasurePreserving (@GaussianRegression.transpose n (4*k))
      (gaussianRect n (4*k)) (gaussianRect (4*k) n) :=
    ⟨by unfold GaussianRegression.transpose; fun_prop, gaussian_transpose n (4*k)⟩
  let b := 2*Real.sqrt (2*GaussianFrobenius.frobeniusSq Rᴴ+
    4*((4*k:ℕ)*Real.log 5+x)*opNorm Rᴴ^2)
  have hb0 : 0≤b := by dsimp only [b]; positivity
  have hlog : Real.log (5:ℝ)≤2 := by
    have he : (5:ℝ)≤Real.exp 2 := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤2) 3
      norm_num [Finset.sum_range_succ] at h
      linarith
    exact (Real.log_le_iff_le_exp (by norm_num)).mpr he
  have hrad : 0≤2*GaussianFrobenius.frobeniusSq Rᴴ+
      4*((4*k:ℕ)*Real.log 5+x)*opNorm Rᴴ^2 := by
    have hlog0 : 0≤Real.log (5:ℝ) := Real.log_nonneg (by norm_num)
    have hf0 : 0≤GaussianFrobenius.frobeniusSq Rᴴ := by unfold GaussianFrobenius.frobeniusSq; positivity
    positivity
  have hbsq : b^2≤8192*((k:ℝ)+x)*a := by
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt hrad, GaussianFrobenius.frobeniusSq, ← frobeniusNorm_sq,
      frobeniusNorm_conjTranspose, opNorm_conjTranspose]
    have hk0 : (0:ℝ)≤k := Nat.cast_nonneg k
    have hc : 0≤4*((4*k:ℕ)*Real.log 5+x) := by
      have hlog0 : 0≤Real.log (5:ℝ) := Real.log_nonneg (by norm_num)
      positivity
    have h2 := mul_le_mul_of_nonneg_left hR hc
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h2 ⊢
    have h3 := mul_le_mul_of_nonneg_right hlog (mul_nonneg hk0 ha)
    nlinarith only [hF,h2,h3,mul_nonneg hk0 ha,mul_nonneg hx.le ha]
  have hsub : {G : RectMat n (4*k) | 8192*((k:ℝ)+x)*a < opNorm (R*Matrix.of G)^2} ⊆
      GaussianRegression.transpose ⁻¹' {H : RectMat (4*k) n | b<opNorm (Matrix.of H*Rᴴ)} := by
    intro G hG
    have he : Matrix.of (GaussianRegression.transpose G)*Rᴴ=(R*Matrix.of G)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      rfl
    change b<opNorm (Matrix.of (GaussianRegression.transpose G)*Rᴴ)
    rw [he,opNorm_conjTranspose]
    have hg : 8192*((k:ℝ)+x)*a<opNorm (R*Matrix.of G)^2 := hG
    nlinarith only [hg,hbsq,hb0,opNorm_nonneg (R*Matrix.of G)]
  exact (measure_mono hsub).trans ((Measure.le_map_apply hmp.measurable.aemeasurable _).trans
    (by rw [hmp.map_eq]; exact ht))

/-- A5 with an explicit universal constant and the stronger exponent 2 and
failure coefficient 2. M may be singular; only the retained singular values
and their reciprocal-square sum are constrained. The event uses the genuine
spectral pseudoinverse of the actual appended matrix. -/
theorem gaussian_append_tail {n k : ℕ} (hk : 0<k) (hkn : k<n)
    (M : Matrix (Fin n) (Fin n) ℝ) {μ x : ℝ} (hμ : 0<μ) (hμk : μ^2≤k)
    (hs : μ ≤ singularValue M (n-k-1))
    (hSigma : TruncatedInverse.sigmaInvSum M k≤2*k*(μ⁻¹)^2) (hx : 0<x) :
    gaussianRect n (4*k) {G |
      appendConstant*(μ⁻¹)^2*Real.exp (2*x/k)<opNorm (pinv (append M (Matrix.of G)))^2 ∨
      appendConstant*k*(μ⁻¹)^2*Real.exp (2*x/k)<frobeniusNorm (pinv (append M (Matrix.of G)))^2} ≤
      ENNReal.ofReal (2*Real.exp (-x)) := by
  obtain ⟨R,U,hU,hMR,hRU,hRF,hRo⟩ := TruncatedInverse.exists_retained_decomposition M hkn hμ hs
  have hRsq : opNorm R^2≤(μ⁻¹)^2 := pow_le_pow_left₀ (opNorm_nonneg _) hRo 2
  have hFsq : frobeniusNorm R^2≤2*k*(μ⁻¹)^2 := hRF.le.trans hSigma
  have hscale : 1≤(k:ℝ)*(μ⁻¹)^2 := by
    have h : 1≤(k:ℝ)/μ^2 := (le_div_iff₀ (sq_pos_of_pos hμ)).mpr (by simpa using hμk)
    simpa only [one_mul,div_eq_mul_inv,inv_pow] using h
  let badL : Set (RectMat n (4*k)) := {G | 8192*((k:ℝ)+x)*(μ⁻¹)^2<opNorm (R*Matrix.of G)^2}
  let badP : Set (RectMat n (4*k)) := {G | 3*Real.exp (2+x/k)/k<
    opNorm (pinv (Matrix.of (GaussianCompression.compress U G)))^2}
  have hL : gaussianRect n (4*k) badL≤ENNReal.ofReal (Real.exp (-x)) :=
    retained_product_tail R (sq_nonneg _) hx hFsq hRsq
  have hmp := GaussianCompression.compress_measurePreserving (p:=4*k) U hU
  have hP : gaussianRect n (4*k) badP≤ENNReal.ofReal (Real.exp (-x)) := by
    apply (Measure.le_map_apply hmp.measurable.aemeasurable
      {H : RectMat k (4*k) | 3*Real.exp (2+x/k)/k<opNorm (pinv (Matrix.of H))^2}).trans
    rw [hmp.map_eq]
    exact GaussianOperatorInverse.gaussian_pinv_tail hk le_rfl (by omega) x
  have hAE : ∀ᵐ G ∂gaussianRect n (4*k),
      (gram (GaussianCompression.compress U G)).PosDef :=
    hmp.quasiMeasurePreserving.ae (gram_posDef_ae k (4*k) (by omega))
  have hsub : {G : RectMat n (4*k) |
      appendConstant*(μ⁻¹)^2*Real.exp (2*x/k)<opNorm (pinv (append M (Matrix.of G)))^2 ∨
      appendConstant*k*(μ⁻¹)^2*Real.exp (2*x/k)<frobeniusNorm (pinv (append M (Matrix.of G)))^2}
      ≤ᵐ[gaussianRect n (4*k)] (fun G => G∈badL ∨ G∈badP) := by
    filter_upwards [hAE] with G hG
    intro hbad
    by_contra hnone
    have hgood : opNorm (R*Matrix.of G)^2≤8192*((k:ℝ)+x)*(μ⁻¹)^2 ∧
        opNorm (pinv (Matrix.of (GaussianCompression.compress U G)))^2≤3*Real.exp (2+x/k)/k := by
      simpa only [badL,badP,Set.mem_union,Set.mem_ofPred_eq,not_or,not_lt] using hnone
    let P := pinv (Matrix.of (GaussianCompression.compress U G))
    have hXP : (Uᴴ*Matrix.of G)*P=1 := mul_pinv_eq_one _ hG.isUnit
    have hJ := append_mul_rightInverse M R U (Matrix.of G) P hMR hXP
    have hmin := pinv_norms_le_rightInverse _ _ hJ
    have hdet := appendRightInverse_bounds R U (Matrix.of G) P hU hRU
    have hscalar := append_scalar_bounds hk (sq_nonneg (μ⁻¹))
      (sq_nonneg (opNorm (R*Matrix.of G))) (sq_nonneg (opNorm P)) hx hscale hgood.1 hgood.2
    have hBop : opNorm (pinv (append M (Matrix.of G)))^2 ≤
        appendConstant*(μ⁻¹)^2*Real.exp (2*x/k) := by
      have h1 := pow_le_pow_left₀ (opNorm_nonneg _) hmin.1 2
      have h2 := hdet.1
      have h3 := hscalar.1
      nlinarith only [h1,h2,h3,hRsq]
    have hBF : frobeniusNorm (pinv (append M (Matrix.of G)))^2 ≤
        appendConstant*k*(μ⁻¹)^2*Real.exp (2*x/k) := by
      have h1 := pow_le_pow_left₀ (frobeniusNorm_nonneg _) hmin.2 2
      have h2 := hdet.2
      have h3 := hscalar.2
      nlinarith only [h1,h2,h3,hFsq]
    exact hbad.elim (not_lt_of_ge hBop) (not_lt_of_ge hBF)
  calc
    _ ≤ gaussianRect n (4*k) (badL∪badP) := measure_mono_ae hsub
    _ ≤ gaussianRect n (4*k) badL+gaussianRect n (4*k) badP := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-x))+ENNReal.ofReal (Real.exp (-x)) := add_le_add hL hP
    _ = _ := by rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]; congr 1; ring

/-- Direct manuscript-form A5, with one explicit common universal constant.
The earlier theorem is stronger in both exponent and failure coefficient. -/
theorem gaussian_append_tail_source {n k : ℕ} (hk : 0<k) (hkn : k<n)
    (M : Matrix (Fin n) (Fin n) ℝ) {μ x : ℝ} (hμ : 0<μ)
    (hμk : μ≤Real.sqrt k) (hs : μ ≤ singularValue M (n-k-1))
    (hSigma : TruncatedInverse.sigmaInvSum M k≤2*k*(μ⁻¹)^2) (hx : 1≤x) :
    gaussianRect n (4*k) {G |
      appendConstant*(μ⁻¹)^2*Real.exp (appendConstant*x/k)<opNorm (pinv (append M (Matrix.of G)))^2 ∨
      appendConstant*k*(μ⁻¹)^2*Real.exp (appendConstant*x/k)<frobeniusNorm (pinv (append M (Matrix.of G)))^2} ≤
      ENNReal.ofReal (3*Real.exp (-x)) := by
  have hμsq : μ^2≤(k:ℝ) := (Real.le_sqrt hμ.le (Nat.cast_nonneg k)).mp hμk
  have hx0 : 0<x := lt_of_lt_of_le zero_lt_one hx
  have hC : 2≤appendConstant := by
    unfold appendConstant
    exact le_add_of_nonneg_right (by positivity)
  have he : Real.exp (2*x/k)≤Real.exp (appendConstant*x/k) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC hx0.le) (Nat.cast_nonneg k)
  have ho := mul_le_mul_of_nonneg_left he
    (mul_nonneg appendConstant_pos.le (sq_nonneg (μ⁻¹)))
  have hf := mul_le_mul_of_nonneg_left he
    (mul_nonneg (mul_nonneg appendConstant_pos.le (Nat.cast_nonneg k)) (sq_nonneg (μ⁻¹)))
  calc
    _ ≤ gaussianRect n (4*k) {G |
        appendConstant*(μ⁻¹)^2*Real.exp (2*x/k)<opNorm (pinv (append M (Matrix.of G)))^2 ∨
        appendConstant*k*(μ⁻¹)^2*Real.exp (2*x/k)<frobeniusNorm (pinv (append M (Matrix.of G)))^2} :=
      measure_mono (fun _ h => h.elim (fun h => Or.inl (ho.trans_lt h)) (fun h => Or.inr (hf.trans_lt h)))
    _ ≤ ENNReal.ofReal (2*Real.exp (-x)) := gaussian_append_tail hk hkn M hμ hμsq hs hSigma hx0
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [Real.exp_nonneg (-x)])

#assert_trust kernel appendConstant
#print axioms appendConstant
#assert_trust kernel appendConstant_pos
#print axioms appendConstant_pos
#assert_trust kernel append_scalar_bounds
#print axioms append_scalar_bounds
#assert_trust kernel retained_product_tail
#print axioms retained_product_tail
#assert_trust kernel gaussian_append_tail
#print axioms gaussian_append_tail
#assert_trust kernel gaussian_append_tail_source
#print axioms gaussian_append_tail_source
end NLA.IE06.GaussianAppend
