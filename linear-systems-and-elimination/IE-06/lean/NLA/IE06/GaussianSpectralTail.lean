import NLA.IE06.GaussianOperatorNet
import NLA.IE06.KyFan

/-! Gaussian spectral concentration with an explicit universal constant.
This is the independently reviewed A1 alternative, not a claim about the
literal constants of manuscript Lemma 4.1. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp Real
open scoped BigOperators ENNReal NNReal
namespace NLA.IE06.GaussianSpectralTail
open GaussianNull GaussianQuadratic GaussianRegression GaussianFrobenius Spectral KyFan

local instance matrixMeasurable (m n : ℕ) : MeasurableSpace (Matrix (Fin m) (Fin n) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin m → Fin n → ℝ))
local instance matrixBorel (m n : ℕ) : BorelSpace (Matrix (Fin m) (Fin n) ℝ) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))

abbrev EntrySpace (m n : ℕ) := EuclideanSpace ℝ (Fin m × Fin n)

theorem entries_gaussian (m n : ℕ) :
    MeasurePreserving (@entries m n) (gaussianRect m n) (stdGaussian (EntrySpace m n)) := by
  exact (show MeasurePreserving (toLp 2)
      (Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1))
      (stdGaussian (EntrySpace m n)) from ⟨by fun_prop,map_pi_eq_stdGaussian⟩).comp
    ⟨by fun_prop,gaussian_uncurry m n⟩

theorem matrixOfEntries_gaussian (m n : ℕ) :
    MeasurePreserving (@matrixOfEntries m n) (stdGaussian (EntrySpace m n)) (gaussianRect m n) := by
  refine ⟨by unfold matrixOfEntries; fun_prop,?_⟩
  rw [← (entries_gaussian m n).map_eq, Measure.map_map
    (by unfold matrixOfEntries; fun_prop) (entries_gaussian m n).measurable]
  change (gaussianRect m n).map id = gaussianRect m n
  exact Measure.map_id

theorem two_exp_neg_two_lt_one : 2*exp (-(2:ℝ)) < 1 := by
  have h : 2+1  ≤  exp (2:ℝ) := Real.add_one_le_exp 2
  rw [Real.exp_neg]
  apply (mul_inv_lt_iff₀ (exp_pos _)).mpr
  linarith

theorem operator_mean_threshold {m n p : ℕ} (hm : 1  ≤  m)
    (M : Matrix (Fin n) (Fin p) ℝ) :
    2*sqrt (2*frobeniusSq M+4*((m:ℝ)*log 5+2)*opNorm M^2)+2*opNorm M  ≤ 
      16*(frobeniusNorm M+sqrt m*opNorm M) := by
  have hF := frobeniusNorm_nonneg M
  have hL := opNorm_nonneg M
  have hFsq : frobeniusNorm M^2=frobeniusSq M := frobeniusNorm_sq M
  have hm' : 1 ≤ (m:ℝ) := by exact_mod_cast hm
  have hs : 1 ≤ sqrt (m:ℝ) := (Real.one_le_sqrt).mpr hm'
  have hlog : log (5:ℝ) ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<5)
    linarith
  have hcoef : (m:ℝ)*log 5+2  ≤  6*m := by nlinarith
  have hcoef' := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (opNorm M))
  have hsL : (sqrt (m:ℝ)*opNorm M)^2=(m:ℝ)*opNorm M^2 := by
    rw [mul_pow,sq_sqrt (Nat.cast_nonneg m)]
  have hroot : sqrt (2*frobeniusSq M+4*((m:ℝ)*log 5+2)*opNorm M^2)  ≤ 
      2*frobeniusNorm M+6*(sqrt m*opNorm M) := by
    apply (sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (frobeniusNorm M),
        mul_nonneg hF (mul_nonneg (sqrt_nonneg (m:ℝ)) hL)]
  nlinarith

theorem operator_mean_le {m n p : ℕ} (hm : 1 ≤ m)
    (M : Matrix (Fin n) (Fin p) ℝ) :
    (∫ z : EntrySpace m n, opNorm (matrixOfEntries z*M) ∂stdGaussian (EntrySpace m n))  ≤ 
      16*(frobeniusNorm M+sqrt m*opNorm M) := by
  let B := 2*sqrt (2*frobeniusSq M+4*((m:ℝ)*log 5+2)*opNorm M^2)
  have hset : MeasurableSet {G : RectMat m n | B<opNorm (Matrix.of G*M)} := by
    apply measurableSet_lt measurable_const
    have he : Measurable (fun G : RectMat m n => entries (Matrix.of G)) := by
      unfold entries
      fun_prop
    have hf : Measurable (fun z : EntrySpace m n => opNorm (matrixOfEntries z*M)) :=
      (opNorm_mul_lipschitz (m := m) M).continuous.measurable
    convert hf.comp he using 1
    rfl
  have hu := GaussianOperatorNet.operator_net_tail_shift (m := m) M 2 (by norm_num)
  have hp := (matrixOfEntries_gaussian m n).measure_preimage hset.nullMeasurableSet
  have hupper : stdGaussian (EntrySpace m n) {z | B<opNorm (matrixOfEntries z*M)}  ≤ 
      ENNReal.ofReal (exp (-(2:ℝ))) := hp.le.trans hu
  have h := GaussianConcentrationSpace.mean_le_of_upper_tail
    (opNorm_mul_lipschitz (m := m) M) (by norm_num : (0:ℝ)<2)
    two_exp_neg_two_lt_one hupper
  have hs : sqrt (2*(2:ℝ))=2 := by norm_num
  rw [hs] at h
  apply h.trans
  change B+opNorm M*2 ≤ _
  simpa only [B,mul_comm (opNorm M) 2] using operator_mean_threshold hm M

theorem gaussian_singular_tail {m n p k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (hkp : k ≤ p)
    (M : Matrix (Fin n) (Fin p) ℝ) (x : ℝ) (hx : 0 < x) :
    gaussianRect m n {G | 16*frobeniusNorm M+(16*sqrt m+sqrt (2*x/k))*opNorm M <
      singularValue (Matrix.of G*M) (k-1)} ≤ ENNReal.ofReal (exp (-x)) := by
  let f : EntrySpace m n → ℝ := fun z => kyFan k (matrixOfEntries z*M)
  let μ := stdGaussian (EntrySpace m n)
  let a := ∫ z, f z ∂μ
  have hfi : Integrable f μ :=
    GaussianConcentrationSpace.lipschitz_integrable (kyFan_mul_lipschitz k M)
  have hoi : Integrable (fun z : EntrySpace m n => opNorm (matrixOfEntries z*M)) μ :=
    GaussianConcentrationSpace.lipschitz_integrable (opNorm_mul_lipschitz M)
  have hmean : a ≤ sqrt k*(16*(frobeniusNorm M+sqrt m*opNorm M)) := by
    calc
      _ ≤ ∫ z : EntrySpace m n, sqrt k*opNorm (matrixOfEntries z*M) ∂μ :=
        integral_mono hfi (hoi.const_mul _) (fun z => kyFan_le_sqrt_mul_opNorm k _)
      _ = sqrt k*(∫ z : EntrySpace m n, opNorm (matrixOfEntries z*M) ∂μ) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (operator_mean_le (by omega) M) (sqrt_nonneg _)
  have ht := GaussianConcentrationSpace.lipschitz_upper_tail (kyFan_mul_lipschitz (m := m) k M) x hx
  have hset : MeasurableSet {z : EntrySpace m n | opNorm M*sqrt (2*x) < f z-a} :=
    measurableSet_lt measurable_const ((kyFan_mul_lipschitz k M).continuous.measurable.sub measurable_const)
  have hp := (entries_gaussian m n).measure_preimage hset.nullMeasurableSet
  have htail : gaussianRect m n {G | opNorm M*sqrt (2*x) < kyFan k (Matrix.of G*M)-a} ≤
      ENNReal.ofReal (exp (-x)) := hp.le.trans ht
  have hkpos : 0 < (k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hsk : sqrt (k:ℝ)*sqrt (2*x/k)=sqrt (2*x) := by
    rw [← sqrt_mul hkpos.le]
    congr 1
    field_simp
  have hthreshold : sqrt k*(16*frobeniusNorm M+(16*sqrt m+sqrt (2*x/k))*opNorm M) =
      sqrt k*(16*(frobeniusNorm M+sqrt m*opNorm M))+opNorm M*sqrt (2*x) := by
    calc
      _ = sqrt k*(16*(frobeniusNorm M+sqrt m*opNorm M))+
        (sqrt k*sqrt (2*x/k))*opNorm M := by ring
      _ = _ := by rw [hsk]; ring
  apply le_trans (measure_mono ?_) htail
  intro G hG
  have hl := sqrt_mul_singularValue_le_kyFan (Matrix.of G*M) hk hkm hkp
  have hs := mul_lt_mul_of_pos_left hG (sqrt_pos.2 hkpos)
  rw [hthreshold] at hs
  change opNorm M*sqrt (2*x) < kyFan k (Matrix.of G*M)-a
  linarith

#assert_trust kernel entries_gaussian
#assert_trust kernel matrixOfEntries_gaussian
#assert_trust kernel two_exp_neg_two_lt_one
#assert_trust kernel operator_mean_threshold
#assert_trust kernel operator_mean_le
#assert_trust kernel gaussian_singular_tail
#print axioms operator_mean_le
#print axioms gaussian_singular_tail

end NLA.IE06.GaussianSpectralTail
