import OAI.Analysis.DirectCrouzeix.DividedDifferences

namespace OAI

universe u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

def taylorCoeff {E : Type u_94} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (k : ℕ) : E := (k.factorial : ℂ)⁻¹ • iteratedDeriv k f 0

@[simp] theorem taylorCoeff_zero {E : Type u_95} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) : taylorCoeff f 0 = f 0 := by simp [taylorCoeff]

theorem taylorCoeff_congr {E : Type u_96} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : ℂ → E} (h : f =ᶠ[𝓝 0] g) (k : ℕ) : taylorCoeff f k = taylorCoeff g k := by
  rw [taylorCoeff,taylorCoeff,h.iteratedDeriv_eq k]

theorem taylorCoeff_add {E : Type u_97} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f g : ℂ → E} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    taylorCoeff (fun z => f z+g z) k = taylorCoeff f k+taylorCoeff g k := by
  simp only [taylorCoeff,iteratedDeriv_fun_add (n := k) hf.contDiffAt hg.contDiffAt,smul_add]

theorem taylorCoeff_sum {E : Type u_98} {ι : Type u_99} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E]
    (I : Finset ι) {f : ι → ℂ → E} (hf : ∀ i ∈ I, AnalyticAt ℂ (f i) 0) (k : ℕ) :
    taylorCoeff (fun z => ∑ i ∈ I, f i z) k = ∑ i ∈ I, taylorCoeff (f i) k := by
  simp only [taylorCoeff, iteratedDeriv_fun_sum (fun i hi => (hf i hi).contDiffAt),Finset.smul_sum]

theorem taylorCoeff_smul_const {E : Type u_100} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (v : E) (k : ℕ) :
    taylorCoeff (fun z => f z • v) k = taylorCoeff f k • v := by
  rw [taylorCoeff,iteratedDeriv_smul_const hf.contDiffAt,taylorCoeff,smul_smul,smul_eq_mul]

@[simp] theorem taylorCoeff_const {E : Type u_101} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : E) (k : ℕ) : taylorCoeff (fun _ => v) k = if k = 0 then v else 0 := by
  by_cases hk : k = 0
  · subst k; simp
  · simp [taylorCoeff,iteratedDeriv_const,hk]

theorem taylorCoeff_pow_mul {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (j k : ℕ) :
    taylorCoeff (fun u => u^j*f u) k = if j ≤ k then taylorCoeff f (k-j) else 0 := by
  classical
  rw [taylorCoeff,iteratedDeriv_fun_mul (f := fun u : ℂ => u^j) (n := k) (by fun_prop) hf.contDiffAt]
  simp only [iteratedDeriv_fun_pow_zero, Nat.cast_ite, Nat.cast_zero]
  by_cases hjk : j ≤ k
  · rw [Finset.sum_eq_single j]
    · simp only [ite_true,smul_eq_mul,ite_eq_left hjk,taylorCoeff]
      have hfac : (k.factorial : ℂ) = (k.choose j : ℂ) * (j.factorial : ℂ) * ((k-j).factorial : ℂ) := by
        exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hjk).symm
      have hkn : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      have hjn : ((k-j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp
      linear_combination -(iteratedDeriv (k-j) f 0)*hfac
    · intro i hi hij
      simp [hij]
    · exact fun h => (h (Finset.mem_range.mpr (Nat.lt_succ_of_le hjk))).elim
  · rw [ite_eq_right hjk]
    have he : ∑ i ∈ Finset.range (k+1), (k.choose i : ℂ) *
        (if i = j then (j.factorial : ℂ) else 0) * iteratedDeriv (k-i) f 0 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hij : i ≠ j := by have hik := Finset.mem_range.mp hi; omega
      simp [hij]
    rw [he,smul_zero]

theorem taylorCoeff_eq_series {E : Type u_102} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E]
    {f : ℂ → E} {p : FormalMultilinearSeries ℂ ℂ E} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p 0 r) (k : ℕ) : taylorCoeff f k = p.coeff k := by
  have hh := hp.iteratedFDeriv_eq_sum_of_completeSpace (fun _ : Fin k => (1:ℂ))
  simp only [← iteratedDeriv_eq_iteratedFDeriv,Finset.sum_const,Finset.card_univ,
    Fintype.card_perm,Fintype.card_fin] at hh
  change iteratedDeriv k f 0 = k.factorial • p.coeff k at hh
  rw [taylorCoeff,hh,← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  simp [Nat.factorial_ne_zero]

abbrev Angle := AddCircle (1:ℝ)

abbrev angularMeasure : Measure Angle := AddCircle.haarAddCircle

def unitPoint (t : Angle) : ℂ := fourier 1 t

@[simp] theorem unitPoint_norm (t : Angle) : ‖unitPoint t‖ = 1 := by
  simp [unitPoint,fourier_apply,Circle.norm_coe]

theorem unitPoint_continuous : Continuous unitPoint := (fourier 1).continuous

theorem unitPoint_pow (t : Angle) (k : ℕ) : unitPoint t ^ k = fourier (k:ℤ) t := by
  simp only [unitPoint,fourier_apply,one_zsmul,← Circle.coe_pow,
    ← AddCircle.toCircle_nsmul,natCast_zsmul]

theorem integral_character_smul {E : Type u_103} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (a b : ℤ) (v : E) :
    (∫ t : Angle, fourier (-a) t • (fourier b t • v) ∂angularMeasure) = if b = a then v else 0 := by
  rw [show (fun t : Angle => fourier (-a) t • (fourier b t • v)) =
      (fun t => (fourier (-a) t * fourier b t) • v) by funext t; rw [smul_smul],
    integral_smul_const]
  have hh := congrFun (fourierCoeff_fourier (T := (1:ℝ)) b) a
  change (∫ t : Angle, fourier (-a) t * fourier b t ∂angularMeasure) = _ at hh
  rw [hh]
  by_cases hab : b = a
  · subst b; simp
  · simp [Ne.symm hab,hab]

theorem fourierCoeff_of_powerSeries {E : Type u_104} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {p : FormalMultilinearSeries ℂ ℂ E} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p 0 r) (hr : 1 < r) (k : ℤ) :
    fourierCoeff (fun t : Angle => f (unitPoint t)) k =
      if 0 ≤ k then taylorCoeff f k.toNat else 0 := by
  have h1 : (1:ℂ) ∈ Metric.eball 0 p.radius := by
    simpa [Metric.mem_eball,edist_dist] using hr.trans_le hp.r_le
  have hs : Summable (fun n => ‖p.coeff n‖) := by
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,one_pow,one_smul] using p.summable_norm_apply h1
  have hp' (t : Angle) : HasSum (fun n : ℕ => fourier n t • p.coeff n) (f (unitPoint t)) := by
    have ht : unitPoint t ∈ Metric.eball 0 r := by
      simpa [Metric.mem_eball,edist_dist] using hr
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,unitPoint_pow,zero_add] using hp.hasSum ht
  have hi := hasSum_integral_of_dominated_convergence
    (μ := angularMeasure) (bound := fun (n : ℕ) (_ : Angle) => ‖p.coeff n‖)
    (F := fun (n : ℕ) (t : Angle) => fourier (-k) t • (fourier n t • p.coeff n))
    (f := fun t => fourier (-k) t • f (unitPoint t))
    (fun n => ((fourier (-k)).continuous.smul ((fourier n).continuous.smul continuous_const)).aestronglyMeasurable)
    (fun n => ae_of_all _ (fun t => by simp [norm_smul,fourier_apply,Circle.norm_coe]))
    (ae_of_all _ (fun _ => hs)) (integrable_const _)
    (ae_of_all _ (fun t => (hp' t).const_smul (fourier (-k) t)))
  simp only [integral_character_smul] at hi
  change HasSum (fun n : ℕ => if (n:ℤ) = k then p.coeff n else 0)
    (fourierCoeff (fun t : Angle => f (unitPoint t)) k) at hi
  rw [← hi.tsum_eq]
  cases k with
  | ofNat k =>
    simp [taylorCoeff_eq_series hp]
  | negSucc k =>
    simp

theorem fourierCoeff_of_analytic {E : Type u_105} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {R : ℝ} (hR : 1 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (k : ℤ) :
    fourierCoeff (fun t : Angle => f (unitPoint t)) k =
      if 0 ≤ k then taylorCoeff f k.toNat else 0 := by
  obtain ⟨ρ,hρ1,hρR⟩ := exists_between hR
  let ρ' : ℝ≥0 := ⟨ρ,by linarith⟩
  have hd : DifferentiableOn ℂ f (closedBall 0 (ρ':ℝ)) :=
    hf.differentiableOn.mono (closedBall_subset_ball hρR)
  have hp := hd.hasFPowerSeriesOnBall (R := ρ') (by change 0 < ρ; linarith)
  apply fourierCoeff_of_powerSeries hp
  exact_mod_cast hρ1

end DirectCrouzeix.Faber

end

end

end OAI
