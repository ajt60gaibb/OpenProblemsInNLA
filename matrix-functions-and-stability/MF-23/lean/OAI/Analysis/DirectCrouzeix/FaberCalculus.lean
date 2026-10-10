import OAI.Analysis.DirectCrouzeix.FaberEnergy

namespace OAI

universe u_129 u_130

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

section BanachAlgebra

variable {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]

theorem analyticAt_ringInverse {x : 𝔄} (hx : IsUnit x) :
    AnalyticAt ℂ Ring.inverse x := by
  rcases hx with ⟨u,rfl⟩
  exact analyticAt_inverse u

theorem ringInverse_smul {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄]
    [CompleteSpace 𝔄] {c : ℂ} (hc : c ≠ 0) (x : 𝔄) :
    Ring.inverse (c • x) = c⁻¹ • Ring.inverse x := by
  have hu : IsUnit (algebraMap ℂ 𝔄 c) := (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℂ 𝔄)
  have hi : Ring.inverse (algebraMap ℂ 𝔄 c) = algebraMap ℂ 𝔄 c⁻¹ := by
    have hm : algebraMap ℂ 𝔄 c * algebraMap ℂ 𝔄 c⁻¹ = 1 := by
      rw [← map_mul,mul_inv_cancel₀ hc,map_one]
    calc
      Ring.inverse (algebraMap ℂ 𝔄 c) = Ring.inverse (algebraMap ℂ 𝔄 c) *
          (algebraMap ℂ 𝔄 c * algebraMap ℂ 𝔄 c⁻¹) := by rw [hm,mul_one]
      _ = algebraMap ℂ 𝔄 c⁻¹ := by rw [← mul_assoc,Ring.inverse_mul_cancel _ hu,one_mul]
  rw [Algebra.smul_def,Ring.inverse_mul (Or.inl hu),hi,Algebra.smul_def,Algebra.commutes]

theorem ringInverse_geometric {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄]
    [CompleteSpace 𝔄] (x : 𝔄) (hx : IsUnit (1-x)) (k : ℕ) :
    Ring.inverse (1-x) = (∑ j ∈ Finset.range (k+1),x^j) + x^(k+1)*Ring.inverse (1-x) := by
  have he := congrArg (fun y : 𝔄 => y * Ring.inverse (1-x)) (geom_sum_mul_neg x (k+1))
  rw [mul_assoc,Ring.mul_inverse_cancel _ hx,mul_one,sub_mul,one_mul] at he
  exact (eq_add_of_sub_eq he.symm)

theorem taylorCoeff_pow_smul_zero {E : Type u_130} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : AnalyticAt ℂ f 0) {j k : ℕ} (hjk : k < j) :
    taylorCoeff (fun u => u^j • f u) k = 0 := by
  have he := iteratedDerivWithin_smul (𝕜 := ℂ) (𝔸 := ℂ) (F := E) (n := k)
    (x := 0) (s := univ) (f := fun u : ℂ => u^j) (g := f)
    (mem_univ _) uniqueDiffOn_univ (by fun_prop) hf.contDiffAt.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at he
  change (k.factorial : ℂ)⁻¹ • iteratedDeriv k ((fun u : ℂ => u^j) • f) 0 = 0
  rw [he]
  have hz : (∑ i ∈ Finset.range (k+1), k.choose i •
      iteratedDeriv i (fun u : ℂ => u^j) 0 • iteratedDeriv (k-i) f 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i ≠ j := by have := Finset.mem_range.mp hi; omega
    simp only [iteratedDeriv_fun_pow_zero,ite_eq_right hij,Nat.cast_zero,smul_zero,zero_smul]
  rw [hz,smul_zero]

def algebraDenominator (c : ℂ) (g : ℂ → ℂ) (A : 𝔄) (u : ℂ) : 𝔄 :=
  (c+u*g u) • 1-u • A

def algebraGenerating (c : ℂ) (g : ℂ → ℂ) (A : 𝔄) (u : ℂ) : 𝔄 :=
  (c-u^2*deriv g u) • Ring.inverse (algebraDenominator c g A u)

theorem analyticAt_algebraDenominator {𝔄 : Type u_129} [NormedRing 𝔄]
    [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] {c : ℂ} {g : ℂ → ℂ} {u : ℂ}
    (hg : AnalyticAt ℂ g u) (A : 𝔄) : AnalyticAt ℂ (algebraDenominator c g A) u := by
  exact ((analyticAt_const.add (analyticAt_id.mul hg)).smul analyticAt_const).sub
    (analyticAt_id.smul analyticAt_const)

theorem analyticAt_algebraGenerating {c : ℂ} {g : ℂ → ℂ} {u : ℂ}
    (hg : AnalyticAt ℂ g u) (A : 𝔄) (hu : IsUnit (algebraDenominator c g A u)) :
    AnalyticAt ℂ (algebraGenerating c g A) u :=
  (analyticAt_const.sub ((analyticAt_id.pow 2).mul hg.deriv)).smul
    ((analyticAt_ringInverse hu).comp (analyticAt_algebraDenominator hg A))

theorem algebraGenerating_local {c : ℂ} {g : ℂ → ℂ} (A : 𝔄) {u : ℂ}
    (h : c+u*g u ≠ 0) :
    algebraGenerating c g A u = localN c g u • Ring.inverse (1-localW c g u • A) := by
  have he : algebraDenominator c g A u = (c+u*g u) • (1-localW c g u • A) := by
    simp only [algebraDenominator,smul_sub,smul_smul,localW,localL]
    congr 1
    congr 1
    field_simp
  rw [algebraGenerating,he,ringInverse_smul h,smul_smul]
  rfl

theorem algebraGenerating_coefficient {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (A : 𝔄) (k : ℕ) :
    taylorCoeff (algebraGenerating c g A) k = Polynomial.aeval A (faberBasis c g k) := by
  classical
  let L := localL c g
  let W := localW c g
  let N := localN c g
  let V := fun u => Ring.inverse (1-W u • A)
  have hL : AnalyticAt ℂ L 0 := analyticAt_localL hc hg
  have hW : AnalyticAt ℂ W 0 := analyticAt_localW hc hg
  have hN : AnalyticAt ℂ N 0 := analyticAt_localN hc hg
  have hd : AnalyticAt ℂ (fun u => (1:𝔄)-W u • A) 0 :=
    analyticAt_const.sub (hW.smul analyticAt_const)
  have hunit : IsUnit ((1:𝔄)-W 0 • A) := by simp [W]
  have hV : AnalyticAt ℂ V 0 := (analyticAt_ringInverse hunit).comp (f := fun u => (1:𝔄)-W u • A) hd
  have hlocal : ∀ᶠ u in 𝓝 0, c+u*g u ≠ 0 :=
    (analyticAt_const.add (analyticAt_id.mul hg)).continuousAt.eventually_ne (by simpa using hc)
  have hu : ∀ᶠ u in 𝓝 0, IsUnit ((1:𝔄)-W u • A) :=
    hd.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hunit)
  let T := fun u => (N u*L u^(k+1)) • (A^(k+1)*V u)
  have hT : AnalyticAt ℂ T 0 := (hN.mul (hL.pow (k+1))).smul (analyticAt_const.mul hV)
  have hs : AnalyticAt ℂ (fun u => ∑ j ∈ Finset.range (k+1), (N u*W u^j) • A^j) 0 :=
    Finset.analyticAt_fun_sum _ (fun j _ => (hN.mul (hW.pow j)).smul analyticAt_const)
  have he : algebraGenerating c g A =ᶠ[𝓝 0]
      (fun u => (∑ j ∈ Finset.range (k+1), (N u*W u^j) • A^j) + u^(k+1) • T u) := by
    filter_upwards [hlocal,hu] with u hlu huu
    rw [algebraGenerating_local A hlu,ringInverse_geometric (W u • A) huu k]
    simp only [smul_add,Finset.smul_sum,smul_pow,smul_smul,smul_mul_assoc]
    congr 1
    change (N u * W u^(k+1)) • (A^(k+1)*V u) =
      u^(k+1) • ((N u*L u^(k+1)) • (A^(k+1)*V u))
    rw [smul_smul]
    congr 1
    change N u * (u*L u)^(k+1) = _
    rw [mul_pow]
    ring
  have htail : AnalyticAt ℂ (fun u => u^(k+1) • T u) 0 := (analyticAt_id.pow (k+1)).smul hT
  rw [taylorCoeff_congr he k,taylorCoeff_add hs htail,
    taylorCoeff_pow_smul_zero hT (by omega : k < k+1),add_zero,taylorCoeff_sum]
  · simp only [faberBasis,map_sum,Polynomial.aeval_monomial,← Algebra.smul_def]
    apply Finset.sum_congr rfl
    intro j hj
    exact taylorCoeff_smul_const (hN.mul (hW.pow j)) (A^j) k
  · exact fun j _ => (hN.mul (hW.pow j)).smul analyticAt_const

theorem algebraGenerating_fourier {R : ℝ} (hR : 1 < R) {c : ℂ} (hc : c ≠ 0)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (ball 0 R)) (A : 𝔄)
    (hunit : ∀ u ∈ closedBall 0 1, IsUnit (algebraDenominator c g A u)) :
    (Continuous (fun t : Angle => algebraGenerating c g A (unitPoint t)⁻¹)) ∧
    (∀ k : ℕ, fourierCoeff (fun t : Angle => algebraGenerating c g A (unitPoint t)⁻¹)
      (-(k:ℤ)) = Polynomial.aeval A (faberBasis c g k)) ∧
    (∀ k : ℤ, 0 < k → fourierCoeff (fun t : Angle => algebraGenerating c g A (unitPoint t)⁻¹) k = 0) := by
  have ha : AnalyticOnNhd ℂ (algebraGenerating c g A) (closedBall 0 1) := by
    intro u hu
    exact analyticAt_algebraGenerating (hg u (closedBall_subset_ball hR hu)) A (hunit u hu)
  obtain ⟨δ,hδ,hsub⟩ := (isCompact_closedBall (0:ℂ) 1).exists_thickening_subset_open
    (isOpen_analyticAt ℂ (algebraGenerating c g A)) ha
  rw [thickening_closedBall hδ (by norm_num : (0:ℝ) ≤ 1)] at hsub
  have hδ1 : 1 < δ+1 := by linarith
  have hsub : AnalyticOnNhd ℂ (algebraGenerating c g A) (ball 0 (δ+1)) := hsub
  have he (k : ℤ) := fourierCoeff_of_antianalytic hδ1 hsub k
  refine ⟨?_,?_,?_⟩
  · exact hsub.continuousOn.comp_continuous (unitPoint_continuous.inv₀ unitPoint_ne_zero)
      (fun t => unitPoint_inv_mem hδ1 t)
  · intro k
    rw [he,ite_eq_left (by omega : -(k:ℤ) ≤ 0)]
    simp only [neg_neg,Int.toNat_natCast]
    exact algebraGenerating_coefficient hc (hg 0 (mem_ball_self (by linarith))) A k
  · intro k hk
    rw [he,ite_eq_right (by omega : ¬k ≤ 0)]

theorem algebraDenominator_exterior {𝔄 : Type u_129} [NormedRing 𝔄]
    [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]
    (c : ℂ) (g : ℂ → ℂ) (A : 𝔄) {u : ℂ} (hu : u ≠ 0) :
    algebraDenominator c g A u = u • (exterior c g u⁻¹ • 1 - A) := by
  simp only [algebraDenominator,exterior,inv_inv,smul_sub,smul_smul]
  congr 1
  congr 1
  field_simp

theorem algebraGenerating_exterior (c : ℂ) (g : ℂ → ℂ) (A : 𝔄) {ζ : ℂ} (hζ : ζ ≠ 0) :
    algebraGenerating c g A ζ⁻¹ = (ζ*(c-ζ⁻¹^2*deriv g ζ⁻¹)) •
      Ring.inverse (exterior c g ζ • 1 - A) := by
  rw [algebraGenerating,algebraDenominator_exterior c g A (inv_ne_zero hζ),inv_inv,
    ringInverse_smul (inv_ne_zero hζ),inv_inv,smul_smul,mul_comm]

end BanachAlgebra

end DirectCrouzeix.Faber

namespace DirectCrouzeix

open MeasureTheory Set Filter Metric

open scoped Topology ComplexConjugate MatrixOrder ComplexOrder

end DirectCrouzeix

end

end

end OAI
