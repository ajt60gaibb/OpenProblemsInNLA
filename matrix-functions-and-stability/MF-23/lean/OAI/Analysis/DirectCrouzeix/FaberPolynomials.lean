import OAI.Analysis.DirectCrouzeix.TaylorFourier

namespace OAI

universe u_106 u_107

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

def localL (c : ℂ) (g : ℂ → ℂ) (u : ℂ) : ℂ := (c+u*g u)⁻¹

def localW (c : ℂ) (g : ℂ → ℂ) (u : ℂ) : ℂ := u*localL c g u

def localN (c : ℂ) (g : ℂ → ℂ) (u : ℂ) : ℂ := (c-u^2*deriv g u)*localL c g u

def faberBasis (c : ℂ) (g : ℂ → ℂ) (k : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (k+1), Polynomial.monomial j
    (taylorCoeff (fun u => localN c g u * localW c g u ^ j) k)

theorem analyticAt_localL {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (localL c g) 0 := by
  apply (analyticAt_const.add (analyticAt_id.mul hg)).inv
  simpa using hc

theorem analyticAt_localW {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (localW c g) 0 := analyticAt_id.mul (analyticAt_localL hc hg)

theorem analyticAt_localN {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (localN c g) 0 :=
  (analyticAt_const.sub ((analyticAt_id.pow 2).mul hg.deriv)).mul (analyticAt_localL hc hg)

@[simp] theorem localL_zero (c : ℂ) (g : ℂ → ℂ) : localL c g 0 = c⁻¹ := by simp [localL]

@[simp] theorem localW_zero (c : ℂ) (g : ℂ → ℂ) : localW c g 0 = 0 := by simp [localW]

@[simp] theorem localN_zero {c : ℂ} (hc : c ≠ 0) (g : ℂ → ℂ) : localN c g 0 = 1 := by
  simp [localN,localL,hc]

theorem faberBasis_coeff (c : ℂ) (g : ℂ → ℂ) (k j : ℕ) :
    (faberBasis c g k).coeff j =
      if j ≤ k then taylorCoeff (fun u => localN c g u * localW c g u^j) k else 0 := by
  classical
  simp [faberBasis,Polynomial.coeff_monomial,Finset.sum_ite_eq']

theorem faberBasis_zero {c : ℂ} (hc : c ≠ 0) (g : ℂ → ℂ) : faberBasis c g 0 = 1 := by
  simp [faberBasis,hc]

theorem faberBasis_top_coeff {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    (faberBasis c g k).coeff k = c⁻¹ ^ k := by
  rw [faberBasis_coeff, ite_eq_left le_rfl]
  have he : (fun u => localN c g u * localW c g u^k) =
      (fun u => u^k*(localN c g u*localL c g u^k)) := by funext u; simp only [localW,mul_pow]; ring
  rw [he,taylorCoeff_pow_mul (f := fun u => localN c g u*localL c g u^k)
    ((analyticAt_localN hc hg).mul ((analyticAt_localL hc hg).pow k))]
  simp [hc]

theorem faberBasis_degree {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    (faberBasis c g k).degree = k := by
  have hn : (faberBasis c g k).coeff k ≠ 0 := by rw [faberBasis_top_coeff hc hg]; exact pow_ne_zero _ (inv_ne_zero hc)
  apply (Polynomial.degree_eq_iff_natDegree_eq (fun h => by simp [h] at hn)).mpr
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero _ hn
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [faberBasis_coeff,ite_eq_right (by omega)]

theorem faberBasis_eval (c : ℂ) (g : ℂ → ℂ) (k : ℕ) (z : ℂ) :
    (faberBasis c g k).eval z = ∑ j ∈ Finset.range (k+1),
      taylorCoeff (fun u => localN c g u * localW c g u^j) k * z^j := by
  simp [faberBasis,Polynomial.eval_finsetSum,Polynomial.eval_monomial]

def scalarGenerating (c : ℂ) (g : ℂ → ℂ) (z u : ℂ) : ℂ :=
  (c-u^2*deriv g u)/(c+u*(g u-z))

theorem analyticAt_scalarGenerating {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (z : ℂ) : AnalyticAt ℂ (scalarGenerating c g z) 0 := by
  apply (analyticAt_const.sub ((analyticAt_id.pow 2).mul hg.deriv)).div
    (analyticAt_const.add (analyticAt_id.mul (hg.sub analyticAt_const)))
  simpa using hc

theorem scalarGenerating_eq_local {c : ℂ} {g : ℂ → ℂ} {z u : ℂ}
    (hu : c+u*g u ≠ 0) : scalarGenerating c g z u = localN c g u/(1-z*localW c g u) := by
  simp only [scalarGenerating,localN,localW,localL]
  field_simp
  congr 1 ; ring

theorem scalarGenerating_coefficient {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (z : ℂ) (k : ℕ) :
    taylorCoeff (scalarGenerating c g z) k = (faberBasis c g k).eval z := by
  let N := localN c g
  let L := localL c g
  let W := localW c g
  have hN : AnalyticAt ℂ N 0 := analyticAt_localN hc hg
  have hL : AnalyticAt ℂ L 0 := analyticAt_localL hc hg
  have hW : AnalyticAt ℂ W 0 := analyticAt_localW hc hg
  let tail := fun u => N u*z^(k+1)*L u^(k+1)/(1-z*W u)
  have ht : AnalyticAt ℂ tail 0 := by
    apply ((hN.mul analyticAt_const).mul (hL.pow (k+1))).div
      (analyticAt_const.sub (analyticAt_const.mul hW))
    simp [W]
  have hsmall : ∀ᶠ u in 𝓝 (0:ℂ), c+u*g u ≠ 0 ∧ 1-z*W u ≠ 0 := by
    apply Filter.Eventually.and
    · exact (analyticAt_const.add (analyticAt_id.mul hg)).continuousAt.eventually_ne (by simpa using hc)
    · exact (analyticAt_const.sub (analyticAt_const.mul hW)).continuousAt.eventually_ne (by simp [W])
  have he : scalarGenerating c g z =ᶠ[𝓝 0]
      (fun u => (∑ j ∈ Finset.range (k+1), (N u*W u^j)*z^j) + u^(k+1)*tail u) := by
    filter_upwards [hsmall] with u hu
    rw [scalarGenerating_eq_local hu.1]
    have hsum := geom_sum_mul_neg (z*W u) (k+1)
    have hre : ∑ j ∈ Finset.range (k+1), N u * W u^j*z^j =
        N u * ∑ j ∈ Finset.range (k+1), (z*W u)^j := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; rw [mul_pow]; ring
    rw [hre]
    change N u / (1-z*W u) = _
    simp only [tail]
    field_simp [hu.2]
    have hw : W u = u*L u := rfl
    rw [hw] at hsum ⊢
    linear_combination -N u*hsum
  have hs : AnalyticAt ℂ (fun u => ∑ j ∈ Finset.range (k+1), N u*W u^j*z^j) 0 :=
    Finset.analyticAt_fun_sum _ (fun j hj => (hN.mul (hW.pow j)).mul analyticAt_const)
  have htail : AnalyticAt ℂ (fun u => u^(k+1)*tail u) 0 := (analyticAt_id.pow (k+1)).mul ht
  rw [taylorCoeff_congr he k,taylorCoeff_add hs htail,taylorCoeff_pow_mul ht,
    ite_eq_right (by omega : ¬k+1 ≤ k),add_zero,taylorCoeff_sum]
  · rw [faberBasis_eval]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [taylorCoeff,iteratedDeriv_mul_const_field,smul_eq_mul]
    ring
  · intro j hj
    exact (hN.mul (hW.pow j)).mul analyticAt_const

theorem taylorCoeff_geometric (z : ℂ) (k : ℕ) :
    taylorCoeff (fun u : ℂ => (1-z*u)⁻¹) k = z^k := by
  have he : (fun u : ℂ => (1-z*u)⁻¹) = scalarGenerating 1 (fun _ => 0) z := by
    funext u
    simp [scalarGenerating,sub_eq_add_neg,mul_comm]
  rw [he,scalarGenerating_coefficient (by norm_num) analyticAt_const,faberBasis_eval]
  have he' (j : ℕ) : (fun u => localN 1 (fun _ => 0) u * localW 1 (fun _ => 0) u^j) =
      (fun u : ℂ => u^j) := by funext u; simp [localN,localW,localL]
  simp_rw [he']
  have hfac : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  simp only [taylorCoeff,iteratedDeriv_fun_pow_zero,smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp [hfac]
  · intro j hj hjk
    simp [Ne.symm hjk]
  · simp

theorem faberBasis_exterior {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    {v : ℂ} (hv : v ∈ ball 0 R) (hv0 : v ≠ 0)
    (hH : ∀ u ∈ ball 0 R, chordDenominator c g u v ≠ 0) (k : ℕ) :
    (faberBasis c g k).eval (exterior c g v⁻¹) = v⁻¹^k +
      taylorCoeff (fun u => correction c g u v) k := by
  have h0 : (0:ℂ) ∈ ball 0 R := mem_ball_self hR
  have hgen := analyticAt_scalarGenerating hc (hg 0 h0) (exterior c g v⁻¹)
  have hcorr := analyticOnNhd_correction_left isOpen_ball (convex_ball 0 R) hg hv hH
  have hgeom : AnalyticAt ℂ (fun u : ℂ => (1-v⁻¹*u)⁻¹) 0 := by
    exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).inv (by simp)
  have he : scalarGenerating c g (exterior c g v⁻¹) =ᶠ[𝓝 0]
      (fun u => (1-v⁻¹*u)⁻¹+correction c g u v) := by
    filter_upwards [isOpen_ball.mem_nhds h0, (isOpen_ne.mem_nhds (Ne.symm hv0))] with u hu huv
    have hh := correction_identity isOpen_ball (convex_ball 0 R) hg c hu hv hv0 huv (hH u hu)
    change correction c g u v = scalarGenerating c g (exterior c g v⁻¹) u - _ at hh
    rw [div_eq_mul_inv,mul_comm] at hh
    linear_combination -hh
  rw [← scalarGenerating_coefficient hc (hg 0 h0),taylorCoeff_congr he,
    taylorCoeff_add hgeom (hcorr 0 h0),taylorCoeff_geometric]

@[simp] theorem unitPoint_neg (t : Angle) : unitPoint (-t) = (unitPoint t)⁻¹ := by
  simp [unitPoint,fourier_apply,AddCircle.toCircle_neg,Circle.coe_inv]

theorem fourierCoeff_comp_neg {E : Type u_106} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Angle → E) (k : ℤ) :
    fourierCoeff (fun t => f (-t)) k = fourierCoeff f (-k) := by
  unfold fourierCoeff
  rw [← integral_neg_eq_self (fun t : Angle => fourier (-k) t • f (-t)) angularMeasure]
  congr 1
  funext t
  simp [fourier_apply,smul_neg,neg_smul]

theorem fourierCoeff_of_antianalytic {E : Type u_107} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {R : ℝ} (hR : 1 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (k : ℤ) :
    fourierCoeff (fun t : Angle => f ((unitPoint t)⁻¹)) k =
      if k ≤ 0 then taylorCoeff f (-k).toNat else 0 := by
  have he : (fun t : Angle => f ((unitPoint t)⁻¹)) = (fun t => (fun s => f (unitPoint s)) (-t)) := by
    funext t; change f ((unitPoint t)⁻¹) = f (unitPoint (-t)); rw [unitPoint_neg]
  rw [he,fourierCoeff_comp_neg (fun t : Angle => f (unitPoint t)) k,fourierCoeff_of_analytic hR hf]
  simp only [neg_nonneg]

end DirectCrouzeix.Faber

end

end

end OAI
