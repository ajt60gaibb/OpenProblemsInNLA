import NLA.IE06.GaussianRegression
import NLA.IE06.GaussianFrobenius
import NLA.IE06.Spectral
import NLA.IE06.FiniteNet
import NLA.IE06.GaussianConcentrationSpace

/-! Gaussian operator estimates from a finite net. Exact contracts and
independent approval are in the spectral concentration alternative review. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp Real
open scoped BigOperators RealInnerProductSpace ENNReal NNReal Matrix.Norms.L2Operator
namespace NLA.IE06.GaussianOperatorNet
open GaussianNull GaussianQuadratic GaussianRegression GaussianFrobenius Spectral

theorem unit_inner_gaussian {m : ℕ} (y : E m) (hy : ‖y‖=1) :
    MeasurePreserving (fun z : Fin m → ℝ => ⟪y,toLp 2 z⟫)
      (gaussianVector m) (gaussianReal 0 1) := by
  have hm : (stdGaussian (E m)).map (innerSL ℝ y) = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, innerSL_apply_norm, hy]
    norm_num
  exact (show MeasurePreserving (innerSL ℝ y) (stdGaussian (E m)) (gaussianReal 0 1)
    from ⟨by fun_prop,hm⟩).comp ⟨by fun_prop,map_pi_eq_stdGaussian⟩

def unitProjection {m n : ℕ} (y : E m) (G : RectMat m n) : Fin n → ℝ :=
  fun j => ⟪y,toLp 2 (fun i => G i j)⟫

theorem unitProjection_gaussian {m n : ℕ} (y : E m) (hy : ‖y‖=1) :
    MeasurePreserving (unitProjection (n := n) y) (gaussianRect m n) (gaussianVector n) := by
  have hm := measurePreserving_pi (fun _ : Fin n => gaussianVector m)
    (fun _ : Fin n => gaussianReal 0 1) (fun _ => unit_inner_gaussian y hy)
  exact hm.comp ⟨by fun_prop,gaussian_transpose m n⟩

theorem unitProjection_eq_vecMul {m n : ℕ} (y : E m) (G : RectMat m n) :
    unitProjection y G = ofLp y ᵥ* Matrix.of G := by
  funext j
  simp [unitProjection, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.vecMul,
    mul_comm]

theorem unitProjection_row_tail {m n p : ℕ}
    (M : Matrix (Fin n) (Fin p) ℝ) (y : E m) (hy : ‖y‖=1) (x : ℝ) (hx : 0<x) :
    gaussianRect m n {G | 2*frobeniusSq M+4*x*opNorm M^2 <
      ∑ j, (ofLp y ᵥ* (Matrix.of G*M)) j^2} ≤ ENNReal.ofReal (exp (-x)) := by
  have hm : MeasurePreserving (fun G : RectMat m n => fun _ : Fin 1 => unitProjection y G)
      (gaussianRect m n) (gaussianRect 1 n) :=
    (measurePreserving_funUnique (gaussianVector n) (Fin 1)).symm.comp
      (unitProjection_gaussian (n := n) y hy)
  let event : Set (RectMat 1 n) := {G | 2*(1:ℝ)*frobeniusSq M+4*x*euclideanOpNorm M^2 <
      frobeniusSq (Matrix.of G*M)}
  have he : MeasurableSet event := by
    dsimp only [event]
    apply measurableSet_lt measurable_const
    exact (show Continuous (fun G : RectMat 1 n => frobeniusSq (Matrix.of G*M)) by
      unfold frobeniusSq
      fun_prop).measurable
  have h : gaussianRect 1 n event ≤ ENNReal.ofReal (exp (-x)) := by
    simpa only [Nat.cast_one] using centered_gaussian_frobenius_tail (m := 1) M x hx
  have h' := (hm.measure_preimage he.nullMeasurableSet).le.trans h
  have hs : {G : RectMat m n | 2*frobeniusSq M+4*x*opNorm M^2 <
      ∑ j, (ofLp y ᵥ* (Matrix.of G*M)) j^2} =
      (fun G : RectMat m n => fun _ : Fin 1 => unitProjection y G) ⁻¹' event := by
    ext G
    change _ ↔ 2*1*frobeniusSq M+4*x*euclideanOpNorm M^2 <
      ∑ i : Fin 1, ∑ j, ((Matrix.of (fun _ : Fin 1 => unitProjection y G))*M) i j^2
    simp only [Fin.sum_univ_one, mul_one]
    rw [unitProjection_eq_vecMul]
    change _ ↔ 2*frobeniusSq M+4*x*euclideanOpNorm M^2 <
      ∑ j, ((ofLp y ᵥ* Matrix.of G) ᵥ* M) j^2
    rw [Matrix.vecMul_vecMul]
    rfl
  rw [hs]
  exact h'

theorem norm_adjoint_eq_row_energy {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) ℝ) (y : E m) :
    ‖(euclideanMap A).adjoint y‖^2 = ∑ j, (ofLp y ᵥ* A) j^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [euclideanMap, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp [Matrix.mulVec, Matrix.vecMul, dotProduct_comm]

theorem operator_net_tail {m n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ)
    (x : ℝ) (hx : 0<x) :
    gaussianRect m n {G | 2*sqrt (2*frobeniusSq M+4*x*opNorm M^2) <
      opNorm (Matrix.of G*M)} ≤ ENNReal.ofReal ((5:ℝ)^m*exp (-x)) := by
  classical
  obtain ⟨T,hT,hcard,hcover⟩ := FiniteNet.exists_half_net
    {y : E m | ‖y‖=1} (fun y hy => hy.le)
  let B := sqrt (2*frobeniusSq M+4*x*opNorm M^2)
  have hBn : 0≤B := sqrt_nonneg _
  have hBsq : B^2=2*frobeniusSq M+4*x*opNorm M^2 := by
    apply sq_sqrt
    have hF : 0≤frobeniusSq M := by unfold frobeniusSq; positivity
    positivity
  let bad (y : E m) : Set (RectMat m n) :=
    {G | 2*frobeniusSq M+4*x*opNorm M^2 < ∑ j, (ofLp y ᵥ* (Matrix.of G*M)) j^2}
  have hsub : {G : RectMat m n | 2*B < opNorm (Matrix.of G*M)} ⊆ ⋃ y∈T, bad y := by
    intro G hG
    by_contra! hnone
    have hpoint : ∀ y∈T, ‖(euclideanMap ((Matrix.of G*M)ᴴ)).toContinuousLinearMap y‖ ≤ B := by
      intro y hy
      have hh : ¬G∈bad y := by
        intro hb
        exact hnone (Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr ⟨hy,hb⟩⟩)
      have he : ‖(euclideanMap ((Matrix.of G*M)ᴴ)).toContinuousLinearMap y‖^2 ≤ B^2 := by
        rw [hBsq]
        change ‖(euclideanMap ((Matrix.of G*M)ᴴ)) y‖^2 ≤ _
        rw [euclideanMap, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
        rw [← euclideanMap, norm_adjoint_eq_row_energy]
        exact le_of_not_gt hh
      nlinarith [norm_nonneg ((euclideanMap ((Matrix.of G*M)ᴴ)).toContinuousLinearMap y)]
    have hb := FiniteNet.opNorm_le_twice (euclideanMap ((Matrix.of G*M)ᴴ)).toContinuousLinearMap
      T (fun y hy => hcover y hy) hBn hpoint
    change opNorm ((Matrix.of G*M)ᴴ) ≤ 2*B at hb
    rw [opNorm_eq_l2, Matrix.l2_opNorm_conjTranspose, ← opNorm_eq_l2] at hb
    exact (not_lt_of_ge hb) hG
  calc
    _ ≤ gaussianRect m n (⋃ y∈T, bad y) := measure_mono hsub
    _ ≤ ∑ y∈T, gaussianRect m n (bad y) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y∈T, ENNReal.ofReal (exp (-x)) := by
      apply Finset.sum_le_sum
      intro y hy
      exact unitProjection_row_tail M y (hT hy) x hx
    _ = (T.card:ℝ≥0∞)*ENNReal.ofReal (exp (-x)) := by simp
    _ ≤ (5:ℝ≥0∞)^m*ENNReal.ofReal (exp (-x)) := by
      gcongr
      simpa using (show (T.card:ℝ≥0∞)≤(5^Module.finrank ℝ (E m):ℕ) by exact_mod_cast hcard)
    _ = _ := by rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]; norm_num

theorem operator_net_tail_shift {m n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ)
    (u : ℝ) (hu : 0<u) :
    gaussianRect m n {G | 2*sqrt (2*frobeniusSq M+4*((m:ℝ)*log 5+u)*opNorm M^2) <
      opNorm (Matrix.of G*M)} ≤ ENNReal.ofReal (exp (-u)) := by
  have hx : 0<(m:ℝ)*log 5+u := by
    have hl : 0≤log (5:ℝ) := log_nonneg (by norm_num)
    positivity
  have h := operator_net_tail (m := m) M ((m:ℝ)*log 5+u) hx
  have he : (5:ℝ)^m*exp (-((m:ℝ)*log 5+u)) = exp (-u) := by
    have hpow : (5:ℝ)^m = exp ((m:ℝ)*log 5) := by rw [exp_nat_mul, exp_log (by norm_num)]
    rw [hpow, ← exp_add]
    congr 1
    ring
  rwa [he] at h

#assert_trust kernel unit_inner_gaussian
#assert_trust kernel unitProjection_gaussian
#assert_trust kernel unitProjection_eq_vecMul
#assert_trust kernel unitProjection_row_tail
#assert_trust kernel norm_adjoint_eq_row_energy
#assert_trust kernel operator_net_tail
#assert_trust kernel operator_net_tail_shift
#print axioms unit_inner_gaussian
#print axioms unitProjection_gaussian
#print axioms operator_net_tail_shift

end NLA.IE06.GaussianOperatorNet
