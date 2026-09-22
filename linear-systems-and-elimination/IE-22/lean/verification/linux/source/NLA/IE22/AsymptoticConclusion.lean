import NLA.IE22.DeterministicSchedule
import NLA.IE22.SphericalRealization

/-!
Logical assembly of the quantitative upper bound, every-sequence limit and
sharpness. The intermediate upper-bound lemmas explicitly name their finite
certificate input; final selected wrappers must supply the proved certificate.
Original mathematical proof: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE22
open NLA.IE21

lemma universal_squared_rate_of_finite_bound (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (hfinite : ∀ (m n r : ℕ), 1 ≤ m → (1 ≤ r ∧ r < n) →
      ∀ δ : ℝ, (0 < δ ∧ δ < 1) → deterministicFailure θ n r δ < 1 →
      ∀ A : Mat m n, UnitRows A → normalizedDeletion θ A ≤ deterministicBound θ n r δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ m n : ℕ, 1 ≤ m → N ≤ n →
        (∀ A : Mat m n, UnitRows A →
          normalizedDeletion θ A ≤ gaussianTrim θ + C * errorSchedule n) ∧
        extremalValue θ m n ^ 2 ≤ gaussianTrim θ + C * errorSchedule n := by
  obtain ⟨hadm, _, C, hC, hbound⟩ := deterministic_schedule θ hθ
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hadm.and hbound)
  refine ⟨C,hC,max N 1,le_max_right _ _,?_⟩
  intro m n hm hn
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  obtain ⟨ha,hb⟩ := hN n ((le_max_left N 1).trans hn)
  have hall : ∀ A : Mat m n, UnitRows A →
      normalizedDeletion θ A ≤ gaussianTrim θ+C*errorSchedule n := by
    intro A hA
    have hf := hfinite m n (deletionSchedule n) hm ⟨ha.1,ha.2.1⟩
      (errorSchedule n) ⟨ha.2.2.1,ha.2.2.2.1⟩ ha.2.2.2.2 A hA
    linarith [hb.2]
  refine ⟨hall,?_⟩
  obtain ⟨A,hA,heq⟩ := (supremum_semantics θ hθ m n hm hn1).2.2.1
  rw [heq,(normalizedSingular_nonneg_sq θ hθ hn1 A).2]
  exact hall A hA

lemma uniform_upper_all_rows_of_rate (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (hrate : ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ m n : ℕ, 1 ≤ m → N ≤ n →
        (∀ A : Mat m n, UnitRows A →
          normalizedDeletion θ A ≤ gaussianTrim θ+C*errorSchedule n) ∧
        extremalValue θ m n^2 ≤ gaussianTrim θ+C*errorSchedule n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ m n : ℕ, 1 ≤ m → N ≤ n →
      extremalValue θ m n ≤ sharpConstant θ+ε := by
  obtain ⟨C,_,N,hN,hbound⟩ := hrate
  have herr : Tendsto (fun n => C*errorSchedule n) atTop (𝓝 0) := by
    simpa using errorSchedule_tendsto_zero.const_mul C
  obtain ⟨K,hK⟩ := eventually_atTop.mp (herr.eventually (gt_mem_nhds (sq_pos_of_pos hε)))
  refine ⟨max N K,hN.trans (le_max_left _ _),?_⟩
  intro m n hm hn
  have hb := (hbound m n hm ((le_max_left N K).trans hn)).2
  have he := hK n ((le_max_right N K).trans hn)
  have hc := constant_semantics θ hθ
  nlinarith [mul_nonneg hc.1 hε.le]

lemma high_aspect_supremum_limit_of_uniform_upper (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (hupper : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
      ∀ m n : ℕ, 1 ≤ m → N ≤ n → extremalValue θ m n ≤ sharpConstant θ+ε)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ)/n j) atTop atTop) :
    Tendsto (fun j => extremalValue θ (m j) (n j)) atTop (𝓝 (sharpConstant θ)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [high_aspect_near_extremizers θ hθ m n hm hn hnlim hQlim
      (sharpConstant θ-a) (sub_pos.mpr ha)] with j hj
    obtain ⟨A,hA,hnear⟩ := hj
    have hle := (supremum_semantics θ hθ (m j) (n j) (hm j) (hn j)).2.2.2.1 A hA
    linarith
  · intro b hb
    obtain ⟨N,_,hN⟩ := hupper ((b-sharpConstant θ)/2) (by linarith)
    filter_upwards [hnlim.eventually_ge_atTop N] with j hj
    have hle := hN (m j) (n j) (hm j) hj
    linarith

lemma no_smaller_uniform_constant (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (C : ℝ) (hC : C < sharpConstant θ) : ¬EventualUniformUpper θ C := by
  intro hupper
  let ε := (sharpConstant θ-C)/3
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨N,R,hNR⟩ := hupper ε hε
  let n : ℕ → ℕ := fun j => j+1
  let m : ℕ → ℕ := fun j => (j+1)*(j+1)
  have hn : ∀ j, 1 ≤ n j := by intro j; dsimp [n]; omega
  have hm : ∀ j, 1 ≤ m j := by intro j; dsimp [m]; nlinarith
  have hnlim : Tendsto n atTop atTop := by
    exact tendsto_add_atTop_nat 1
  have hratio (j : ℕ) : (m j : ℝ)/n j = (j : ℝ)+1 := by
    dsimp [m,n]
    push_cast
    field_simp
  have hQlim : Tendsto (fun j => (m j : ℝ)/n j) atTop atTop := by
    simp_rw [hratio]
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hevent := high_aspect_near_extremizers θ hθ m n hm hn hnlim hQlim ε hε
  obtain ⟨j,hj,hNj,hRj⟩ := (hevent.and ((hnlim.eventually_ge_atTop N).and
    (hQlim.eventually_ge_atTop R))).exists
  obtain ⟨A,hA,hnear⟩ := hj
  have hsup := (supremum_semantics θ hθ (m j) (n j) (hm j) (hn j)).2.2.2.1 A hA
  have hle := hNR (m j) (n j) (hm j) (hn j) hNj hRj
  dsimp [ε] at hnear hle
  linarith

end NLA.IE22
