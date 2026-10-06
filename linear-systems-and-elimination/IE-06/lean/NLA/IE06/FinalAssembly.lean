import NLA.IE06.GaussianAllRows
import NLA.IE06.GaussianSpectralRecursion
import NLA.IE06.FinalGrowthScalars
import NLA.IE06.FinalFailureScalars
import NLA.IE06.Reduction

/-! Exact final assembly of the reviewed estimates. The reusable implication
exposes its B5 input; the unconditional module supplies the actual theorem. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped ENNReal Topology
namespace NLA.IE06.FinalAssembly

/-- The full simultaneous retained-inverse estimate, with constants independent
of dimension. This is a proposition interface, not an assumed axiom. -/
def InverseTailEstimate : Prop :=
  ∀ β : ℝ, 1 ≤ β → ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 256 ≤ Real.log (n:ℝ) →
    gaussianMatrix n (GaussianSpectralRecursion.inverseBad n ⌈Real.sqrt (Real.log (n:ℝ))⌉₊ D) ≤
      ENNReal.ofReal (Real.exp (-(β-2)*Real.log (n:ℝ)))

theorem schur_tail_of_inverse_estimate (hB5 : InverseTailEstimate) : SchurSubpolynomialTail := by
  intro α hα
  obtain ⟨D,hD,hB⟩ := hB5 (α+4) (by linarith)
  let a := α+6
  have ha : 1 ≤ a := by dsimp [a]; linarith
  let C := FinalGrowthScalars.constant D a
  have hC : 0 < C := FinalGrowthScalars.constant_pos hD ha
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htail : ∀ᶠ n : ℕ in atTop,
      gaussianMatrix n (exceedanceEvent n (Real.sqrt (n:ℝ)*Real.exp (C*Real.sqrt (Real.log (n:ℝ))))) <
        ENNReal.ofReal ((n:ℝ)^(-α)) := by
    filter_upwards [hlog.eventually_ge_atTop 256,FinalFailureScalars.failure_budget_eventually α hα]
      with n hn hfail
    let r := ⌈Real.sqrt (Real.log (n:ℝ))⌉₊
    let x := a*Real.log (n:ℝ)
    let τ := (2*(n:ℝ)/(r:ℝ))*Real.exp (12*D*Real.sqrt (Real.log (n:ℝ)))
    have hr : 1 ≤ r := (by norm_num : 1 ≤ 16).trans (SpectralRecursionScalars.sixteen_le_ceil_sqrt hn)
    have hx : 0 < x := mul_pos (by linarith) (by linarith)
    have hτ : 0 ≤ τ := by dsimp [τ]; positivity
    have hrows := GaussianAllRows.growth_tail (n:=n) hr hτ hx
    have hI : gaussianMatrix n (GaussianAllRows.inverseBad n r τ) ≤
        ENNReal.ofReal (Real.exp (-((α+4)-2)*Real.log (n:ℝ))) := by
      apply (measure_mono ?_).trans (hB n hn)
      rintro A ⟨t,ht,hs⟩
      exact ⟨t,ht,r,le_rfl,hs⟩
    have hK : Real.sqrt (2*x*(GaussianAllRows.rowBound r τ x)^2) ≤
        Real.sqrt (n:ℝ)*Real.exp (C*Real.sqrt (Real.log (n:ℝ))) := by
      exact FinalGrowthScalars.log_absorption hD ha (by linarith)
    have hevent : exceedanceEvent n (Real.sqrt (n:ℝ)*Real.exp (C*Real.sqrt (Real.log (n:ℝ)))) ⊆
        exceedanceEvent n (Real.sqrt (2*x*(GaussianAllRows.rowBound r τ x)^2)) := by
      intro A hA
      obtain ⟨hdim,hdet,p,hp,hg⟩ := hA
      exact ⟨hdim,hdet,p,hp,hK.trans_lt hg⟩
    apply ((measure_mono hevent).trans hrows).trans_lt
    apply lt_of_le_of_lt (add_le_add (add_le_add hI le_rfl) le_rfl)
    simpa only [x,a,neg_mul] using hfail
  obtain ⟨N,hN⟩ := eventually_atTop.mp htail
  refine ⟨C,hC,max N 2,le_max_right _ _,?_⟩
  intro n hn
  exact hN n ((le_max_left _ _).trans hn)

#assert_trust kernel InverseTailEstimate
#assert_trust kernel schur_tail_of_inverse_estimate
#print axioms schur_tail_of_inverse_estimate
end NLA.IE06.FinalAssembly
