import NLA.Proofs.TR06.ModelOuterDerivative
import NLA.TR06.RankOneCharts
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Intrinsic rank-one tangents are actual pivot-decoder derivatives. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.Model
open scoped BigOperators Topology
open Filter
variable {d : ℕ} {n : Fin d → ℕ}

/-- Absorb the actual pivot amplitude into one genuine tensor factor. -/
def pivotFactorMap (q : NLA.TR06.TensorIndex d n) (j₀ : Fin d)
    (p : NLA.TR06.PivotData q) : FactorSpace d n :=
  Function.update (NLA.TR06.expandedPivotFactors q p.2) j₀
    (fun k => p.1 * NLA.TR06.expandedPivotFactors q p.2 j₀ k)

theorem pureTensor_pivotFactorMap (q : NLA.TR06.TensorIndex d n) (j₀ : Fin d)
    (p : NLA.TR06.PivotData q) :
    NLA.TR06.pureTensor (pivotFactorMap q j₀ p) = NLA.TR06.tensorFromPivotData q p :=
  NLA.TR06.pureTensor_smul_factor _ j₀ p.1

theorem contDiff_pivotFactorMap (q : NLA.TR06.TensorIndex d n) (j₀ : Fin d) :
    ContDiff ℝ 1 (pivotFactorMap q j₀) := by
  apply contDiff_pi.mpr
  intro j
  apply contDiff_pi.mpr
  intro k
  by_cases hj : j=j₀
  · subst j
    simp only [pivotFactorMap,Function.update_self]
    unfold NLA.TR06.expandedPivotFactors
    split_ifs <;> fun_prop
  · simp only [pivotFactorMap,Function.update_of_ne hj]
    unfold NLA.TR06.expandedPivotFactors
    split_ifs <;> fun_prop

theorem rankOneTangent_decoder (q : NLA.TR06.TensorIndex d n) (j₀ : Fin d)
    (p w : NLA.TR06.PivotData q) :
    NLA.Statements.TR06.RankOneTangent (NLA.TR06.tensorFromPivotData q p)
      (fderiv ℝ (NLA.TR06.tensorFromPivotData q) p w) := by
  have hmap := (contDiff_pivotFactorMap q j₀).differentiable one_ne_zero
  have h := (hasFDerivAt_pureTensor (pivotFactorMap q j₀ p)).comp p (hmap p).hasFDerivAt
  have heq : NLA.TR06.pureTensor ∘ pivotFactorMap q j₀ = NLA.TR06.tensorFromPivotData q :=
    funext (pureTensor_pivotFactorMap q j₀)
  rw [heq] at h
  refine ⟨pivotFactorMap q j₀ p,fderiv ℝ (pivotFactorMap q j₀) p w,
    (pureTensor_pivotFactorMap q j₀ p).symm,?_⟩
  rw [h.fderiv]
  exact outerDerivative_apply _ _

/-- Every intrinsic variation comes from differentiating the actual pivot
coordinates. No tangent-range or smoothness oracle is an assumption. -/
theorem rankOneTangent_has_pivot_preimage
    (q : NLA.TR06.TensorIndex d n) (A v : NLA.TR06.Tensor ℝ d n)
    (hq : A q ≠ 0) (hv : NLA.Statements.TR06.RankOneTangent A v) :
    ∃ w : NLA.TR06.PivotData q,
      fderiv ℝ (NLA.TR06.tensorFromPivotData q) (NLA.TR06.tensorToPivotData q A) w = v := by
  obtain ⟨a,b,ha,hv⟩ := hv
  let line := fun t : ℝ => a+t • b
  let γ := fun t : ℝ => NLA.TR06.pureTensor (line t)
  have hline : HasDerivAt line b 0 := by
    simpa [line] using ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a
  have hγ : HasDerivAt γ v 0 := by
    have hbase : HasFDerivAt NLA.TR06.pureTensor (outerDerivative a) (line 0) := by
      simpa only [line,zero_smul,add_zero] using hasFDerivAt_pureTensor a
    have h := hbase.comp_hasDerivAt 0 hline
    convert! h using 1
    simp only [outerDerivative_apply,← hv]
  have hγ0 : γ 0 = A := by simp [γ,line,ha,NLA.Statements.TR06.Outer,NLA.TR06.pureTensor]
  have hp : ∀ᶠ t : ℝ in 𝓝 0, γ t q ≠ 0 :=
    ((PiLp.continuous_apply 2 _ q).continuousAt.comp hγ.continuousAt).eventually_ne
      (by change γ 0 q ≠ 0; rwa [hγ0])
  have hopen : IsOpen {B : NLA.TR06.Tensor ℝ d n | B q ≠ 0} :=
    isOpen_ne_fun (PiLp.continuous_apply 2 _ q) continuous_const
  have he : DifferentiableAt ℝ (NLA.TR06.tensorToPivotData q) (γ 0) :=
    ((NLA.TR06.contDiffOn_tensorToPivotData q 1).contDiffAt
      (hopen.mem_nhds (by rwa [hγ0]))).differentiableAt one_ne_zero
  have hη := he.hasFDerivAt.comp_hasDerivAt 0 hγ
  have hd := ((NLA.TR06.contDiff_tensorFromPivotData q 1).differentiable one_ne_zero
    (NLA.TR06.tensorToPivotData q (γ 0))).hasFDerivAt.comp_hasDerivAt 0 hη
  have hlocal : (fun t => NLA.TR06.tensorFromPivotData q
      (NLA.TR06.tensorToPivotData q (γ t))) =ᶠ[𝓝 0] γ := by
    filter_upwards [hp] with t ht
    apply NLA.TR06.tensorFromPivotData_to q (γ t)
    · refine ⟨?_,line t,rfl⟩
      intro hz
      apply ht
      simp [hz]
    · exact ht
  have hactual := hd.congr_of_eventuallyEq hlocal.symm
  refine ⟨fderiv ℝ (NLA.TR06.tensorToPivotData q) A v,?_⟩
  simpa only [hγ0] using (hγ.unique hactual).symm

theorem rankOneTangent_iff_pivotRange
    (q : NLA.TR06.TensorIndex d n) (j₀ : Fin d) (A v : NLA.TR06.Tensor ℝ d n)
    (hA : NLA.TR06.RankOne A) (hq : A q ≠ 0) :
    NLA.Statements.TR06.RankOneTangent A v ↔
      ∃ w : NLA.TR06.PivotData q,
        fderiv ℝ (NLA.TR06.tensorFromPivotData q) (NLA.TR06.tensorToPivotData q A) w = v := by
  constructor
  · exact rankOneTangent_has_pivot_preimage q A v hq
  · rintro ⟨w,rfl⟩
    have h := rankOneTangent_decoder q j₀ (NLA.TR06.tensorToPivotData q A) w
    rwa [NLA.TR06.tensorFromPivotData_to q A hA hq] at h

#assert_trust kernel rankOneTangent_decoder
#assert_trust kernel rankOneTangent_has_pivot_preimage
#assert_trust kernel rankOneTangent_iff_pivotRange
#print axioms rankOneTangent_iff_pivotRange
end NLA.Proofs.TR06.Model
