import NLA.Proofs.TR06.ModelTangent

/-! Actual pivot derivative regularity agrees with the frozen intrinsic
addition-derivative regularity. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.Model
open scoped BigOperators Topology
open Filter
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem decoder_derivative_injective (q : NLA.TR06.TensorIndex d n)
    (p : NLA.TR06.PivotData q) (hp : p.1 ≠ 0) :
    Function.Injective (fderiv ℝ (NLA.TR06.tensorFromPivotData q) p) := by
  have hd := (NLA.TR06.contDiff_tensorFromPivotData q 1).differentiable one_ne_zero p
  have hq : NLA.TR06.tensorFromPivotData q p q ≠ 0 := by
    rwa [NLA.TR06.tensorFromPivotData_pivot]
  have hopen : IsOpen {A : NLA.TR06.Tensor ℝ d n | A q ≠ 0} :=
    isOpen_ne_fun (PiLp.continuous_apply 2 _ q) continuous_const
  have he := ((NLA.TR06.contDiffOn_tensorToPivotData q 1).contDiffAt
    (hopen.mem_nhds hq)).differentiableAt one_ne_zero
  have hlocal : (NLA.TR06.tensorToPivotData q ∘ NLA.TR06.tensorFromPivotData q) =ᶠ[𝓝 p] id := by
    filter_upwards [continuous_fst.continuousAt.eventually_ne hp] with z hz
    exact NLA.TR06.tensorToPivotData_from q z hz
  have hcomp := he.hasFDerivAt.comp p hd.hasFDerivAt
  have hidentity := (hasFDerivAt_id (𝕜 := ℝ) p).congr_of_eventuallyEq hlocal
  have hleft := hcomp.unique hidentity
  intro x y hxy
  have h := congrArg (fderiv ℝ (NLA.TR06.tensorToPivotData q)
    (NLA.TR06.tensorFromPivotData q p)) hxy
  change ((fderiv ℝ (NLA.TR06.tensorToPivotData q) (NLA.TR06.tensorFromPivotData q p)).comp
    (fderiv ℝ (NLA.TR06.tensorFromPivotData q) p)) x =
    ((fderiv ℝ (NLA.TR06.tensorToPivotData q) (NLA.TR06.tensorFromPivotData q p)).comp
      (fderiv ℝ (NLA.TR06.tensorFromPivotData q) p)) y at h
  rw [hleft] at h
  exact h

theorem fderiv_pivotSum_apply (q : Fin r → NLA.TR06.TensorIndex d n)
    (p w : NLA.TR06.OrderedPivotData q) :
    fderiv ℝ (NLA.TR06.pivotSum q) p w =
      ∑ i, fderiv ℝ (NLA.TR06.tensorFromPivotData (q i)) (p i) (w i) := by
  have h : HasFDerivAt (NLA.TR06.pivotSum q)
      (∑ i, (fderiv ℝ (NLA.TR06.tensorFromPivotData (q i)) (p i)).comp
        (ContinuousLinearMap.proj i)) p := by
    unfold NLA.TR06.pivotSum
    apply HasFDerivAt.fun_sum
    intro i _
    exact ((NLA.TR06.contDiff_tensorFromPivotData (q i) 1).differentiable
      one_ne_zero (p i)).hasFDerivAt.comp p (hasFDerivAt_apply (𝕜 := ℝ) i p)
  rw [h.fderiv]
  simp only [sum_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]

/-- A concrete full ordered pivot family supplies every intrinsic tangent
variation, and the actual decoder differentials are injective. -/
theorem regularDecomposition_decoder_iff (q : Fin r → NLA.TR06.TensorIndex d n)
    (j₀ : Fin d) (p : NLA.TR06.OrderedPivotData q) (hp : ∀ i, (p i).1 ≠ 0) :
    NLA.Statements.TR06.RegularDecomposition (NLA.TR06.orderedTensorFromPivotData q p) ↔
      Function.Injective (fderiv ℝ (NLA.TR06.pivotSum q) p) := by
  classical
  constructor
  · intro h x y hxy
    have hz : fderiv ℝ (NLA.TR06.pivotSum q) p (x-y) = 0 := by
      rw [map_sub,hxy,sub_self]
    have hzero := h (fun i => fderiv ℝ (NLA.TR06.tensorFromPivotData (q i)) (p i) ((x-y) i))
      (fun i => rankOneTangent_decoder (q i) j₀ (p i) ((x-y) i)) (by
        rw [← fderiv_pivotSum_apply]
        exact hz)
    apply sub_eq_zero.mp
    funext i
    apply decoder_derivative_injective (q i) (p i) (hp i)
    simpa only [map_zero,Pi.zero_apply] using hzero i
  · intro hinj v hv hsum
    have hw : ∀ i, ∃ w : NLA.TR06.PivotData (q i),
        fderiv ℝ (NLA.TR06.tensorFromPivotData (q i)) (p i) w = v i := by
      intro i
      obtain ⟨w,hw⟩ := rankOneTangent_has_pivot_preimage (q i)
        (NLA.TR06.tensorFromPivotData (q i) (p i)) (v i)
        (by rw [NLA.TR06.tensorFromPivotData_pivot]; exact hp i) (hv i)
      rw [NLA.TR06.tensorToPivotData_from (q i) (p i) (hp i)] at hw
      exact ⟨w,hw⟩
    choose w hw using hw
    have hz : fderiv ℝ (NLA.TR06.pivotSum q) p w = 0 := by
      rw [fderiv_pivotSum_apply]
      simp_rw [hw]
      exact hsum
    have hwzero : w=0 := hinj (by simpa only [map_zero] using hz)
    intro i
    rw [← hw i,hwzero]
    simp

#assert_trust kernel decoder_derivative_injective
#assert_trust kernel fderiv_pivotSum_apply
#assert_trust kernel regularDecomposition_decoder_iff
#print axioms regularDecomposition_decoder_iff
end NLA.Proofs.TR06.Model
