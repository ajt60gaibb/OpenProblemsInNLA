import NLA.Proofs.PF05.Resolvent
import NLA.Proofs.PF05.OneSidedPSD
import NLA.Proofs.PF05.PositiveReduction

/-! The actual inverse-dual path stays PSD for every feasible straight segment.
The flat rank-one case is proved by an exact resolvent eigenvector identity. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Topology
open Filter
namespace NLA.Proofs.PF05
open NLA.Statements.PF05 CoordinateActions

theorem inverse_dual_psd_near_of_segment (T : M3) (B : M2)
    (hB : PositiveSemidefinite B)
    (hseg : ∃ h : ℝ, 0<h ∧ ∀ t, 0≤t → t<h →
      PositiveSemidefinite (B+t • (-dual T B))) :
    ∃ h : ℝ, 0<h ∧ ∀ t, 0≤t → t<h →
      PositiveSemidefinite (dual (inversePencil T t) B) := by
  have hF : Symmetric (-dual T B) := by
    intro i j; simp [Matrix.neg_apply,dual_symmetric T B i j]
  have hd (i j : Fin 2) : HasDerivAt (fun t => dual (inversePencil T t) B i j)
      ((-dual T B) i j) 0 := inverse_dual_entry_derivative T B i j
  have h0 : dual (inversePencil T 0) B=B := inverse_dual_zero T B hB.1
  by_cases hne : B=0
  · subst B
    refine ⟨1,by norm_num,?_⟩
    intro t _ _
    rw [dual_zero_input]
    exact hB
  have hdet := psd_det_nonneg B hB
  rcases eq_or_lt_of_le hdet with hzero|hpos
  · have hdet0 : B.det=0 := hzero.symm
    have hq := determinantDirection_nonneg_of_segment B (-dual T B) hB.1 hF hdet0 hseg
    rcases eq_or_lt_of_le hq with hqzero|hqpos
    · have hflat : determinantDirection B (-dual T B)=0 := hqzero.symm
      obtain ⟨d,hdscalar⟩ := flat_psd_segment_direction_scalar B (-dual T B)
        hB hne hF hdet0 hflat hseg
      have heig : dual T B=(-d) • B := by
        have h := congrArg Neg.neg hdscalar
        simpa [neg_smul] using h
      have hc : ContinuousAt (fun t : ℝ => 1+t*(-d)) 0 := by fun_prop
      have hp : 0<1+(0:ℝ)*(-d) := by norm_num
      apply right_segment_of_eventually_nhds
      filter_upwards [pencil_det_eventually_ne_zero T,hc.eventually (lt_mem_nhds hp)] with t ht hscalar
      rw [inversePencil,dual_resolvent_eigen T B hB.1 (-d) t heig ht (ne_of_gt hscalar)]
      exact psd_smul_of_nonneg B hB _ (inv_pos.mpr hscalar).le
    · exact psd_near_of_det_derivative_pos _ B (-dual T B) h0 hB hne hF
        (fun t => dual_symmetric _ _) hd hdet0 hqpos
  · exact psd_near_of_det_pos _ B (-dual T B) h0 hB hF
      (fun t => dual_symmetric _ _) hd hpos

/-- A finite collection of actual one-sided intervals has one common interval,
including when its indexing type is empty. -/
theorem finite_common_psd_interval {ι : Type*} [Finite ι]
    (P : ι → ℝ → Prop)
    (hP : ∀ i, ∃ h : ℝ, 0<h ∧ ∀ t, 0≤t → t<h → P i t) :
    ∃ h : ℝ, 0<h ∧ ∀ t, 0≤t → t<h → ∀ i, P i t := by
  have he : ∀ᶠ t : ℝ in 𝓝[≥] 0, ∀ i, P i t := by
    apply Filter.eventually_all.mpr
    intro i
    obtain ⟨h,hh,hpi⟩ := hP i
    exact mem_nhdsGE_iff_exists_Ico_subset.mpr ⟨h,hh,fun t ht => hpi t ht.1 ht.2⟩
  obtain ⟨h,hh,hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp he
  exact ⟨h,hh,fun t ht hth => hsub ⟨ht,hth⟩⟩

#assert_trust kernel inverse_dual_psd_near_of_segment
#assert_trust kernel finite_common_psd_interval
#print axioms inverse_dual_psd_near_of_segment
end NLA.Proofs.PF05
