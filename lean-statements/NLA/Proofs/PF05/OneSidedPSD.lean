import NLA.Proofs.PF05.PSDLine
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.LeftRightNhds

/-! Entrywise calculus and exact one-sided PSD intervals in size two. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Topology
open Filter
namespace NLA.Proofs.PF05
open NLA.Statements.PF05

theorem positive_on_right_of_derivative_pos (f : ℝ → ℝ) (q : ℝ)
    (hd : HasDerivAt f q 0) (hz : f 0=0) (hq : 0<q) :
    ∃ h : ℝ, 0<h ∧ ∀ t, 0<t → t<h → 0<f t := by
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, 0<t⁻¹*f t := by
    simpa [hz,smul_eq_mul] using hd.tendsto_slope_zero_right.eventually (lt_mem_nhds hq)
  have hp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0<f t := by
    filter_upwards [he,self_mem_nhdsWithin] with t ht htp
    have hti : 0<t⁻¹ := inv_pos.mpr htp
    exact ((mul_pos_iff.mp ht).resolve_right (fun h => (not_lt_of_ge hti.le) h.1)).2
  obtain ⟨h,hh,hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hp
  exact ⟨h,hh,fun t ht hth => hsub ⟨ht,hth⟩⟩

theorem right_segment_of_eventually_nhds (P : ℝ → Prop)
    (hP : ∀ᶠ t in 𝓝 (0:ℝ), P t) :
    ∃ h : ℝ, 0<h ∧ ∀ t, 0≤t → t<h → P t := by
  obtain ⟨l,u,⟨hl,hu⟩,hsub⟩ := hP.exists_Ioo_subset
  exact ⟨u,hu,fun t ht htu => hsub ⟨hl.trans_le ht,htu⟩⟩

theorem trace_pos_of_psd_ne_zero (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : PositiveSemidefinite B) (hne : B≠0) : 0<B.trace := by
  have h0 := psd_diag_nonneg B hB 0
  have h1 := psd_diag_nonneg B hB 1
  rw [Matrix.trace_fin_two]
  rcases nonzero_psd_two_positive_diagonal B hB hne with h|h <;> linarith

theorem matrix_trace_derivative
    (f : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (F : Matrix (Fin 2) (Fin 2) ℝ)
    (hd : ∀ i j, HasDerivAt (fun t => f t i j) (F i j) 0) :
    HasDerivAt (fun t => (f t).trace) F.trace 0 := by
  convert! (hd 0 0).add (hd 1 1) using 1
  · funext t; simp [Matrix.trace_fin_two]
  · simp [Matrix.trace_fin_two]

theorem matrix_determinant_derivative
    (f : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (B F : Matrix (Fin 2) (Fin 2) ℝ)
    (h0 : f 0=B) (hB : Symmetric B) (hF : Symmetric F)
    (hd : ∀ i j, HasDerivAt (fun t => f t i j) (F i j) 0) :
    HasDerivAt (fun t => (f t).det) (determinantDirection B F) 0 := by
  convert! ((hd 0 0).mul (hd 1 1)).sub ((hd 0 1).mul (hd 1 0)) using 1
  · ext t; simp [Matrix.det_fin_two]
  · rw [h0]
    simp [determinantDirection,hB 1 0,hF 1 0]
    ring

/-- A strictly positive determinant persists, as does the positive trace. -/
theorem psd_near_of_det_pos
    (f : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (B F : Matrix (Fin 2) (Fin 2) ℝ)
    (h0 : f 0=B) (hB : PositiveSemidefinite B) (hF : Symmetric F)
    (hfs : ∀ t, Symmetric (f t))
    (hd : ∀ i j, HasDerivAt (fun t => f t i j) (F i j) 0)
    (hdet : 0<B.det) :
    ∃ h : ℝ, 0<h ∧ ∀ t, 0≤t → t<h → PositiveSemidefinite (f t) := by
  have hne : B≠0 := by intro h; simp [h] at hdet
  have ht : 0<(f 0).trace := by rw [h0]; exact trace_pos_of_psd_ne_zero B hB hne
  have hdet0 : 0<(f 0).det := by rw [h0]; exact hdet
  have htc := (matrix_trace_derivative f F hd).continuousAt
  have hdc := (matrix_determinant_derivative f B F h0 hB.1 hF hd).continuousAt
  apply right_segment_of_eventually_nhds
  filter_upwards [htc.eventually (lt_mem_nhds ht),hdc.eventually (lt_mem_nhds hdet0)] with t htr hde
  exact psd_two_of_trace_pos_det_nonneg (f t) (hfs t) htr hde.le

/-- At a nonzero singular PSD factor, strictly positive determinant derivative
is sufficient for the actual path to remain PSD on a one-sided interval. -/
theorem psd_near_of_det_derivative_pos
    (f : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (B F : Matrix (Fin 2) (Fin 2) ℝ)
    (h0 : f 0=B) (hB : PositiveSemidefinite B) (hne : B≠0) (hF : Symmetric F)
    (hfs : ∀ t, Symmetric (f t))
    (hd : ∀ i j, HasDerivAt (fun t => f t i j) (F i j) 0)
    (hdet : B.det=0) (hq : 0<determinantDirection B F) :
    ∃ h : ℝ, 0<h ∧ ∀ t, 0≤t → t<h → PositiveSemidefinite (f t) := by
  have hdc := matrix_determinant_derivative f B F h0 hB.1 hF hd
  have hz : (f 0).det=0 := by rw [h0,hdet]
  obtain ⟨h,hpos,hD⟩ := positive_on_right_of_derivative_pos _ _ hdc hz hq
  have ht : 0<(f 0).trace := by rw [h0]; exact trace_pos_of_psd_ne_zero B hB hne
  have htc := (matrix_trace_derivative f F hd).continuousAt
  obtain ⟨u,hupos,htr⟩ := right_segment_of_eventually_nhds _ (htc.eventually (lt_mem_nhds ht))
  refine ⟨min h u, lt_min hpos hupos, ?_⟩
  intro t ht0 htbound
  rcases eq_or_lt_of_le ht0 with hz|htpos
  · rw [← hz,h0]; exact hB
  · exact psd_two_of_trace_pos_det_nonneg (f t) (hfs t)
      (htr t ht0 (htbound.trans_le (min_le_right h u)))
      (hD t htpos (htbound.trans_le (min_le_left h u))).le

#assert_trust kernel positive_on_right_of_derivative_pos
#assert_trust kernel matrix_determinant_derivative
#assert_trust kernel psd_near_of_det_pos
#assert_trust kernel psd_near_of_det_derivative_pos
#print axioms psd_near_of_det_derivative_pos
end NLA.Proofs.PF05
