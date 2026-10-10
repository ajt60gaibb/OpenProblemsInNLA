import OAI.Analysis.DirectCrouzeix.BoundaryParametrization

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

def inverseExterior (f : ℂ → ℝ) (a : ℂ) : Set ℂ := {w | w = 0 ∨ 1 < f (a+w⁻¹)}

@[simp] theorem zero_mem_inverseExterior (f : ℂ → ℝ) (a : ℂ) : 0 ∈ inverseExterior f a := Or.inl rfl

theorem mem_inverseExterior_iff {f : ℂ → ℝ} {a w : ℂ} (hw : w ≠ 0) :
    w ∈ inverseExterior f a ↔ 1 < f (a+w⁻¹) := or_iff_right hw

theorem inverseExterior_isOpen {f : ℂ → ℝ} (hf : Continuous f)
    (hc : IsCompact {z | f z ≤ 1}) (a : ℂ) : IsOpen (inverseExterior f a) := by
  obtain ⟨M,hM,hbound⟩ := hc.isBounded.exists_pos_norm_le
  rw [isOpen_iff_mem_nhds]
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    let r := (M+‖a‖+1)⁻¹
    have hr : 0 < r := inv_pos.mpr (by positivity)
    apply mem_of_superset (ball_mem_nhds (0:ℂ) hr)
    intro w hw
    by_cases hw0 : w = 0
    · exact Or.inl hw0
    apply Or.inr
    by_contra hn
    have hh := hbound (a+w⁻¹) (le_of_not_gt hn)
    have hnorm : ‖w⁻¹‖ ≤ M+‖a‖ := by
      calc
        ‖w⁻¹‖ = ‖(a+w⁻¹)-a‖ := by congr 1; abel
        _ ≤ ‖a+w⁻¹‖+‖a‖ := norm_sub_le _ _
        _ ≤ M+‖a‖ := add_le_add_left hh _
    have hrw : ‖w‖ < (M+‖a‖+1)⁻¹ := mem_ball_zero_iff.mp hw
    have hlarge : M+‖a‖+1 < ‖w‖⁻¹ := (lt_inv_comm₀ (norm_pos_iff.mpr hw0) (by positivity)).mp hrw
    rw [norm_inv] at hnorm
    linarith
  · have hc' : ContinuousAt (fun w : ℂ => f (a+w⁻¹)) w :=
      hf.continuousAt.comp (continuousAt_const.add (continuousAt_id.inv₀ hw0))
    have he : ∀ᶠ y in 𝓝 w, 1 < f (a+y⁻¹) := continuousAt_const.eventually_lt hc' ((mem_inverseExterior_iff hw0).mp hw)
    exact mem_of_superset he (fun y hy => Or.inr hy)

theorem inverseExterior_starConvex {f : ℂ → ℝ} (hf : ConvexOn ℝ univ f)
    {a : ℂ} (ha : f a < 1) : StarConvex ℝ 0 (inverseExterior f a) := by
  intro x hx t s ht hs hts
  simp only [smul_zero,zero_add]
  by_cases hs0 : s = 0
  · simp [hs0]
  by_cases hx0 : x = 0
  · simp [hx0]
  have hxout := (mem_inverseExterior_iff hx0).mp hx
  apply Or.inr
  by_contra hn
  have hnew : f (a+(s • x)⁻¹) ≤ 1 := le_of_not_gt hn
  have hsC : (s:ℂ) ≠ 0 := by exact_mod_cast hs0
  have hsum : (t:ℂ)+(s:ℂ)=1 := by exact_mod_cast hts
  have he : t • a+s • (a+(s • x)⁻¹) = a+x⁻¹ := by
    simp only [Complex.real_smul,mul_add]
    rw [mul_inv_rev]
    have hh : (s:ℂ)*((x⁻¹)*(s:ℂ)⁻¹) = x⁻¹ := by field_simp
    rw [hh]
    linear_combination a*hsum
  have hconv := hf.2 (mem_univ a) (mem_univ (a+(s • x)⁻¹)) ht hs hts
  rw [he] at hconv
  have h1 := mul_le_mul_of_nonneg_left (le_of_lt ha) ht
  have h2 := mul_le_mul_of_nonneg_left hnew hs
  dsimp only [smul_eq_mul] at hconv
  nlinarith

theorem inverseExterior_simplyConnected {f : ℂ → ℝ} (hf : ConvexOn ℝ univ f)
    {a : ℂ} (ha : f a < 1) : IsSimplyConnected (inverseExterior f a) := by
  let : ContractibleSpace (inverseExterior f a) :=
    (inverseExterior_starConvex hf ha).contractibleSpace ⟨0,zero_mem_inverseExterior f a⟩
  change SimplyConnectedSpace (inverseExterior f a)
  infer_instance

theorem inverseExterior_bounded {f : ℂ → ℝ} (hf : Continuous f)
    {a : ℂ} (ha : f a < 1) : ∃ L > 0, inverseExterior f a ⊆ closedBall 0 L := by
  have hnh : {z | f z < 1} ∈ 𝓝 a := (isOpen_lt hf continuous_const).mem_nhds ha
  obtain ⟨r,hr,hrB⟩ := Metric.mem_nhds_iff.mp hnh
  refine ⟨r⁻¹,inv_pos.mpr hr,?_⟩
  intro w hw
  rw [mem_closedBall_zero_iff]
  by_cases hw0 : w = 0
  · subst w; simp [le_of_lt (inv_pos.mpr hr)]
  by_contra hn
  have hwL : r⁻¹ < ‖w‖ := lt_of_not_ge hn
  have hninv : ‖w‖⁻¹ < r := (inv_lt_comm₀ hr (norm_pos_iff.mpr hw0)).mp hwL
  have hball : a+w⁻¹ ∈ ball a r := by simpa [dist_eq_norm,norm_inv] using hninv
  have hh : f (a+w⁻¹) < 1 := hrB hball
  have hout := (mem_inverseExterior_iff hw0).mp hw
  linarith

theorem inverseExterior_compact_closure {f : ℂ → ℝ} (hf : Continuous f)
    {a : ℂ} (ha : f a < 1) : IsCompact (closure (inverseExterior f a)) := by
  obtain ⟨L,hL,hB⟩ := inverseExterior_bounded hf ha
  exact (isCompact_closedBall (0:ℂ) L).of_isClosed_subset isClosed_closure
    (closure_minimal hB isClosed_closedBall)

theorem inverseExterior_proper {f : ℂ → ℝ} (hf : Continuous f)
    {a : ℂ} (ha : f a < 1) : inverseExterior f a ≠ univ := by
  obtain ⟨L,hL,hB⟩ := inverseExterior_bounded hf ha
  intro he
  have hh := hB (show ((L+1:ℝ):ℂ) ∈ inverseExterior f a from he ▸ mem_univ _)
  rw [mem_closedBall_zero_iff,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)] at hh
  linarith

theorem inverseExterior_frontier_level {f : ℂ → ℝ} (hf : Continuous f)
    (hc : IsCompact {z | f z ≤ 1}) {a w : ℂ}
    (hw : w ∈ frontier (inverseExterior f a)) : w ≠ 0 ∧ f (a+w⁻¹) = 1 := by
  have hU := inverseExterior_isOpen hf hc a
  have hw' : w ∈ closure (inverseExterior f a) ∧ w ∉ inverseExterior f a := by
    simpa only [frontier,hU.interior_eq,Set.mem_sdiff] using hw
  have hw0 : w ≠ 0 := by intro he; subst w; exact hw'.2 (zero_mem_inverseExterior f a)
  refine ⟨hw0,le_antisymm (le_of_not_gt (fun h => hw'.2 (Or.inr h))) ?_⟩
  by_contra hn
  have hl : f (a+w⁻¹) < 1 := lt_of_not_ge hn
  have hct : ContinuousAt (fun y : ℂ => f (a+y⁻¹)) w :=
    hf.continuousAt.comp (continuousAt_const.add (continuousAt_id.inv₀ hw0))
  have he : {y : ℂ | y ≠ 0 ∧ f (a+y⁻¹) < 1} ∈ 𝓝 w :=
    (continuousAt_id.eventually_ne hw0).and (hct.eventually_lt continuousAt_const hl)
  obtain ⟨y,hy,hyU⟩ := mem_closure_iff_nhds.mp hw'.1 _ he
  have hout := (mem_inverseExterior_iff hy.1).mp hyU
  linarith [hy.2]

end DirectCrouzeix.Geometry

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end

end

end

end OAI
