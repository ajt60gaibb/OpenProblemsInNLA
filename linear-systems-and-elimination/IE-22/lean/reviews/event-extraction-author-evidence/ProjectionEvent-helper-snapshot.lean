import NLA.IE22.TrimmingThreshold
import NLA.IE22.GaussianMean

/-! Probability assembly for the exact finite Gaussian projection certificate.
Intermediate lemmas expose their inputs; the selected final target will only
be introduced after the independent variance and energy modules supply them.
Original mathematical proof: Matthew J. Colbrook.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with AI-agent assistance. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE22
open NLA.IE21

lemma measureReal_abs_deviation_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) (hX : MemLp X 2 μ)
    (ε : ℝ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ |X ω - ∫ w, X w ∂μ|} ≤ Var[X;μ] / ε^2 := by
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg X μ) (sq_nonneg ε))
    (meas_ge_le_variance_div_sq hX hε)

lemma measureReal_upper_tail_le_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) (hX : MemLp X 2 μ)
    (a ε : ℝ) (hε : 0 < ε) (ha : (∫ w, X w ∂μ) ≤ a) :
    μ.real {ω | a+ε < X ω} ≤ Var[X;μ] / ε^2 := by
  apply (measureReal_mono (show {ω | a+ε < X ω} ⊆
      {ω | ε ≤ |X ω-∫ w, X w ∂μ|} from ?_)).trans
    (measureReal_abs_deviation_le μ X hX ε hε)
  intro ω hω
  change a+ε < X ω at hω
  change ε ≤ |X ω-∫ w, X w ∂μ|
  have hh := le_abs_self (X ω-∫ w, X w ∂μ)
  linarith

lemma gaussian_radius_lower_tail (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ : 0 < δ) :
    (stdGaussian (Space d)).real {g | ‖g‖^2 < (1-δ)*(d : ℝ)} ≤
      2 / ((d : ℝ)*δ^2) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hi : MemLp (fun g : Space d => ‖g‖^2) 2 (stdGaussian (Space d)) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    simpa only [← pow_mul] using gaussian_norm_pow_integrable d 4
  have hv : Var[(fun g : Space d => ‖g‖^2);stdGaussian (Space d)] = 2*(d : ℝ) := by
    rw [variance_eq_integral (by fun_prop),gaussian_norm_sq_mean d hd]
    exact gaussian_norm_sq_centered_moment d hd
  have hsub : {g : Space d | ‖g‖^2 < (1-δ)*(d : ℝ)} ⊆
      {g | δ*(d : ℝ) ≤ |‖g‖^2-∫ x : Space d, ‖x‖^2 ∂stdGaussian (Space d)|} := by
    intro g hg
    change ‖g‖^2 < (1-δ)*(d : ℝ) at hg
    change δ*(d : ℝ) ≤ |‖g‖^2-∫ x : Space d, ‖x‖^2 ∂stdGaussian (Space d)|
    rw [gaussian_norm_sq_mean d hd]
    have hh := neg_le_abs (‖g‖^2-(d : ℝ))
    nlinarith
  have h := (measureReal_mono hsub).trans
    (measureReal_abs_deviation_le (stdGaussian (Space d)) _ hi (δ*(d : ℝ)) (mul_pos hδ hdpos))
  rw [hv] at h
  have heq : 2*(d : ℝ)/(δ*(d : ℝ))^2 = 2/((d : ℝ)*δ^2) := by
    field_simp
  rwa [heq] at h

lemma continuous_projectedObjective {m d : ℕ} (θ t : ℝ) (B : Mat m d) :
    Continuous (projectedObjective θ B t) := by
  unfold projectedObjective trimDual
  fun_prop

lemma projectionGood_measurable {m d : ℕ} (θ δ : ℝ) (B : Mat m d) :
    MeasurableSet (ProjectionGood θ B δ) := by
  apply IsClosed.measurableSet
  have heq : ProjectionGood θ B δ =
      {g | projectedEnergy B g ≤ 2} ∩ {g | (1-δ)*(d : ℝ) ≤ ‖g‖^2} ∩
      ⋂ t : ℝ, ⋂ (_ht : 0 ≤ t), ⋂ (_htL : t ≤ truncationScale θ),
        {g | projectedObjective θ B t g ≤ gaussianTrim θ+2*δ} := by
    ext g
    simp [ProjectionGood,and_assoc]
  rw [heq]
  refine (IsClosed.inter (isClosed_le (by unfold projectedEnergy; fun_prop) continuous_const)
    (isClosed_le continuous_const (by fun_prop))).inter ?_
  apply isClosed_iInter
  intro t
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro _
  exact isClosed_le (continuous_projectedObjective θ t B) continuous_const

/-- Explicit finite-grid assembly; this helper is not the selected final theorem. -/
lemma projection_event_probability_of_bounds (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (B : Mat m d)
    (δ : ℝ) (hδ : 0 < δ) (BE BT : ℝ) (hBT : 0 ≤ BT)
    (henergy : (stdGaussian (Space d)).real {g | 2 < projectedEnergy B g} ≤ BE)
    (hpoint : ∀ t ∈ Icc 0 (truncationScale θ),
      (stdGaussian (Space d)).real {g | gaussianTrim θ+δ < projectedObjective θ B t g} ≤ BT) :
    (stdGaussian (Space d)).real (ProjectionGood θ B δ)ᶜ ≤
      BE+(truncationScale θ/δ+2)*BT+2/((d : ℝ)*δ^2) := by
  classical
  obtain ⟨C,hC,hcard,hcover⟩ := threshold_grid θ hθ δ hδ
  let Bad (t : ℝ) : Set (Space d) := {g | gaussianTrim θ+δ < projectedObjective θ B t g}
  have hsub : (ProjectionGood θ B δ)ᶜ ⊆
      ({g | 2 < projectedEnergy B g} ∪ ⋃ t ∈ C, Bad t) ∪
      {g | ‖g‖^2 < (1-δ)*(d : ℝ)} := by
    intro g hg
    by_contra hout
    have he : projectedEnergy B g ≤ 2 := le_of_not_gt (fun h => hout (Or.inl (Or.inl h)))
    have hr : (1-δ)*(d : ℝ) ≤ ‖g‖^2 := le_of_not_gt (fun h => hout (Or.inr h))
    have hgrid : ∀ s ∈ C, projectedObjective θ B s g ≤ gaussianTrim θ+δ := by
      intro s hs
      apply le_of_not_gt
      intro h
      exact hout (Or.inl (Or.inr (mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨hs,h⟩⟩)))
    apply hg
    refine ⟨he,hr,?_⟩
    intro t ht htL
    obtain ⟨s,hs,hdist⟩ := hcover t ⟨ht,htL⟩
    have hlip := threshold_lipschitz θ hθ m hm (fun i => (matrixMap B g i)^2) t s
    change |projectedObjective θ B t g-projectedObjective θ B s g| ≤ |t-s| at hlip
    have hh := (le_abs_self _).trans (hlip.trans hdist)
    have hg' := hgrid s hs
    linarith
  have hsum : (∑ t ∈ C, (stdGaussian (Space d)).real (Bad t)) ≤ (C.card : ℝ)*BT := by
    have hh := Finset.sum_le_sum (s := C) (fun t ht => hpoint t (hC t ht))
    simpa only [Bad,Finset.sum_const,nsmul_eq_mul] using hh
  calc
    _ ≤ (stdGaussian (Space d)).real (({g | 2 < projectedEnergy B g} ∪ ⋃ t ∈ C, Bad t) ∪
        {g | ‖g‖^2 < (1-δ)*(d : ℝ)}) := measureReal_mono hsub
    _ ≤ ((stdGaussian (Space d)).real {g | 2 < projectedEnergy B g}+
        ∑ t ∈ C, (stdGaussian (Space d)).real (Bad t))+
        (stdGaussian (Space d)).real {g | ‖g‖^2 < (1-δ)*(d : ℝ)} := by
      apply (measureReal_union_le _ _).trans
      apply add_le_add _ le_rfl
      exact (measureReal_union_le _ _).trans
        (add_le_add le_rfl (measureReal_biUnion_finset_le (μ := stdGaussian (Space d)) C Bad))
    _ ≤ (BE+(C.card : ℝ)*BT)+2/((d : ℝ)*δ^2) :=
      add_le_add (add_le_add henergy hsum) (gaussian_radius_lower_tail d hd δ hδ)
    _ ≤ _ := add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard hBT)) le_rfl

/-- Assembly from explicit moment inputs, kept separate from the selected final
statement until those inputs are supplied by the Gaussian proof modules. -/
lemma projection_good_event_of_energy_variance (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m d r : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (B : Mat m d)
    (hrows : ∀ i, ‖matrixRow B i‖ ≤ 1)
    (hop : operatorNorm B^2 ≤ (m : ℝ)/((r : ℝ)+1))
    (δ : ℝ) (hδ : 0 < δ)
    (hE : MemLp (projectedEnergy B) 2 (stdGaussian (Space d)))
    (hEmean : (∫ g, projectedEnergy B g ∂stdGaussian (Space d)) ≤ 1)
    (hEvar : Var[projectedEnergy B;stdGaussian (Space d)] ≤ 2/((r : ℝ)+1))
    (hV : ∀ t : ℝ, 0 ≤ t →
      MemLp (projectedObjective θ B t) 2 (stdGaussian (Space d)) ∧
      Var[projectedObjective θ B t;stdGaussian (Space d)] ≤ 4*t*operatorNorm B^2/m) :
    MeasurableSet (ProjectionGood θ B δ) ∧
    (stdGaussian (Space d)).real (ProjectionGood θ B δ)ᶜ ≤ projectionFailure θ d r δ := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hrpos : (0 : ℝ) < (r : ℝ)+1 := by positivity
  have hgap : 0 < 1-θ := sub_pos.mpr hθ.2
  have hL : 0 ≤ truncationScale θ := by unfold truncationScale; positivity
  have henergy : (stdGaussian (Space d)).real {g | 2 < projectedEnergy B g} ≤
      2/((r : ℝ)+1) := by
    have h := measureReal_upper_tail_le_variance (stdGaussian (Space d))
      (projectedEnergy B) hE 1 1 (by norm_num) hEmean
    norm_num at h
    exact h.trans hEvar
  let BT := 4*truncationScale θ/(((r : ℝ)+1)*δ^2)
  have hBT : 0 ≤ BT := by dsimp [BT]; positivity
  have hpoint : ∀ t ∈ Icc 0 (truncationScale θ),
      (stdGaussian (Space d)).real {g | gaussianTrim θ+δ < projectedObjective θ B t g} ≤ BT := by
    intro t ht
    have hmean := (gaussian_objective_mean θ hθ m d hm hd B hrows t ht.1).2
    have hv := hV t ht.1
    have hvariance : Var[projectedObjective θ B t;stdGaussian (Space d)] ≤
        4*truncationScale θ/((r : ℝ)+1) := by
      calc
        _ ≤ 4*t*operatorNorm B^2/m := hv.2
        _ ≤ (4*truncationScale θ*((m : ℝ)/((r : ℝ)+1)))/m := by gcongr; exact ht.2
        _ = _ := by field_simp
    have hprob := measureReal_upper_tail_le_variance (stdGaussian (Space d))
      (projectedObjective θ B t) hv.1 (gaussianTrim θ) δ hδ hmean
    apply hprob.trans
    calc
      _ ≤ (4*truncationScale θ/((r : ℝ)+1))/δ^2 :=
        div_le_div_of_nonneg_right hvariance (sq_nonneg δ)
      _ = BT := by dsimp [BT]; rw [div_div]
  refine ⟨projectionGood_measurable θ δ B,?_⟩
  have h := projection_event_probability_of_bounds θ hθ m d hm hd B δ hδ
    (2/((r : ℝ)+1)) BT hBT henergy hpoint
  convert h using 1
  unfold projectionFailure BT
  ring

end NLA.IE22
