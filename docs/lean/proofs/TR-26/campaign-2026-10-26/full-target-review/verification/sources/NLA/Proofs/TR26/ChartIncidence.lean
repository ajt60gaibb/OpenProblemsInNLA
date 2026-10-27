import NLA.Proofs.TR26.IncidenceScaling
import NLA.Proofs.TR26.TangentRank
import NLA.Proofs.TR26.LinearCriticalGraph

/-! Full-ideal incidence and rank upper bounds from an actual chart identity.
The chart identity, nonzero pivot, and double-root conditions remain explicit
until discharged for the concrete Wronskian in both curve charts. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Topology
open Filter
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem incidenceCoordinates_continuousAt
    (d : ℕ) (ζ : ℂ → CurveVector d) (η : ℂ → Parameter d) (t : ℂ)
    (hζ : ContinuousAt ζ t) (hη : ContinuousAt η t) :
    ContinuousAt (fun s => incidenceCoordinates (ζ s) (η s)) t := by
  apply continuousAt_pi.mpr
  intro j
  cases j with
  | inl i => exact continuousAt_pi.mp hζ i
  | inr i => exact continuousAt_pi.mp hη i

theorem chart_incidence_of_root
    (d : ℕ) (ζ : ℂ → CurveVector d) (hζ : Continuous ζ)
    (L : SymIndex d → Polynomial ℂ) (P : Polynomial ℂ) (hP : P ≠ 0)
    (hcritical : ∀ s (A : Parameter d), A ≠ 0 → P.eval s ≠ 0 →
      linearCriticalValue L s A = 0 → OpenCritical (ζ s) A)
    (t : ℂ) (H : Parameter d) (hH : H ≠ 0) (hcurve : OnCurve (ζ t))
    (j : SymIndex d) (hj : (L j).eval t ≠ 0)
    (ht : linearCriticalValue L t H = 0) : Incidence d (ζ t) H := by
  let η := criticalGraphParameter L H j
  let γ : ℂ → IncidenceVariable d → ℂ :=
    fun s => incidenceCoordinates (ζ s) (η s)
  have hη : ContinuousAt η t := criticalGraphParameter_continuousAt L H j t hj
  have hηt : η t = H := criticalGraphParameter_at_root L H j t ht
  have hnearH : ∀ᶠ s in 𝓝 t, η s ≠ 0 := hη.eventually_ne (by rw [hηt]; exact hH)
  have hnearA : ∀ᶠ s in 𝓝 t, (L j).eval s ≠ 0 := (L j).continuousAt.eventually_ne hj
  have hγ : ContinuousAt γ t :=
    incidenceCoordinates_continuousAt d ζ η t hζ.continuousAt hη
  refine ⟨onCurve_ne_zero hcurve,hH,hcurve,?_⟩
  intro f hf
  have hh : MvPolynomial.eval (γ t) f = 0 := by
    apply continuousAt_zero_of_polynomial_exclusion (fun s => MvPolynomial.eval (γ s) f)
      t (f.continuous_eval.continuousAt.comp hγ) P hP
    filter_upwards [hnearH,hnearA] with s hsH hsA hsP
    exact hf (ζ s) (η s) (hcritical s (η s) hsH hsP
      (criticalGraphParameter_is_root L H j s hsA))
  simpa only [γ,hηt] using hh

theorem chart_jacobian_annihilates_of_double_root
    (d : ℕ) (ζ : ℂ → CurveVector d) (hζ : Continuous ζ)
    (L : SymIndex d → Polynomial ℂ) (P : Polynomial ℂ) (hP : P ≠ 0)
    (hcritical : ∀ s (A : Parameter d), A ≠ 0 → P.eval s ≠ 0 →
      linearCriticalValue L s A = 0 → OpenCritical (ζ s) A)
    (t : ℂ) (H : Parameter d) (hH : H ≠ 0)
    (j : SymIndex d) (hj : (L j).eval t ≠ 0)
    (ht : linearCriticalValue L t H = 0)
    (hderiv : (linearCriticalPolynomial L H).derivative.eval t = 0)
    (v : CurveVector d) (hv : ∀ i, HasDerivAt (fun s => ζ s i) (v i) t) :
    ∀ g ∈ JacobianSpace d (ζ t) H, ∑ i, g i * v i = 0 := by
  let η := criticalGraphParameter L H j
  let γ : ℂ → IncidenceVariable d → ℂ :=
    fun s => incidenceCoordinates (ζ s) (η s)
  have hη : ContinuousAt η t := criticalGraphParameter_continuousAt L H j t hj
  have hηt : η t = H := criticalGraphParameter_at_root L H j t ht
  have hnearH : ∀ᶠ s in 𝓝 t, η s ≠ 0 := hη.eventually_ne (by rw [hηt]; exact hH)
  have hnearA : ∀ᶠ s in 𝓝 t, (L j).eval s ≠ 0 := (L j).continuousAt.eventually_ne hj
  have hγz (i : Index d) : HasDerivAt (fun s => γ s (.inl i)) (v i) t := hv i
  have hγH (i : SymIndex d) : HasDerivAt (fun s => γ s (.inr i)) 0 t :=
    hasDerivAt_criticalGraphParameter_of_double_root L H j t hj ht hderiv i
  have hcont : ∀ᶠ s in 𝓝 t, ContinuousAt γ s := by
    filter_upwards [hnearA] with s hs
    exact incidenceCoordinates_continuousAt d ζ η s hζ.continuousAt
      (criticalGraphParameter_continuousAt L H j s hs)
  have hS : ∀ᶠ s in 𝓝 t, P.eval s ≠ 0 → γ s ∈ criticalCoordinateSet d := by
    filter_upwards [hnearH,hnearA] with s hsH hsA hsP
    exact ⟨ζ s,η s,hcritical s (η s) hsH hsP
      (criticalGraphParameter_is_root L H j s hsA),rfl⟩
  have hIS (f : IncidenceRing d) (hf : f ∈ openVanishingIdeal d)
      (q : IncidenceVariable d → ℂ) (hq : q ∈ criticalCoordinateSet d) :
      MvPolynomial.eval q f = 0 := by
    rcases hq with ⟨z,A,hA,rfl⟩
    exact (mem_openVanishingIdeal_iff d f).mp hf z A hA
  have hh := idealConormal_annihilates_curve_excluding_polynomial
    (openVanishingIdeal d) (criticalCoordinateSet d) hIS γ v t hγz hγH hcont P hP hS
  simpa only [γ,hηt,← jacobianSpace_eq_conormal] using hh

theorem chart_ramification_of_double_root
    (d : ℕ) (ζ : ℂ → CurveVector d) (hζ : Continuous ζ)
    (L : SymIndex d → Polynomial ℂ) (P : Polynomial ℂ) (hP : P ≠ 0)
    (hcritical : ∀ s (A : Parameter d), A ≠ 0 → P.eval s ≠ 0 →
      linearCriticalValue L s A = 0 → OpenCritical (ζ s) A)
    (t : ℂ) (H : Parameter d) (hH : H ≠ 0) (hcurve : OnCurve (ζ t))
    (j : SymIndex d) (hj : (L j).eval t ≠ 0)
    (ht : linearCriticalValue L t H = 0)
    (hderiv : (linearCriticalPolynomial L H).derivative.eval t = 0)
    (v : CurveVector d) (hv : ∀ i, HasDerivAt (fun s => ζ s i) (v i) t)
    (hind : LinearIndependent ℂ ![ζ t,v]) : Ramification d (ζ t) H := by
  have hI := chart_incidence_of_root d ζ hζ L P hP hcritical t H hH hcurve j hj ht
  refine ⟨hI,?_⟩
  have hr := jacobianSpace_annihilates_radial hI
  have htangent := chart_jacobian_annihilates_of_double_root
    d ζ hζ L P hP hcritical t H hH j hj ht hderiv v hv
  have hdim := finrank_add_two_le_of_annihilates_independent
    (JacobianSpace d (ζ t) H) ![ζ t,v] hind (by
      intro g hg k
      fin_cases k
      · exact hr g hg
      · exact htangent g hg)
  simp only [Fintype.card_fin] at hdim
  have hdim' : Module.finrank ℂ (JacobianSpace d (ζ t) H) + 2 ≤ d+1 := by
    convert! hdim using 1
  have hrank : Module.finrank ℂ (JacobianSpace d (ζ t) H) ≤ d-1 := by omega
  convert! hrank using 1

#assert_trust kernel incidenceCoordinates_continuousAt
#assert_trust kernel chart_incidence_of_root
#assert_trust kernel chart_jacobian_annihilates_of_double_root
#assert_trust kernel chart_ramification_of_double_root
#print axioms chart_incidence_of_root
#print axioms chart_ramification_of_double_root
end NLA.Proofs.TR26
