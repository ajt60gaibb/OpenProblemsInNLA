import NLA.Proofs.TR26.IncidenceIdeal
import NLA.Proofs.TR26.AnalyticConormal

/-! Scaling preserves the actual full incidence, even at isotropic points.
The pullback argument applies to arbitrary ideal polynomials, rather than
assuming that each chosen polynomial is homogeneous. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Topology
open Filter
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem onCurve_smul {d : ℕ} {z : CurveVector d} (hz : OnCurve z)
    (a : ℂ) (ha : a ≠ 0) : OnCurve (a • z) := by
  rcases hz with ⟨u,v,c,huv,hc,hz⟩
  refine ⟨u,v,a*c,huv,mul_ne_zero ha hc,?_⟩
  intro i
  change a * z i = _
  rw [hz i]
  ring

theorem openCritical_smul {d : ℕ} {z : CurveVector d} {H : Parameter d}
    (h : OpenCritical z H) (a : ℂ) (ha : a ≠ 0) : OpenCritical (a • z) H := by
  rcases h with ⟨hH,u,v,c,huv,hc,hz,hD,hDa,hDb⟩
  refine ⟨hH,u,v,a*c,huv,mul_ne_zero ha hc,?_,hD,hDa,hDb⟩
  intro i
  change a * z i = _
  rw [hz i]
  ring

def scaleIncidencePolynomial (d : ℕ) (a : ℂ) (f : IncidenceRing d) : IncidenceRing d :=
  MvPolynomial.aeval (fun j : IncidenceVariable d => match j with
    | .inl i => MvPolynomial.C a * MvPolynomial.X (.inl i)
    | .inr ij => MvPolynomial.X (.inr ij)) f

theorem eval_scaleIncidencePolynomial (d : ℕ) (a : ℂ) (f : IncidenceRing d)
    (z : CurveVector d) (H : Parameter d) :
    MvPolynomial.eval (incidenceCoordinates z H) (scaleIncidencePolynomial d a f) =
      MvPolynomial.eval (incidenceCoordinates (a • z) H) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [scaleIncidencePolynomial]
  | add f g hf hg => simp only [scaleIncidencePolynomial,map_add] at *; rw [hf,hg]
  | mul_X f j hf =>
      simp only [scaleIncidencePolynomial,map_mul,MvPolynomial.aeval_X] at *
      rw [hf]
      cases j <;> simp [incidenceCoordinates]

theorem incidence_smul {d : ℕ} {z : CurveVector d} {H : Parameter d}
    (h : Incidence d z H) (a : ℂ) (ha : a ≠ 0) : Incidence d (a • z) H := by
  refine ⟨smul_ne_zero ha h.1,h.2.1,onCurve_smul h.2.2.1 a ha,?_⟩
  intro f hf
  have hs : VanishesOnOpen d (scaleIncidencePolynomial d a f) := by
    intro z' H' h'
    rw [eval_scaleIncidencePolynomial]
    exact hf (a • z') H' (openCritical_smul h' a ha)
  have hh := h.2.2.2 (scaleIncidencePolynomial d a f) hs
  rwa [eval_scaleIncidencePolynomial] at hh

theorem jacobianSpace_annihilates_radial {d : ℕ} {z : CurveVector d} {H : Parameter d}
    (h : Incidence d z H) :
    ∀ g ∈ JacobianSpace d z H, ∑ i, g i * z i = 0 := by
  let γ : ℂ → IncidenceVariable d → ℂ :=
    fun s => incidenceCoordinates (s • z) H
  have hzero (f : IncidenceRing d) (hf : f ∈ openVanishingIdeal d) :
      (fun s => MvPolynomial.eval (γ s) f) =ᶠ[𝓝 (1 : ℂ)] fun _ => 0 := by
    filter_upwards [eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0)] with s hs
    exact (incidence_smul h s hs).2.2.2 f ((mem_openVanishingIdeal_iff d f).mp hf)
  have hz (i : Index d) : HasDerivAt (fun s => γ s (.inl i)) (z i) 1 := by
    simpa [γ,incidenceCoordinates] using (hasDerivAt_id (1 : ℂ)).mul_const (z i)
  have hH (i : SymIndex d) : HasDerivAt (fun s => γ s (.inr i)) 0 1 :=
    hasDerivAt_const 1 (H i)
  have hh := idealConormal_annihilates_curve (openVanishingIdeal d) γ z 1 hz hH hzero
  simpa only [γ,one_smul,← jacobianSpace_eq_conormal] using hh

#assert_trust kernel onCurve_smul
#assert_trust kernel openCritical_smul
#assert_trust kernel eval_scaleIncidencePolynomial
#assert_trust kernel incidence_smul
#assert_trust kernel jacobianSpace_annihilates_radial
#print axioms incidence_smul
#print axioms jacobianSpace_annihilates_radial
end NLA.Proofs.TR26
