import NLA.Proofs.TR26.ConormalLemmas

/-! The literal full vanishing ideal and partial conormal space occurring in
the original TR-26 incidence. No convenient selected equations are substituted
for that ideal. Later chart theorems must identify this actual ideal. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

def criticalCoordinateSet (d : ℕ) : Set (IncidenceVariable d → ℂ) :=
  {q | ∃ (z : CurveVector d) (H : Parameter d),
    OpenCritical z H ∧ q = incidenceCoordinates z H}

def openVanishingIdeal (d : ℕ) : Ideal (IncidenceRing d) :=
  MvPolynomial.vanishingIdeal ℂ (criticalCoordinateSet d)

theorem mem_openVanishingIdeal_iff (d : ℕ) (f : IncidenceRing d) :
    f ∈ openVanishingIdeal d ↔ VanishesOnOpen d f := by
  change (∀ q ∈ criticalCoordinateSet d, MvPolynomial.aeval q f = 0) ↔ _
  constructor
  · intro hf z H hcrit
    have h := hf (incidenceCoordinates z H) ⟨z,H,hcrit,rfl⟩
    simpa only [MvPolynomial.aeval_eq_eval] using h
  · intro hf q hq
    rcases hq with ⟨z,H,hcrit,hq⟩
    rw [hq]
    simpa only [MvPolynomial.aeval_eq_eval] using hf z H hcrit

theorem incidence_iff_zeroLocus (d : ℕ) (z : CurveVector d) (H : Parameter d) :
    Incidence d z H ↔ z ≠ 0 ∧ H ≠ 0 ∧ OnCurve z ∧
      incidenceCoordinates z H ∈ MvPolynomial.zeroLocus ℂ (openVanishingIdeal d) := by
  simp only [Incidence, MvPolynomial.mem_zeroLocus_iff,
    mem_openVanishingIdeal_iff, MvPolynomial.aeval_eq_eval]

theorem onCurve_ne_zero {d : ℕ} {z : CurveVector d} (h : OnCurve z) : z ≠ 0 := by
  rcases h with ⟨a,b,c,hab,hc,hz⟩
  intro hzero
  rcases hab with ha | hb
  · have hh := hz (0 : Index d)
    simp [hzero,veronese,hc,ha] at hh
  · have hh := hz (Fin.last d)
    simp [hzero,veronese,hc,hb] at hh

theorem openCritical_onCurve {d : ℕ} {z : CurveVector d} {H : Parameter d}
    (h : OpenCritical z H) : OnCurve z := by
  rcases h with ⟨_,a,b,c,hab,hc,hz,_,_,_⟩
  exact ⟨a,b,c,hab,hc,hz⟩

theorem openCritical_incidence {d : ℕ} {z : CurveVector d} {H : Parameter d}
    (h : OpenCritical z H) : Incidence d z H := by
  have hcurve := openCritical_onCurve h
  exact ⟨onCurve_ne_zero hcurve,h.1,hcurve,fun f hf => hf z H h⟩

theorem jacobianSpace_eq_conormal (d : ℕ) (z : CurveVector d) (H : Parameter d) :
    JacobianSpace d z H = idealConormal (Sum.inl : Index d → IncidenceVariable d)
      (incidenceCoordinates z H) (openVanishingIdeal d) := by
  unfold JacobianSpace idealConormal
  congr 1
  ext v
  constructor
  · rintro ⟨f,hf,hv⟩
    refine ⟨f,(mem_openVanishingIdeal_iff d f).mpr hf,?_⟩
    ext j
    exact congrFun hv.symm j
  · rintro ⟨f,hf,hv⟩
    refine ⟨f,(mem_openVanishingIdeal_iff d f).mp hf,?_⟩
    ext j
    exact congrFun hv.symm j

theorem ramification_iff_conormal (d : ℕ) (z : CurveVector d) (H : Parameter d) :
    Ramification d z H ↔ Incidence d z H ∧
      Module.finrank ℂ (idealConormal (Sum.inl : Index d → IncidenceVariable d)
        (incidenceCoordinates z H) (openVanishingIdeal d)) ≤ d-1 := by
  rw [Ramification,jacobianSpace_eq_conormal]

#assert_trust kernel mem_openVanishingIdeal_iff
#assert_trust kernel incidence_iff_zeroLocus
#assert_trust kernel onCurve_ne_zero
#assert_trust kernel openCritical_onCurve
#assert_trust kernel openCritical_incidence
#assert_trust kernel jacobianSpace_eq_conormal
#assert_trust kernel ramification_iff_conormal
#print axioms mem_openVanishingIdeal_iff
#print axioms jacobianSpace_eq_conormal
#print axioms openCritical_incidence
end NLA.Proofs.TR26
