import NLA.Proofs.TR06.AlgebraicLocusNull
import NLA.Proofs.TR06.AdditionGoodBase
import NLA.Proofs.TR06.UnramifiedDifferentialReal
import NLA.TR06.RegularChart
import NLA.TR06.LocusMeasurability

/-! The original generic-identifiability hypothesis supplies actual proper,
unramified good charts, with expected-dimensional null exceptional set and an
actual real regular witness. No certificate is a final assumption. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.AlgebraicLocus
open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory Set NLA.TR06 NLA.TR06.Proposed
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem isOpen_real_polynomial_ne_zero (p : MvPolynomial (TensorIndex d n) ℂ) :
    IsOpen {A : Tensor ℝ d n | MvPolynomial.eval (fun q => complexify A q) p ≠ 0} := by
  apply isOpen_ne_fun _ continuous_const
  exact (MvPolynomial.continuous_eval p).comp
    (continuous_pi fun q => Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ q))

theorem generic_smooth_regular_good_polynomial (hd : 0 < d) (hn : ∀ j, 0 < n j)
    (hr : 2 ≤ r) (hgeneric : GenericComplexIdentifiable d n r) :
    ∃ P : MvPolynomial (TensorIndex d n) ℂ,
      additionAlgebraHom d n r P ≠ 0 ∧
      IsOpen {A : Tensor ℝ d n | MvPolynomial.eval (fun q => complexify A q) P ≠ 0} ∧
      IdentifiableAdditionOn (r := r)
        {A : Tensor ℝ d n | MvPolynomial.eval (fun q => complexify A q) P ≠ 0} ∧
      ({A : Tensor ℝ d n | MvPolynomial.eval (fun q => complexify A q) P ≠ 0} ∩
        identifiableRealSet d n r ⊆ smoothRegularSet d n r) := by
  obtain ⟨p,hp,hpopen,hgood,hproper⟩ := generic_identifiability_good_base hd hn hr hgeneric
  obtain ⟨j,hj,hjac⟩ := UnramifiedDifferential.exists_ambient_real_derivative_denominator hd hgeneric
  let P := p*j
  let U : Set (Tensor ℝ d n) :=
    {A | MvPolynomial.eval (fun q => complexify A q) P ≠ 0}
  have hU : U = {A | MvPolynomial.eval (fun q => complexify A q) p ≠ 0} ∩
      {A | MvPolynomial.eval (fun q => complexify A q) j ≠ 0} := by
    ext A
    simp only [U,P,map_mul,mul_ne_zero_iff,mem_ofPred_eq,mem_inter_iff]
  have hopen : IsOpen U := by
    rw [hU]
    exact hpopen.inter (isOpen_real_polynomial_ne_zero j)
  have hgoodU : IdentifiableAdditionOn (r := r) U := by
    rw [hU]
    exact fun A hA hdec => hgood A hA.1 hdec
  have hproperU : CompactAdditionPreimagesOn (r := r) U := by
    rw [hU]
    exact fun K hK hKU => hproper K hK (fun A hA => (hKU hA).1)
  refine ⟨P,by simpa only [P,map_mul] using mul_ne_zero hp hj,hopen,hgoodU,?_⟩
  apply smooth_regular_on_proper_immersion d n r hd U hopen hgoodU hproperU
  intro q₀ z hznz hzU
  exact hjac q₀ z hznz ((hU ▸ hzU).2)

theorem generic_smoothRegular_full_measure (hd : 0 < d) (hn : ∀ j, 0 < n j)
    (hr : 2 ≤ r) (hgeneric : GenericComplexIdentifiable d n r) :
    ∀ᵐ A ∂tensorVolume d n r, A ∈ smoothRegularSet d n r := by
  obtain ⟨P,hP,_hopen,_hgood,hcharts⟩ := generic_smooth_regular_good_polynomial hd hn hr hgeneric
  have hmem : ∀ᵐ A ∂tensorVolume d n r, A ∈ identifiableRealSet d n r :=
    ae_restrict_mem (measurableSet_identifiableRealSet d n r)
  filter_upwards [hmem,sampling_ae_polynomial_ne_zero P hP] with A hA hPA
  exact hcharts ⟨hPA,hA⟩

theorem generic_smoothRegular_nonempty (hd : 0 < d) (hn : ∀ j, 0 < n j)
    (hr : 2 ≤ r) (hgeneric : GenericComplexIdentifiable d n r) :
    (smoothRegularSet d n r).Nonempty := by
  obtain ⟨P,hP,_hopen,hgood,hcharts⟩ := generic_smooth_regular_good_polynomial hd hn hr hgeneric
  let q₀ : Fin r → TensorIndex d n := fun _ j => ⟨0,hn j⟩
  obtain ⟨A,a,ha,hPA⟩ := exists_real_decomposition_good hd q₀ P hP
  exact ⟨A,hcharts ⟨hPA,hgood A hPA ⟨a,ha⟩⟩⟩

#assert_trust kernel isOpen_real_polynomial_ne_zero
#assert_trust kernel generic_smooth_regular_good_polynomial
#assert_trust kernel generic_smoothRegular_full_measure
#assert_trust kernel generic_smoothRegular_nonempty
#print axioms generic_smoothRegular_full_measure
#print axioms generic_smoothRegular_nonempty
end NLA.Proofs.TR06.AlgebraicLocus
