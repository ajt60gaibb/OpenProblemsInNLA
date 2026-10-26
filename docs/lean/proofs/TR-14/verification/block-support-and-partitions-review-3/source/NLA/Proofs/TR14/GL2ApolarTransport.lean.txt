import NLA.Proofs.TR14.GL2ApolarPairing

/-!
All-degree apolar transport for the explicit invertible TR-14 chart.
The inverse-dual action on moments is essential. This module does not
normalize a minimal form, transport tensor widths, or prove the Target.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

noncomputable section

/-- The coefficient vector of the genuinely substituted homogeneous form. -/
def transportedApolarVector (z : ℂ) (d : ℕ) (g : Fin (d + 1) → ℂ) :
    Fin (d + 1) → ℂ :=
  (binaryFormEquiv d).symm (chartPhi z d (binaryFormEquiv d g))

/-- The transported coefficient map is itself a complex-linear equivalence. -/
def chartCoefficientEquiv (z : ℂ) (d : ℕ) :
    (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ) :=
  (binaryFormEquiv d).trans
    ((chartPhiEquiv z d).trans (binaryFormEquiv d).symm)

theorem chartCoefficientEquiv_apply (z : ℂ) (d : ℕ)
    (g : Fin (d + 1) → ℂ) :
    chartCoefficientEquiv z d g = transportedApolarVector z d g := rfl

theorem binaryFormEquiv_transportedApolarVector (z : ℂ) (d : ℕ)
    (g : Fin (d + 1) → ℂ) :
    binaryFormEquiv d (transportedApolarVector z d g) =
      chartPhi z d (binaryFormEquiv d g) :=
  (binaryFormEquiv d).apply_symm_apply _

/-- Multiplication and the inverse-dual moment action commute in every
complementary degree split, including degree zero. -/
theorem chartMoment_productAt_pairing (z : ℂ) {D d : ℕ} (hd : d ≤ D)
    (L : BinaryMoment D) (G : BinaryForm d) (Q : BinaryForm (D - d)) :
    chartMoment z L
      (binaryProductAt hd (chartPhi z d G) (chartPhi z (D - d) Q)) =
      L (binaryProductAt hd G Q) := by
  have hmul : chartPhi z D (binaryProductAt hd G Q) =
      binaryProductAt hd (chartPhi z d G) (chartPhi z (D - d) Q) := by
    apply Subtype.ext
    exact (chartSubst z).map_mul G.1 Q.1
  rw [← hmul]
  exact congrArg L ((chartPhiEquiv z D).symm_apply_apply (binaryProductAt hd G Q))

/-- Every frozen apolar equation is preserved by the explicit chart, with
the moments transformed by the inverse dual and the form by the forward map. -/
theorem apolar_iff_chart_apolar (z : ℂ) {D d : ℕ} (hd : d ≤ D)
    (h : Fin (D + 1) → ℂ) (g : Fin (d + 1) → ℂ) :
    IsApolar h d hd g ↔
      IsApolar (transformedMoments z h) d hd (transportedApolarVector z d g) := by
  rw [apolar_iff_product_annihilation hd h g,
    apolar_iff_product_annihilation hd (transformedMoments z h)
      (transportedApolarVector z d g)]
  constructor
  · intro hAnn Q'
    let Q : BinaryForm (D - d) := (chartPhiEquiv z (D - d)).symm Q'
    have hQ : chartPhi z (D - d) Q = Q' :=
      (chartPhiEquiv z (D - d)).apply_symm_apply Q'
    have hpair := chartMoment_productAt_pairing z hd (homogeneousMoment h)
      (binaryFormEquiv d g) Q
    rw [homogeneousMoment_transformedMoments,
      binaryFormEquiv_transportedApolarVector, ← hQ, hpair]
    exact hAnn Q
  · intro hAnn Q
    have hpair := chartMoment_productAt_pairing z hd (homogeneousMoment h)
      (binaryFormEquiv d g) Q
    have hz := hAnn (chartPhi z (D - d) Q)
    rw [homogeneousMoment_transformedMoments,
      binaryFormEquiv_transportedApolarVector, hpair] at hz
    exact hz

/-- The coefficient substitution is an equivalence, so it preserves zero. -/
theorem transportedApolarVector_eq_zero_iff (z : ℂ) (d : ℕ)
    (g : Fin (d + 1) → ℂ) :
    transportedApolarVector z d g = 0 ↔ g = 0 := by
  constructor
  · intro hz
    have hG := congrArg (binaryFormEquiv d) hz
    simp only [binaryFormEquiv_transportedApolarVector, map_zero] at hG
    have hC : chartPhi z d (binaryFormEquiv d g) =
        chartPhi z d (0 : BinaryForm d) := by
      rw [map_zero]
      exact hG
    have hOrig : binaryFormEquiv d g = 0 :=
      (chartPhiEquiv z d).injective hC
    have hB : binaryFormEquiv d g = binaryFormEquiv d (0 : Fin (d + 1) → ℂ) := by
      rw [map_zero]
      exact hOrig
    exact (binaryFormEquiv d).injective hB
  · intro hz
    subst g
    simp [transportedApolarVector]

/-- The transformed degree-`d` apolar kernel is precisely the image of the
original kernel under the invertible coefficient chart map. -/
theorem chart_apolar_kernel_image (z : ℂ) {D d : ℕ} (hd : d ≤ D)
    (h : Fin (D + 1) → ℂ) :
    {g' : Fin (d + 1) → ℂ |
      IsApolar (transformedMoments z h) d hd g'} =
      transportedApolarVector z d ''
        {g : Fin (d + 1) → ℂ | IsApolar h d hd g} := by
  ext g'
  constructor
  · intro hg'
    obtain ⟨g, rfl⟩ := (chartCoefficientEquiv z d).surjective g'
    exact ⟨g, (apolar_iff_chart_apolar z hd h g).mpr hg', rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact (apolar_iff_chart_apolar z hd h g).mp hg

/-- In every degree `d≤D`, existence of a nonzero apolar form is chart
invariant. This preserves the full set of such degrees and hence its least
member whenever one exists. -/
theorem chart_nonzero_apolar_degree_iff (z : ℂ) {D d : ℕ} (hd : d ≤ D)
    (h : Fin (D + 1) → ℂ) :
    (∃ g : Fin (d + 1) → ℂ, g ≠ 0 ∧ IsApolar h d hd g) ↔
      (∃ g' : Fin (d + 1) → ℂ,
        g' ≠ 0 ∧ IsApolar (transformedMoments z h) d hd g') := by
  constructor
  · rintro ⟨g, hg, hAp⟩
    refine ⟨transportedApolarVector z d g, ?_,
      (apolar_iff_chart_apolar z hd h g).mp hAp⟩
    exact fun hz => hg ((transportedApolarVector_eq_zero_iff z d g).mp hz)
  · rintro ⟨g', hg', hAp'⟩
    obtain ⟨g, rfl⟩ := (chartCoefficientEquiv z d).surjective g'
    refine ⟨g, ?_,
      (apolar_iff_chart_apolar z hd h g).mpr hAp'⟩
    exact fun hz => hg' ((transportedApolarVector_eq_zero_iff z d g).mpr hz)

#assert_trust kernel transportedApolarVector
#assert_trust kernel chartCoefficientEquiv
#assert_trust kernel chartMoment_productAt_pairing
#assert_trust kernel apolar_iff_chart_apolar
#assert_trust kernel transportedApolarVector_eq_zero_iff
#assert_trust kernel chart_apolar_kernel_image
#assert_trust kernel chart_nonzero_apolar_degree_iff
#print axioms apolar_iff_chart_apolar

end
end NLA.Proofs.TR14
