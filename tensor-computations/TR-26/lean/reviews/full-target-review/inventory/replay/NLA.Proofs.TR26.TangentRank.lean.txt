import NLA.Proofs.TR26.AnalyticConormal

/-! Rank bounds use the complex bilinear coordinate pairing. No Hermitian
orthogonality is used. The two affine charts include the point at infinity. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
universe u
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem finrank_add_two_le_of_annihilates_independent
    {ι : Type u} [Fintype ι] (S : Submodule ℂ (ι → ℂ))
    (v : Fin 2 → ι → ℂ) (hv : LinearIndependent ℂ v)
    (horth : ∀ g ∈ S, ∀ j, ∑ i, g i * v j i = 0) :
    Module.finrank ℂ S + 2 ≤ Fintype.card ι := by
  let B : LinearMap.BilinForm ℂ (ι → ℂ) := dotProductBilin ℂ ℂ
  have hB : B.Nondegenerate := by
    constructor
    · intro x hx
      exact dotProduct_eq_zero x hx
    · intro y hy
      apply dotProduct_eq_zero y
      intro x
      have h := hy x
      change dotProduct x y = 0 at h
      rwa [dotProduct_comm] at h
  have hle : Submodule.span ℂ (Set.range v) ≤ B.orthogonal S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    intro g hg
    exact horth g hg j
  have hdim := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hv,Fintype.card_fin,
    LinearMap.BilinForm.finrank_orthogonal hB] at hdim
  have hbound := S.finrank_le
  simp only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,mul_one] at hdim hbound
  omega

def affineChartVector (d : ℕ) (c t : ℂ) : CurveVector d :=
  fun i => c * t ^ i.val

def affineChartVelocity (d : ℕ) (c t : ℂ) : CurveVector d :=
  fun i => c * (i.val : ℂ) * t ^ (i.val-1)

def reverseChartVector (d : ℕ) (c t : ℂ) : CurveVector d :=
  fun i => c * t ^ (d-i.val)

def reverseChartVelocity (d : ℕ) (c t : ℂ) : CurveVector d :=
  fun i => c * (d-i.val : ℕ) * t ^ (d-i.val-1)

theorem affineChart_tangents_independent (d : ℕ) (hd : 1 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) :
    LinearIndependent ℂ ![affineChartVector d c t,affineChartVelocity d c t] := by
  apply linearIndependent_fin2.mpr
  constructor
  · intro h
    have hh := congrFun h (⟨1,by omega⟩ : Index d)
    apply hc
    simpa [affineChartVelocity] using hh
  · intro a h
    have hh := congrFun h (0 : Index d)
    apply hc
    simpa [affineChartVector,affineChartVelocity] using hh.symm

theorem reverseChart_tangents_independent (d : ℕ) (hd : 1 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) :
    LinearIndependent ℂ ![reverseChartVector d c t,reverseChartVelocity d c t] := by
  apply linearIndependent_fin2.mpr
  constructor
  · intro h
    have hh := congrFun h (⟨d-1,by omega⟩ : Index d)
    have he : d-(d-1)=1 := by omega
    apply hc
    simpa [reverseChartVelocity,he] using hh
  · intro a h
    have hh := congrFun h (Fin.last d)
    apply hc
    simpa [reverseChartVector,reverseChartVelocity] using hh.symm

theorem hasDerivAt_affineChartVector (d : ℕ) (c t : ℂ) (i : Index d) :
    HasDerivAt (fun s => affineChartVector d c s i)
      (affineChartVelocity d c t i) t := by
  simpa [affineChartVector,affineChartVelocity,mul_assoc] using
    ((hasDerivAt_id t).pow i.val).const_mul c

theorem hasDerivAt_reverseChartVector (d : ℕ) (c t : ℂ) (i : Index d) :
    HasDerivAt (fun s => reverseChartVector d c s i)
      (reverseChartVelocity d c t i) t := by
  simpa [reverseChartVector,reverseChartVelocity,mul_assoc] using
    ((hasDerivAt_id t).pow (d-i.val)).const_mul c

theorem affineChartVector_onCurve (d : ℕ) (c t : ℂ) (hc : c ≠ 0) :
    OnCurve (affineChartVector d c t) := by
  exact ⟨1,t,c,Or.inl one_ne_zero,hc,by simp [affineChartVector,veronese]⟩

theorem reverseChartVector_onCurve (d : ℕ) (c t : ℂ) (hc : c ≠ 0) :
    OnCurve (reverseChartVector d c t) := by
  exact ⟨t,1,c,Or.inr one_ne_zero,hc,by simp [reverseChartVector,veronese]⟩

#assert_trust kernel finrank_add_two_le_of_annihilates_independent
#assert_trust kernel affineChart_tangents_independent
#assert_trust kernel reverseChart_tangents_independent
#assert_trust kernel hasDerivAt_affineChartVector
#assert_trust kernel hasDerivAt_reverseChartVector
#assert_trust kernel affineChartVector_onCurve
#assert_trust kernel reverseChartVector_onCurve
#print axioms finrank_add_two_le_of_annihilates_independent
#print axioms affineChart_tangents_independent
end NLA.Proofs.TR26
