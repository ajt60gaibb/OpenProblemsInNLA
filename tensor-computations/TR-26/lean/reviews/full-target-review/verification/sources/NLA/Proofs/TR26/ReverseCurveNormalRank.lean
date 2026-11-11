import NLA.Proofs.TR26.CurveDifferentiation

/-! Actual global curve equations and d−1 independent normals in the second
projective chart. The proof uses the full retained incidence ideal. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR26
open NLA.Statements.TR26 MvPolynomial

def reverseCurveEquation (d : ℕ) (hd : 1 ≤ d) (i : Index d) : IncidenceRing d :=
  X (.inl i) * X (.inl (Fin.last d)) ^ (d-i.val-1) -
    X (.inl (⟨d-1,by omega⟩ : Index d)) ^ (d-i.val)

theorem reverseCurveEquation_eval (d : ℕ) (hd : 1 ≤ d) (i : Index d)
    (z : CurveVector d) (H : Parameter d) :
    eval (incidenceCoordinates z H) (reverseCurveEquation d hd i) =
      z i * z (Fin.last d) ^ (d-i.val-1) -
        z (⟨d-1,by omega⟩ : Index d) ^ (d-i.val) := by
  simp [reverseCurveEquation,incidenceCoordinates]

theorem reverseCurveEquation_vanishes_onCurve (d : ℕ) (hd : 1 ≤ d)
    (i : Index d) (hi : i.val < d) (z : CurveVector d) (H : Parameter d)
    (hz : OnCurve z) :
    eval (incidenceCoordinates z H) (reverseCurveEquation d hd i) = 0 := by
  rw [reverseCurveEquation_eval]
  rcases hz with ⟨a,b,c,_,_,hz⟩
  have he : d-(d-1)=1 := by omega
  simp only [hz,veronese,Fin.val_last,Nat.sub_self,pow_zero,one_mul,he,pow_one]
  have hexp : i.val+d*(d-i.val-1) = (d-1)*(d-i.val) := by
    have h1 : d-i.val+i.val=d := Nat.sub_add_cancel (by omega)
    have h2 : d-i.val-1+1=d-i.val := Nat.sub_add_cancel (by omega)
    have h3 : d-1+1=d := Nat.sub_add_cancel hd
    nlinarith
  apply sub_eq_zero.mpr
  rw [mul_pow,mul_pow,mul_pow,← pow_mul,← pow_mul]
  calc
    _ = (c*c^(d-i.val-1)) * a^(d-i.val) * (b^i.val*b^(d*(d-i.val-1))) := by ring
    _ = _ := by
      rw [← pow_succ',Nat.sub_add_cancel (by omega : 1 ≤ d-i.val),← pow_add,hexp]
      simp [mul_assoc]

theorem reverseCurveEquation_mem_openVanishingIdeal (d : ℕ) (hd : 1 ≤ d)
    (i : Index d) (hi : i.val < d) : reverseCurveEquation d hd i ∈ openVanishingIdeal d := by
  apply (mem_openVanishingIdeal_iff d _).mpr
  intro z H hcrit
  exact reverseCurveEquation_vanishes_onCurve d hd i hi z H (openCritical_onCurve hcrit)

def reverseNormalCurveIndex (d : ℕ) (hd : 1 ≤ d) (k : Fin (d-1)) : Index d :=
  ⟨d-(k.val+2),by omega⟩

theorem reverseNormalCurveIndex_injective (d : ℕ) (hd : 1 ≤ d) :
    Function.Injective (reverseNormalCurveIndex d hd) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  simp only [reverseNormalCurveIndex] at h
  have hi := i.isLt
  have hj := j.isLt
  omega

theorem partialGradient_reverseCurveEquation_tail
    (d : ℕ) (hd : 1 ≤ d) (i j : Index d) (hj : j.val+2 ≤ d)
    (z : CurveVector d) (H : Parameter d) :
    partialGradient (Sum.inl : Index d → IncidenceVariable d)
      (incidenceCoordinates z H) (reverseCurveEquation d hd i) j =
      if i=j then z (Fin.last d) ^ (d-i.val-1) else 0 := by
  classical
  have hj0 : j ≠ Fin.last d := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_last] at hv
    omega
  have hj1 : j ≠ (⟨d-1,by omega⟩ : Index d) := by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega
  by_cases hij : i=j <;>
    simp [partialGradient,reverseCurveEquation,MvPolynomial.pderiv_X,
      hj0,hj1,hij,eq_comm,incidenceCoordinates]

def reverseNormalVector (d : ℕ) (hd : 1 ≤ d) (z : CurveVector d) (H : Parameter d)
    (k : Fin (d-1)) : CurveVector d :=
  partialGradient (Sum.inl : Index d → IncidenceVariable d)
    (incidenceCoordinates z H) (reverseCurveEquation d hd (reverseNormalCurveIndex d hd k))

theorem reverseNormalVector_tail (d : ℕ) (hd : 1 ≤ d)
    (z : CurveVector d) (H : Parameter d) (k l : Fin (d-1)) :
    reverseNormalVector d hd z H k (reverseNormalCurveIndex d hd l) =
      if k=l then z (Fin.last d) ^ (k.val+1) else 0 := by
  rw [reverseNormalVector,partialGradient_reverseCurveEquation_tail d hd _ _ (by
    simp only [reverseNormalCurveIndex]; have := l.isLt; omega)]
  have he : d-(reverseNormalCurveIndex d hd k).val-1 = k.val+1 := by
    simp only [reverseNormalCurveIndex]
    have := k.isLt
    omega
  rw [he]
  congr 1
  exact propext (reverseNormalCurveIndex_injective d hd).eq_iff

theorem reverseNormalVectors_independent (d : ℕ) (hd : 1 ≤ d)
    (z : CurveVector d) (H : Parameter d) (hz : z (Fin.last d) ≠ 0) :
    LinearIndependent ℂ (reverseNormalVector d hd z H) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha k
  have hh := congrFun ha (reverseNormalCurveIndex d hd k)
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,
    reverseNormalVector_tail] at hh
  have he : a k * z (Fin.last d) ^ (k.val+1) = 0 := by simpa [mul_ite] using hh
  exact (mul_eq_zero.mp he).resolve_right (pow_ne_zero _ hz)

theorem reverseNormalVector_mem_jacobianSpace (d : ℕ) (hd : 1 ≤ d)
    (z : CurveVector d) (H : Parameter d) (k : Fin (d-1)) :
    reverseNormalVector d hd z H k ∈ JacobianSpace d z H := by
  rw [jacobianSpace_eq_conormal]
  apply gradient_mem_conormal
  exact reverseCurveEquation_mem_openVanishingIdeal d hd _ (by
    simp only [reverseNormalCurveIndex]; have := k.isLt; omega)

theorem reverseNormalVector_tangent_pairing (d : ℕ) (hd : 1 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d) (k : Fin (d-1)) :
    ∑ i, reverseNormalVector d hd (reverseChartVector d c t) H k i *
      reverseChartVelocity d c t i = 0 := by
  apply gradient_annihilates_of_eval_identically_zero
    (reverseCurveEquation d hd (reverseNormalCurveIndex d hd k)) (reverseChartVector d c) H
    (reverseChartVelocity d c t) t (hasDerivAt_reverseChartVector d c t)
  intro s
  exact reverseCurveEquation_vanishes_onCurve d hd _ (by
    simp only [reverseNormalCurveIndex]; have := k.isLt; omega)
    _ H (reverseChartVector_onCurve d c s hc)

#assert_trust kernel reverseCurveEquation_vanishes_onCurve
#assert_trust kernel reverseNormalVector_tail
#assert_trust kernel reverseNormalVectors_independent
#assert_trust kernel reverseNormalVector_mem_jacobianSpace
#assert_trust kernel reverseNormalVector_tangent_pairing
#print axioms reverseNormalVectors_independent
#print axioms reverseNormalVector_tangent_pairing
end NLA.Proofs.TR26
