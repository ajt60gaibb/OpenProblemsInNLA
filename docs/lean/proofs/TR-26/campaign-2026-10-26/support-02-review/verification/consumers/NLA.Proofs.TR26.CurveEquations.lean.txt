import NLA.Proofs.TR26.TangentRank
import NLA.Proofs.TR26.IncidenceIdeal

/-! Global equations of the exact unweighted rational normal curve. They
vanish on the entire cone, including its omitted affine-chart endpoint. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26 MvPolynomial

def chartFirstIndex (d : ℕ) (hd : 1 ≤ d) : Index d := ⟨1,by omega⟩

def affineCurveEquation (d : ℕ) (hd : 1 ≤ d) (i : Index d) : IncidenceRing d :=
  X (.inl i) * X (.inl (0 : Index d)) ^ (i.val-1) -
    X (.inl (chartFirstIndex d hd)) ^ i.val

theorem affineCurveEquation_eval (d : ℕ) (hd : 1 ≤ d) (i : Index d)
    (z : CurveVector d) (H : Parameter d) :
    eval (incidenceCoordinates z H) (affineCurveEquation d hd i) =
      z i * z 0 ^ (i.val-1) - z (chartFirstIndex d hd) ^ i.val := by
  simp [affineCurveEquation,incidenceCoordinates]

theorem affineCurveEquation_vanishes_onCurve (d : ℕ) (hd : 1 ≤ d)
    (i : Index d) (hi : 1 ≤ i.val) (z : CurveVector d) (H : Parameter d)
    (hz : OnCurve z) :
    eval (incidenceCoordinates z H) (affineCurveEquation d hd i) = 0 := by
  rw [affineCurveEquation_eval]
  rcases hz with ⟨a,b,c,_,_,hz⟩
  simp only [hz,veronese,Fin.val_zero,Nat.sub_zero,pow_zero,mul_one,chartFirstIndex]
  have hiD : i.val ≤ d := by omega
  have hexp : d-i.val + d*(i.val-1) = (d-1)*i.val := by
    have h1 : d-i.val+i.val=d := Nat.sub_add_cancel hiD
    have h2 : i.val-1+1=i.val := Nat.sub_add_cancel hi
    have h3 : d-1+1=d := Nat.sub_add_cancel hd
    nlinarith
  apply sub_eq_zero.mpr
  rw [mul_pow,mul_pow,mul_pow,← pow_mul,← pow_mul]
  calc
    _ = (c*c^(i.val-1)) * (a^(d-i.val)*a^(d*(i.val-1))) * b^i.val := by ring
    _ = _ := by
      rw [← pow_succ',Nat.sub_add_cancel hi,← pow_add,hexp]
      simp [mul_assoc]

theorem affineCurveEquation_mem_openVanishingIdeal (d : ℕ) (hd : 1 ≤ d)
    (i : Index d) (hi : 1 ≤ i.val) :
    affineCurveEquation d hd i ∈ openVanishingIdeal d := by
  apply (mem_openVanishingIdeal_iff d _).mpr
  intro z H hcrit
  exact affineCurveEquation_vanishes_onCurve d hd i hi z H (openCritical_onCurve hcrit)

#assert_trust kernel affineCurveEquation_eval
#assert_trust kernel affineCurveEquation_vanishes_onCurve
#assert_trust kernel affineCurveEquation_mem_openVanishingIdeal
#print axioms affineCurveEquation_vanishes_onCurve
end NLA.Proofs.TR26
