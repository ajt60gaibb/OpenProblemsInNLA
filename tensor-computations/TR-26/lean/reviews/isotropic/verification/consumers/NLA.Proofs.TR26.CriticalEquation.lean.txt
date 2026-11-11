import NLA.Proofs.TR26.BinaryScaling
import NLA.Proofs.TR26.CurveEquations
import NLA.Proofs.TR26.FamilyDiscriminantEvaluation

/-! Global polynomial witnesses in the full incidence ideal. Their
coefficients remain the actual symmetric-matrix variables, rather than
being frozen at a particular matrix. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26 MvPolynomial

def binaryParameterIncidence (d : ℕ) (i j : Index d)
    (P : BinaryForm (ParameterRing d)) : IncidenceRing d :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.rename (Sum.inr : SymIndex d → IncidenceVariable d)).toRingHom
    ![MvPolynomial.X (.inl i),MvPolynomial.X (.inl j)] P

theorem eval_binaryParameterIncidence (d : ℕ) (i j : Index d)
    (P : BinaryForm (ParameterRing d)) (z : CurveVector d) (H : Parameter d) :
    MvPolynomial.eval (incidenceCoordinates z H) (binaryParameterIncidence d i j P) =
      binaryEval (MvPolynomial.map (MvPolynomial.eval H) P) (z i) (z j) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp [binaryParameterIncidence,binaryEvalOver,MvPolynomial.eval_rename,
        incidenceCoordinates,Function.comp_def]
  | add P Q hP hQ =>
      simp only [binaryParameterIncidence,map_add] at *
      simp only [binaryEvalOver,map_add] at *
      rw [hP,hQ]
  | mul_X P k hP =>
      simp only [binaryParameterIncidence,map_mul,MvPolynomial.eval₂Hom_X',
        MvPolynomial.map_X] at *
      simp only [binaryEvalOver,map_mul,MvPolynomial.eval_X] at *
      rw [hP]
      fin_cases k <;> simp [incidenceCoordinates]

def affineCriticalEquation (d : ℕ) (hd : 1 ≤ d) : IncidenceRing d :=
  binaryParameterIncidence d 0 (chartFirstIndex d hd)
    (binaryWronskianOver (fun ij : SymIndex d => MvPolynomial.X ij : SymIndex d → ParameterRing d))

def chartPenultimateIndex (d : ℕ) (hd : 1 ≤ d) : Index d := ⟨d-1,by omega⟩

def reverseCriticalEquation (d : ℕ) (hd : 1 ≤ d) : IncidenceRing d :=
  binaryParameterIncidence d (chartPenultimateIndex d hd) (Fin.last d)
    (binaryWronskianOver (fun ij : SymIndex d => MvPolynomial.X ij : SymIndex d → ParameterRing d))

theorem affineCriticalEquation_eval (d : ℕ) (hd : 1 ≤ d)
    (z : CurveVector d) (H : Parameter d) :
    eval (incidenceCoordinates z H) (affineCriticalEquation d hd) =
      binaryEval (binaryWronskian H) (z 0) (z (chartFirstIndex d hd)) := by
  rw [affineCriticalEquation,eval_binaryParameterIncidence,map_parameter_binaryWronskian]

theorem reverseCriticalEquation_eval (d : ℕ) (hd : 1 ≤ d)
    (z : CurveVector d) (H : Parameter d) :
    eval (incidenceCoordinates z H) (reverseCriticalEquation d hd) =
      binaryEval (binaryWronskian H) (z (chartPenultimateIndex d hd)) (z (Fin.last d)) := by
  rw [reverseCriticalEquation,eval_binaryParameterIncidence,map_parameter_binaryWronskian]

theorem affineCriticalEquation_mem_openVanishingIdeal (d : ℕ) (hd : 1 ≤ d) :
    affineCriticalEquation d hd ∈ openVanishingIdeal d := by
  apply (mem_openVanishingIdeal_iff d _).mpr
  intro z H hcrit
  rw [affineCriticalEquation_eval]
  rcases hcrit with ⟨_,a,b,c,hab,_,hz,_,hDa,hDb⟩
  have hW := (parameterCritical_iff (by omega : 0 < d) H hab).mp ⟨hDa,hDb⟩
  have h0 : z 0 = (c*a^(d-1))*a := by
    rw [hz 0]
    simp only [veronese,Fin.val_zero,Nat.sub_zero,pow_zero,mul_one]
    rw [mul_assoc,← pow_succ,Nat.sub_add_cancel hd]
  have h1 : z (chartFirstIndex d hd) = (c*a^(d-1))*b := by
    rw [hz]
    simp [veronese,chartFirstIndex,mul_assoc]
  rw [h0,h1,binaryEval_homogeneous_smul (4*d-2) _
    (binaryWronskianOver_homogeneous H),hW,mul_zero]

theorem reverseCriticalEquation_mem_openVanishingIdeal (d : ℕ) (hd : 1 ≤ d) :
    reverseCriticalEquation d hd ∈ openVanishingIdeal d := by
  apply (mem_openVanishingIdeal_iff d _).mpr
  intro z H hcrit
  rw [reverseCriticalEquation_eval]
  rcases hcrit with ⟨_,a,b,c,hab,_,hz,_,hDa,hDb⟩
  have hW := (parameterCritical_iff (by omega : 0 < d) H hab).mp ⟨hDa,hDb⟩
  have he : d-(d-1)=1 := by omega
  have h0 : z (chartPenultimateIndex d hd) = (c*b^(d-1))*a := by
    rw [hz]
    simp only [veronese,chartPenultimateIndex,he,pow_one]
    ring
  have h1 : z (Fin.last d) = (c*b^(d-1))*b := by
    rw [hz]
    simp only [veronese,Fin.val_last,Nat.sub_self,pow_zero,one_mul]
    rw [mul_assoc,← pow_succ,Nat.sub_add_cancel hd]
  rw [h0,h1,binaryEval_homogeneous_smul (4*d-2) _
    (binaryWronskianOver_homogeneous H),hW,mul_zero]

theorem affineCriticalEquation_affine_eval (d : ℕ) (hd : 1 ≤ d)
    (c t : ℂ) (H : Parameter d) :
    eval (incidenceCoordinates (affineChartVector d c t) H) (affineCriticalEquation d hd) =
      c^(4*d-2) * (affineWronskian H).eval t := by
  rw [affineCriticalEquation_eval]
  simp only [affineChartVector,Fin.val_zero,pow_zero,mul_one,chartFirstIndex,pow_one]
  calc
    _ = c^(4*d-2) * binaryEval (binaryWronskian H) 1 t := by
      simpa only [mul_one] using binaryEval_homogeneous_smul (4*d-2)
        (binaryWronskian H) (binaryWronskianOver_homogeneous H) 1 t c
    _ = _ := by rw [binaryWronskian_affine_eval (by omega : 0 < d)]

theorem incidence_affine_wrRoot (d : ℕ) (hd : 1 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d)
    (hI : Incidence d (affineChartVector d c t) H) :
    (affineWronskian H).eval t = 0 := by
  have hh := hI.2.2.2 (affineCriticalEquation d hd)
    ((mem_openVanishingIdeal_iff d _).mp (affineCriticalEquation_mem_openVanishingIdeal d hd))
  rw [affineCriticalEquation_affine_eval] at hh
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ hc)

#assert_trust kernel eval_binaryParameterIncidence
#assert_trust kernel affineCriticalEquation_eval
#assert_trust kernel reverseCriticalEquation_eval
#assert_trust kernel affineCriticalEquation_mem_openVanishingIdeal
#assert_trust kernel reverseCriticalEquation_mem_openVanishingIdeal
#assert_trust kernel affineCriticalEquation_affine_eval
#assert_trust kernel incidence_affine_wrRoot
#print axioms affineCriticalEquation_mem_openVanishingIdeal
#print axioms incidence_affine_wrRoot
end NLA.Proofs.TR26
