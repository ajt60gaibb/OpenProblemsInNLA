import NLA.Proofs.TR26.Denominator
import NLA.Proofs.TR26.Numerator

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem binaryVeroneseOver_homogeneous (R : Type*) [CommSemiring R] (d : ℕ)
    (i : Index d) : (binaryVeroneseOver R d i).IsHomogeneous d := by
  have h := ((MvPolynomial.isHomogeneous_X (R := R) (0 : Fin 2)).pow (d-i.val)).mul
    ((MvPolynomial.isHomogeneous_X (R := R) (1 : Fin 2)).pow i.val)
  have hi : d-i.val+i.val = d := Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt)
  simpa only [binaryVeroneseOver, one_mul, hi] using h

theorem binaryDenominatorOver_homogeneous (R : Type*) [CommSemiring R] (d : ℕ) :
    (binaryDenominatorOver R d).IsHomogeneous (2*d) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  simpa only [two_mul] using (binaryVeroneseOver_homogeneous R d i).mul
    (binaryVeroneseOver_homogeneous R d i)

theorem binaryNumeratorOver_homogeneous {R : Type*} [CommSemiring R] {d : ℕ}
    (H : SymIndex d → R) : (binaryNumeratorOver H).IsHomogeneous (2*d) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  have h := ((binaryVeroneseOver_homogeneous R d i).mul
    (binaryVeroneseOver_homogeneous R d j)).C_mul (coordinateEntry H i j)
  simpa only [two_mul, mul_assoc] using h

theorem binaryWronskianOver_homogeneous {R : Type*} [CommRing R] [Algebra ℂ R]
    {d : ℕ} (H : SymIndex d → R) :
    (binaryWronskianOver H).IsHomogeneous (4*d-2) := by
  have hN := binaryNumeratorOver_homogeneous H
  have hD := binaryDenominatorOver_homogeneous R d
  have h := (((hN.pderiv (i := 1)).mul (hD.pderiv (i := 0))).sub
    ((hN.pderiv (i := 0)).mul (hD.pderiv (i := 1)))).C_mul
    (algebraMap ℂ R ((2*d : ℂ)⁻¹))
  have hn : (2*d-1)+(2*d-1) = 4*d-2 := by omega
  simpa only [binaryWronskianOver, hn] using h

theorem binary_homogeneous_reconstruct {R : Type*} [CommSemiring R] {k : ℕ}
    (P : BinaryForm R) (hP : P.IsHomogeneous k) :
    P = ∑ i : Fin (k+1), MvPolynomial.C (binaryCoeff k P i) *
      MvPolynomial.X 0^(k-i.val)*MvPolynomial.X 1^i.val := by
  classical
  have hmono (i : Fin (k+1)) :
      MvPolynomial.C (binaryCoeff k P i)*MvPolynomial.X (0 : Fin 2)^(k-i.val)*MvPolynomial.X 1^i.val =
      MvPolynomial.monomial (Finsupp.single 0 (k-i.val)+Finsupp.single 1 i.val)
        (binaryCoeff k P i) := by
    rw [MvPolynomial.C_mul_X_pow_eq_monomial, ← MvPolynomial.monomial_add_single]
  simp_rw [hmono]
  ext s
  simp only [MvPolynomial.coeff_sum]
  have hsdeg : s.degree = s 0+s 1 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  by_cases hs : s.degree = k
  · let i : Fin (k+1) := ⟨s 1, by omega⟩
    have hexp : Finsupp.single 0 (k-i.val)+Finsupp.single 1 i.val = s := by
      ext j
      fin_cases j <;> simp [i] <;> omega
    rw [Finset.sum_eq_single i]
    · rw [MvPolynomial.coeff_monomial, if_pos hexp]
      change MvPolynomial.coeff s P = MvPolynomial.coeff
        (Finsupp.single 0 (k-i.val)+Finsupp.single 1 i.val) P
      rw [hexp]
    · intro j _ hji
      have hne : Finsupp.single 0 (k-j.val)+Finsupp.single 1 j.val ≠ s := by
        intro he
        have h1 := congrArg (fun e : Fin 2 →₀ ℕ => e 1) he
        simp only [Finsupp.add_apply, Finsupp.single_apply, Fin.zero_ne_one,
          ↓reduceIte, zero_add] at h1
        apply hji
        exact Fin.ext h1
      rw [MvPolynomial.coeff_monomial, if_neg hne]
    · simp
  · rw [hP.coeff_eq_zero hs]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hne : Finsupp.single 0 (k-i.val)+Finsupp.single 1 i.val ≠ s := by
      intro he
      have hdeg := congrArg Finsupp.degree he
      have hideg : (Finsupp.single (0 : Fin 2) (k-i.val)+Finsupp.single 1 i.val).degree = k := by
        rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
        simp
        omega
      rw [hideg] at hdeg
      exact hs hdeg.symm
    rw [MvPolynomial.coeff_monomial, if_neg hne]

theorem binaryWronskianOver_reconstruct {R : Type*} [CommRing R] [Algebra ℂ R]
    {d : ℕ} (H : SymIndex d → R) :
    binaryWronskianOver H = ∑ i : Fin (4*d-2+1),
      MvPolynomial.C (wronskianCoefficientsOver H i)*
        MvPolynomial.X 0^(4*d-2-i.val)*MvPolynomial.X 1^i.val :=
  binary_homogeneous_reconstruct _ (binaryWronskianOver_homogeneous H)

theorem binaryVeroneseDa_eval (d : ℕ) (i : Index d) (a b : ℂ) :
    binaryEval (MvPolynomial.pderiv 0 (binaryVeroneseOver ℂ d i)) a b =
      veroneseDa d a b i := by
  simp [binaryEvalOver, binaryVeroneseOver, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, veroneseDa, mul_comm, mul_left_comm, mul_assoc]

theorem binaryVeroneseDb_eval (d : ℕ) (i : Index d) (a b : ℂ) :
    binaryEval (MvPolynomial.pderiv 1 (binaryVeroneseOver ℂ d i)) a b =
      veroneseDb d a b i := by
  simp [binaryEvalOver, binaryVeroneseOver, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, veroneseDb, mul_comm, mul_left_comm, mul_assoc]

theorem binaryDenominatorDa_eval (d : ℕ) (a b : ℂ) :
    binaryEval (MvPolynomial.pderiv 0 (binaryDenominator d)) a b =
      denominatorDerivative (veronese d a b) (veroneseDa d a b) := by
  simp only [binaryEvalOver, binaryDenominatorOver, denominatorDerivative,
    map_sum, MvPolynomial.pderiv_mul, map_add, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  change binaryEval (MvPolynomial.pderiv 0 (binaryVeroneseOver ℂ d i)) a b *
      binaryEval (binaryVeroneseOver ℂ d i) a b +
    binaryEval (binaryVeroneseOver ℂ d i) a b *
      binaryEval (MvPolynomial.pderiv 0 (binaryVeroneseOver ℂ d i)) a b = _
  rw [binaryVeronese_eval, binaryVeroneseDa_eval]

theorem binaryDenominatorDb_eval (d : ℕ) (a b : ℂ) :
    binaryEval (MvPolynomial.pderiv 1 (binaryDenominator d)) a b =
      denominatorDerivative (veronese d a b) (veroneseDb d a b) := by
  simp only [binaryEvalOver, binaryDenominatorOver, denominatorDerivative,
    map_sum, MvPolynomial.pderiv_mul, map_add, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  change binaryEval (MvPolynomial.pderiv 1 (binaryVeroneseOver ℂ d i)) a b *
      binaryEval (binaryVeroneseOver ℂ d i) a b +
    binaryEval (binaryVeroneseOver ℂ d i) a b *
      binaryEval (MvPolynomial.pderiv 1 (binaryVeroneseOver ℂ d i)) a b = _
  rw [binaryVeronese_eval, binaryVeroneseDb_eval]

theorem binaryNumeratorDa_eval {d : ℕ} (H : Parameter d) (a b : ℂ) :
    binaryEval (MvPolynomial.pderiv 0 (binaryNumerator H)) a b =
      numeratorDerivative H (veronese d a b) (veroneseDa d a b) := by
  simp only [binaryEvalOver, binaryNumeratorOver, numeratorDerivative, map_sum,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add,
    map_add, map_mul, MvPolynomial.eval_C]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change coordinateEntry H i j *
      binaryEval (MvPolynomial.pderiv 0 (binaryVeroneseOver ℂ d i)) a b *
      binaryEval (binaryVeroneseOver ℂ d j) a b +
    coordinateEntry H i j * binaryEval (binaryVeroneseOver ℂ d i) a b *
      binaryEval (MvPolynomial.pderiv 0 (binaryVeroneseOver ℂ d j)) a b = _
  rw [binaryVeroneseDa_eval, binaryVeronese_eval, binaryVeronese_eval,
    binaryVeroneseDa_eval, coordinateEntry_eq]
  ring

theorem binaryNumeratorDb_eval {d : ℕ} (H : Parameter d) (a b : ℂ) :
    binaryEval (MvPolynomial.pderiv 1 (binaryNumerator H)) a b =
      numeratorDerivative H (veronese d a b) (veroneseDb d a b) := by
  simp only [binaryEvalOver, binaryNumeratorOver, numeratorDerivative, map_sum,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add,
    map_add, map_mul, MvPolynomial.eval_C]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change coordinateEntry H i j *
      binaryEval (MvPolynomial.pderiv 1 (binaryVeroneseOver ℂ d i)) a b *
      binaryEval (binaryVeroneseOver ℂ d j) a b +
    coordinateEntry H i j * binaryEval (binaryVeroneseOver ℂ d i) a b *
      binaryEval (MvPolynomial.pderiv 1 (binaryVeroneseOver ℂ d j)) a b = _
  rw [binaryVeroneseDb_eval, binaryVeronese_eval, binaryVeronese_eval,
    binaryVeroneseDb_eval, coordinateEntry_eq]
  ring

theorem binary_euler_eval {k : ℕ} (P : BinaryForm ℂ) (hP : P.IsHomogeneous k)
    (a b : ℂ) :
    a * binaryEval (MvPolynomial.pderiv 0 P) a b +
      b * binaryEval (MvPolynomial.pderiv 1 P) a b = (k : ℂ)*binaryEval P a b := by
  have h := congrArg (fun Q => binaryEval Q a b) hP.sum_X_mul_pderiv
  simpa only [binaryEvalOver, Fin.sum_univ_two, map_add, map_mul,
    MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, map_nsmul, nsmul_eq_mul, map_natCast] using h

theorem binaryWronskian_eval {d : ℕ} (H : Parameter d) (a b : ℂ) :
    binaryEval (binaryWronskian H) a b = (2*d : ℂ)⁻¹ *
      (numeratorDerivative H (veronese d a b) (veroneseDb d a b) *
          denominatorDerivative (veronese d a b) (veroneseDa d a b) -
        numeratorDerivative H (veronese d a b) (veroneseDa d a b) *
          denominatorDerivative (veronese d a b) (veroneseDb d a b)) := by
  change (MvPolynomial.eval ![a,b]) (binaryWronskianOver H) = _
  simp only [binaryWronskianOver, map_mul, map_sub, MvPolynomial.eval_C,
    Algebra.algebraMap_self, RingHom.id_apply]
  change (2*d : ℂ)⁻¹ *
    (binaryEval (MvPolynomial.pderiv 1 (binaryNumerator H)) a b *
        binaryEval (MvPolynomial.pderiv 0 (binaryDenominator d)) a b -
      binaryEval (MvPolynomial.pderiv 0 (binaryNumerator H)) a b *
        binaryEval (MvPolynomial.pderiv 1 (binaryDenominator d)) a b) = _
  rw [binaryNumeratorDb_eval, binaryDenominatorDa_eval,
    binaryNumeratorDa_eval, binaryDenominatorDb_eval]

theorem quotientDerivativeNumerator_Da {d : ℕ} (hd : 0 < d) (H : Parameter d)
    (a b : ℂ) :
    quotientDerivativeNumerator H (veronese d a b) (veroneseDa d a b) =
      -b * binaryEval (binaryWronskian H) a b := by
  have hN := binary_euler_eval (binaryNumerator H) (binaryNumeratorOver_homogeneous H) a b
  have hD := binary_euler_eval (binaryDenominator d) (binaryDenominatorOver_homogeneous ℂ d) a b
  rw [binaryNumeratorDa_eval, binaryNumeratorDb_eval, binaryNumerator_eval] at hN
  rw [binaryDenominatorDa_eval, binaryDenominatorDb_eval, binaryDenominator_eval] at hD
  push_cast at hN hD
  have hm : (2*d : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2*d ≠ 0)
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [binaryWronskian_eval]
  unfold quotientDerivativeNumerator
  apply mul_left_cancel₀ hm
  calc
    _ = -b *
        (numeratorDerivative H (veronese d a b) (veroneseDb d a b) *
            denominatorDerivative (veronese d a b) (veroneseDa d a b) -
          numeratorDerivative H (veronese d a b) (veroneseDa d a b) *
            denominatorDerivative (veronese d a b) (veroneseDb d a b)) := by
      linear_combination
        (denominatorDerivative (veronese d a b) (veroneseDa d a b))*hN -
          (numeratorDerivative H (veronese d a b) (veroneseDa d a b))*hD
    _ = _ := by field_simp [hm, hdC]

theorem quotientDerivativeNumerator_Db {d : ℕ} (hd : 0 < d) (H : Parameter d)
    (a b : ℂ) :
    quotientDerivativeNumerator H (veronese d a b) (veroneseDb d a b) =
      a * binaryEval (binaryWronskian H) a b := by
  have hN := binary_euler_eval (binaryNumerator H) (binaryNumeratorOver_homogeneous H) a b
  have hD := binary_euler_eval (binaryDenominator d) (binaryDenominatorOver_homogeneous ℂ d) a b
  rw [binaryNumeratorDa_eval, binaryNumeratorDb_eval, binaryNumerator_eval] at hN
  rw [binaryDenominatorDa_eval, binaryDenominatorDb_eval, binaryDenominator_eval] at hD
  push_cast at hN hD
  have hm : (2*d : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2*d ≠ 0)
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [binaryWronskian_eval]
  unfold quotientDerivativeNumerator
  apply mul_left_cancel₀ hm
  calc
    _ = a *
        (numeratorDerivative H (veronese d a b) (veroneseDb d a b) *
            denominatorDerivative (veronese d a b) (veroneseDa d a b) -
          numeratorDerivative H (veronese d a b) (veroneseDa d a b) *
            denominatorDerivative (veronese d a b) (veroneseDb d a b)) := by
      linear_combination
        (denominatorDerivative (veronese d a b) (veroneseDb d a b))*hN -
          (numeratorDerivative H (veronese d a b) (veroneseDb d a b))*hD
    _ = _ := by field_simp [hm, hdC]

theorem parameterCritical_iff {d : ℕ} (hd : 0 < d) (H : Parameter d)
    {a b : ℂ} (hab : a ≠ 0 ∨ b ≠ 0) :
    (quotientDerivativeNumerator H (veronese d a b) (veroneseDa d a b) = 0 ∧
      quotientDerivativeNumerator H (veronese d a b) (veroneseDb d a b) = 0) ↔
      binaryEval (binaryWronskian H) a b = 0 := by
  rw [quotientDerivativeNumerator_Da hd, quotientDerivativeNumerator_Db hd]
  constructor
  · rintro ⟨ha,hb⟩
    rcases hab with ha0 | hb0
    · exact (mul_eq_zero.mp hb).resolve_left ha0
    · exact (mul_eq_zero.mp ha).resolve_left (neg_ne_zero.mpr hb0)
  · intro h
    simp [h]

def binaryDehomogenizeOver (R : Type*) [CommSemiring R] :
    BinaryForm R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C ![1, Polynomial.X]

theorem binaryDehomogenize_pderiv_b {R : Type*} [CommSemiring R] (P : BinaryForm R) :
    binaryDehomogenizeOver R (MvPolynomial.pderiv 1 P) =
      (binaryDehomogenizeOver R P).derivative := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [binaryDehomogenizeOver]
  | add P Q hP hQ => simp only [map_add, Polynomial.derivative_add, hP, hQ]
  | mul_X P i hP =>
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, Polynomial.derivative_mul, hP]
    fin_cases i <;> simp [binaryDehomogenizeOver]

theorem binaryDehomogenize_denominator (R : Type*) [CommSemiring R] (d : ℕ) :
    binaryDehomogenizeOver R (binaryDenominatorOver R d) = affineDenominatorOver R d := by
  simp [binaryDehomogenizeOver, binaryDenominatorOver, binaryVeroneseOver,
    affineDenominatorOver, pow_add, two_mul]

theorem binaryDehomogenize_numerator {R : Type*} [CommSemiring R] {d : ℕ}
    (H : SymIndex d → R) :
    binaryDehomogenizeOver R (binaryNumeratorOver H) = affineNumeratorOver H := by
  simp [binaryDehomogenizeOver, binaryNumeratorOver, binaryVeroneseOver,
    affineNumeratorOver, pow_add, mul_assoc]

theorem binaryDehomogenize_eval (P : BinaryForm ℂ) (t : ℂ) :
    (binaryDehomogenizeOver ℂ P).eval t = binaryEval P 1 t := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [binaryDehomogenizeOver, binaryEvalOver]
  | add P Q hP hQ => simp only [map_add, Polynomial.eval_add, binaryEvalOver] at *; rw [hP,hQ]
  | mul_X P i hP =>
    fin_cases i
    · simpa [binaryDehomogenizeOver, binaryEvalOver] using hP
    · simpa [binaryDehomogenizeOver, binaryEvalOver] using congrArg (fun z => z*t) hP

theorem binaryDehomogenize_pderiv_a {R : Type*} [CommRing R] {k : ℕ}
    (P : BinaryForm R) (hP : P.IsHomogeneous k) :
    binaryDehomogenizeOver R (MvPolynomial.pderiv 0 P) =
      Polynomial.C (k : R)*binaryDehomogenizeOver R P -
        Polynomial.X*(binaryDehomogenizeOver R P).derivative := by
  have h := congrArg (binaryDehomogenizeOver R) hP.sum_X_mul_pderiv
  simp only [Fin.sum_univ_two, map_add, map_mul, map_nsmul,
    binaryDehomogenizeOver, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul] at h
  change binaryDehomogenizeOver R (MvPolynomial.pderiv 0 P) +
      Polynomial.X*binaryDehomogenizeOver R (MvPolynomial.pderiv 1 P) =
    k • binaryDehomogenizeOver R P at h
  rw [binaryDehomogenize_pderiv_b] at h
  simpa only [nsmul_eq_mul, Polynomial.C_eq_natCast] using eq_sub_of_add_eq h

theorem binaryDehomogenize_wronskian {R : Type*} [CommRing R] [Algebra ℂ R]
    {d : ℕ} (hd : 0 < d) (H : SymIndex d → R) :
    binaryDehomogenizeOver R (binaryWronskianOver H) = affineWronskianOver H := by
  have hm : (2*d : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2*d ≠ 0)
  have hc : Polynomial.C (algebraMap ℂ R ((2*d : ℂ)⁻¹)) * Polynomial.C (2*d : R) = 1 := by
    have h := congrArg (fun z : ℂ => Polynomial.C (algebraMap ℂ R z)) (inv_mul_cancel₀ hm)
    simpa only [map_mul, map_one, map_natCast, map_ofNat] using h
  simp only [binaryWronskianOver, map_mul, map_sub, binaryDehomogenizeOver,
    MvPolynomial.eval₂Hom_C]
  change Polynomial.C (algebraMap ℂ R ((2*d : ℂ)⁻¹)) *
    (binaryDehomogenizeOver R (MvPolynomial.pderiv 1 (binaryNumeratorOver H)) *
        binaryDehomogenizeOver R (MvPolynomial.pderiv 0 (binaryDenominatorOver R d)) -
      binaryDehomogenizeOver R (MvPolynomial.pderiv 0 (binaryNumeratorOver H)) *
        binaryDehomogenizeOver R (MvPolynomial.pderiv 1 (binaryDenominatorOver R d))) = _
  rw [binaryDehomogenize_pderiv_b, binaryDehomogenize_pderiv_b,
    binaryDehomogenize_pderiv_a _ (binaryDenominatorOver_homogeneous R d),
    binaryDehomogenize_pderiv_a _ (binaryNumeratorOver_homogeneous H),
    binaryDehomogenize_numerator, binaryDehomogenize_denominator]
  push_cast
  change _ = (affineNumeratorOver H).derivative*affineDenominatorOver R d -
    affineNumeratorOver H*(affineDenominatorOver R d).derivative
  calc
    _ = (Polynomial.C (algebraMap ℂ R ((2*d : ℂ)⁻¹))*Polynomial.C (2*d : R)) *
        ((affineNumeratorOver H).derivative*affineDenominatorOver R d -
          affineNumeratorOver H*(affineDenominatorOver R d).derivative) := by push_cast; ring
    _ = _ := by rw [hc, one_mul]

theorem binaryWronskian_affine_eval {d : ℕ} (hd : 0 < d) (H : Parameter d) (t : ℂ) :
    binaryEval (binaryWronskian H) 1 t = (affineWronskian H).eval t := by
  rw [← binaryDehomogenize_eval, binaryDehomogenize_wronskian hd]

theorem binaryWronskian_affine_derivative_eval {d : ℕ} (hd : 0 < d)
    (H : Parameter d) (t : ℂ) :
    binaryEval (MvPolynomial.pderiv 1 (binaryWronskian H)) 1 t =
      (affineWronskian H).derivative.eval t := by
  rw [← binaryDehomogenize_eval, binaryDehomogenize_pderiv_b,
    binaryDehomogenize_wronskian hd]

#assert_trust kernel binaryWronskianOver_homogeneous
#assert_trust kernel binary_homogeneous_reconstruct
#assert_trust kernel binaryWronskianOver_reconstruct
#assert_trust kernel binaryWronskian_eval
#assert_trust kernel quotientDerivativeNumerator_Da
#assert_trust kernel quotientDerivativeNumerator_Db
#assert_trust kernel binaryDehomogenize_wronskian
#assert_trust kernel binaryWronskian_affine_eval
#assert_trust kernel binaryWronskian_affine_derivative_eval
#print axioms binaryWronskianOver_reconstruct
end NLA.Proofs.TR26
