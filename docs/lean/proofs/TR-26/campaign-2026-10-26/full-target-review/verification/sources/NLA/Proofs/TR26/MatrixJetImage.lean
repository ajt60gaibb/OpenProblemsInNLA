import NLA.Proofs.TR26.ClearedJetGraph

/-! The cleared nonisotropic Taylor map with all free matrix-kernel directions.
Its coordinates are genuine polynomials in the root, jet, tail and free matrix
variables. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem affineNumerator_lift_eq_ofFn (d : ℕ) (c : Fin (2 * d + 1) → ℂ) :
    affineNumerator (numeratorLift d c) = Polynomial.ofFn (2 * d + 1) c := by
  rw [affineNumerator_lift, Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.C_mul_X_pow_eq_monomial]

theorem affineNumerator_lift_toFn {d : ℕ} (N : Polynomial ℂ) (hN : N.natDegree ≤ 2 * d) :
    affineNumerator (numeratorLift d (Polynomial.toFn (2 * d + 1) N)) = N := by
  rw [affineNumerator_lift_eq_ofFn,
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)]

theorem numeratorLift_sub (d : ℕ) (a b : Fin (2 * d + 1) → ℂ) :
    numeratorLift d (a - b) = numeratorLift d a - numeratorLift d b := by
  simp [numeratorLift, sub_smul, Finset.sum_sub_distrib]

def numeratorKernelProjection {d : ℕ} (H : Parameter d) : Parameter d :=
  H - numeratorLift d (numeratorCoefficientMap d H)

theorem affineNumerator_kernelProjection {d : ℕ} (H : Parameter d) :
    affineNumerator (numeratorKernelProjection H) = 0 := by
  change affineNumeratorLinear d (H - numeratorLift d (numeratorCoefficientMap d H)) = 0
  rw [map_sub]
  change affineNumerator H - affineNumerator
    (numeratorLift d (Polynomial.toFn (2 * d + 1) (affineNumerator H))) = 0
  rw [affineNumerator_lift_toFn _ (affineNumerator_natDegree_le H), sub_self]

theorem numeratorLift_add_kernelProjection {d : ℕ} (H : Parameter d) :
    numeratorLift d (numeratorCoefficientMap d H) + numeratorKernelProjection H = H := by
  simp [numeratorKernelProjection]

abbrev MatrixJetVariable (d : ℕ) := Sum (JetVariable d) (SymIndex d)
abbrev MatrixJetRing (d : ℕ) := MvPolynomial (MatrixJetVariable d) ℂ

def matrixJetFreeNumeratorCoefficient (d : ℕ) (k : Fin (2 * d + 1)) : MatrixJetRing d :=
  (affineNumeratorOver
    (fun ij : SymIndex d => MvPolynomial.X (Sum.inr ij) : SymIndex d → MatrixJetRing d)).coeff k.val

def matrixJetPolynomial (d : ℕ) (ij : SymIndex d) : MatrixJetRing d :=
  MvPolynomial.X (Sum.inr ij) + ∑ k : Fin (2 * d + 1),
    (MvPolynomial.rename Sum.inl (clearedJetCoefficient d k) -
      matrixJetFreeNumeratorCoefficient d k) * MvPolynomial.C (numeratorBasisMatrix d k ij)

def matrixJetDenominator (d : ℕ) : MatrixJetRing d :=
  MvPolynomial.rename Sum.inl (jetGraphDenominator d)

def matrixJetMap (d : ℕ) (x : MatrixJetVariable d → ℂ) : Parameter d :=
  fun ij => MvPolynomial.eval x (matrixJetPolynomial d ij)

theorem map_coordinateEntry {R S : Type*} [CommSemiring R] [CommSemiring S]
    {d : ℕ} (f : R →+* S) (H : SymIndex d → R) (i j : Index d) :
    f (coordinateEntry H i j) = coordinateEntry (fun ij => f (H ij)) i j := by
  unfold coordinateEntry
  split_ifs <;> rfl

theorem map_affineNumeratorOver {R S : Type*} [CommSemiring R] [CommSemiring S]
    {d : ℕ} (f : R →+* S) (H : SymIndex d → R) :
    (affineNumeratorOver H).map f = affineNumeratorOver (fun ij => f (H ij)) := by
  simp only [affineNumeratorOver, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [map_coordinateEntry f H i j]

theorem eval_matrixJetFreeNumeratorCoefficient (d : ℕ) (x : MatrixJetVariable d → ℂ)
    (k : Fin (2 * d + 1)) :
    MvPolynomial.eval x (matrixJetFreeNumeratorCoefficient d k) =
      numeratorCoefficientMap d (fun ij => x (Sum.inr ij)) k := by
  have h := congrArg (fun P : Polynomial ℂ => P.coeff k.val)
    (map_affineNumeratorOver (MvPolynomial.eval x)
      (fun ij : SymIndex d => MvPolynomial.X (Sum.inr ij) : SymIndex d → MatrixJetRing d))
  change MvPolynomial.eval x
    ((affineNumeratorOver (fun ij : SymIndex d => MvPolynomial.X (Sum.inr ij) :
      SymIndex d → MatrixJetRing d)).coeff k.val) =
    (affineNumeratorOver (fun ij : SymIndex d => x (Sum.inr ij))).coeff k.val
  simpa only [Polynomial.coeff_map, MvPolynomial.eval_X] using h

theorem matrixJetMap_eq (d : ℕ) (x : MatrixJetVariable d → ℂ) :
    matrixJetMap d x =
      numeratorLift d (fun k => MvPolynomial.eval (fun j => x (Sum.inl j)) (clearedJetCoefficient d k)) +
        numeratorKernelProjection (fun ij => x (Sum.inr ij)) := by
  classical
  ext ij
  simp only [matrixJetMap, matrixJetPolynomial, map_add, map_sum, map_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_C, map_sub,
    MvPolynomial.eval_rename, Function.comp_def, eval_matrixJetFreeNumeratorCoefficient]
  simp only [numeratorLift, numeratorKernelProjection, Pi.add_apply, Pi.sub_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
  ring

theorem eval_matrixJetDenominator (d : ℕ) (x : MatrixJetVariable d → ℂ) :
    MvPolynomial.eval x (matrixJetDenominator d) =
      2 * (affineDenominator d).eval (x (Sum.inl (Sum.inl 0))) := by
  rw [matrixJetDenominator, MvPolynomial.eval_rename, eval_jetGraphDenominator]
  rfl

theorem matrixJetDenominator_ne_zero (d : ℕ) : matrixJetDenominator d ≠ 0 := by
  exact (MvPolynomial.rename_injective _ Sum.inl_injective).ne (jetGraphDenominator_ne_zero d)

theorem secondJetPolynomial_smul (c r a0 a1 a2 : ℂ) (tail : Polynomial ℂ) :
    secondJetPolynomial r (c * a0) (c * a1) (c * a2) (c • tail) =
      c • secondJetPolynomial r a0 a1 a2 tail := by
  simp only [secondJetPolynomial, Polynomial.smul_eq_C_mul, map_mul]
  ring

theorem nonisotropicJetNumerator_smul (d : ℕ) (r c a0 : ℂ)
    (tail : Fin (2 * d - 2) → ℂ) :
    nonisotropicJetNumerator d r (c * a0) (c • tail) =
      c • nonisotropicJetNumerator d r a0 tail := by
  unfold nonisotropicJetNumerator
  rw [map_smul]
  have h1 : c * a0 * (affineDenominator d).derivative.eval r /
      (affineDenominator d).eval r =
      c * (a0 * (affineDenominator d).derivative.eval r / (affineDenominator d).eval r) := by ring
  have h2 : c * a0 * (affineDenominator d).derivative.derivative.eval r /
      (2 * (affineDenominator d).eval r) =
      c * (a0 * (affineDenominator d).derivative.derivative.eval r /
        (2 * (affineDenominator d).eval r)) := by ring
  rw [h1, h2, secondJetPolynomial_smul]

theorem affineNumerator_matrixJetMap {d : ℕ} (hd : 2 ≤ d)
    (x : MatrixJetVariable d → ℂ)
    (hD : (affineDenominator d).eval (x (Sum.inl (Sum.inl 0))) ≠ 0) :
    affineNumerator (matrixJetMap d x) =
      C (2 * (affineDenominator d).eval (x (Sum.inl (Sum.inl 0)))) *
        nonisotropicJetNumerator d (x (Sum.inl (Sum.inl 0)))
          (x (Sum.inl (Sum.inl 1))) (fun i => x (Sum.inl (Sum.inr i))) := by
  let jx : JetVariable d → ℂ := fun j => x (Sum.inl j)
  let P := (clearedJetNumerator d).map (MvPolynomial.eval jx)
  have hP : P = C (2 * (affineDenominator d).eval (jx (Sum.inl 0))) *
      nonisotropicJetNumerator d (jx (Sum.inl 0)) (jx (Sum.inl 1))
        (fun i => jx (Sum.inr i)) := map_clearedJetNumerator d jx hD
  have hdeg : P.natDegree ≤ 2 * d := by
    rw [hP]
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      (nonisotropicJetNumerator_natDegree_le hd _ _ _)
  have hc : (fun k => MvPolynomial.eval jx (clearedJetCoefficient d k)) =
      Polynomial.toFn (2 * d + 1) P := by
    ext k
    exact (Polynomial.coeff_map _ _).symm
  rw [matrixJetMap_eq]
  change affineNumeratorLinear d (_ + _) = _
  rw [map_add]
  change affineNumerator (numeratorLift d (fun k => MvPolynomial.eval jx (clearedJetCoefficient d k))) +
    affineNumerator (numeratorKernelProjection (fun ij => x (Sum.inr ij))) = _
  rw [affineNumerator_kernelProjection, add_zero, hc, affineNumerator_lift_toFn P hdeg]
  exact hP

theorem matrixJetMap_double_root {d : ℕ} (hd : 2 ≤ d)
    (x : MatrixJetVariable d → ℂ)
    (hD : (affineDenominator d).eval (x (Sum.inl (Sum.inl 0))) ≠ 0) :
    (affineWronskian (matrixJetMap d x)).eval (x (Sum.inl (Sum.inl 0))) = 0 ∧
      (affineWronskian (matrixJetMap d x)).derivative.eval (x (Sum.inl (Sum.inl 0))) = 0 := by
  let r := x (Sum.inl (Sum.inl 0))
  let J := nonisotropicJetNumerator d r (x (Sum.inl (Sum.inl 1)))
    (fun i => x (Sum.inl (Sum.inr i)))
  have hJ : (polynomialWronskian J (affineDenominator d)).eval r = 0 ∧
      (polynomialWronskian J (affineDenominator d)).derivative.eval r = 0 :=
    (secondJetPolynomial_double_root_iff _ _ _ _ _ _ hD).mpr ⟨rfl, rfl⟩
  have hW : affineWronskian (matrixJetMap d x) =
      C (2 * (affineDenominator d).eval r) * polynomialWronskian J (affineDenominator d) := by
    change (affineNumerator (matrixJetMap d x)).derivative * affineDenominator d -
      affineNumerator (matrixJetMap d x) * (affineDenominator d).derivative = _
    rw [affineNumerator_matrixJetMap hd x hD]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
      polynomialWronskian]
    ring
  change (affineWronskian (matrixJetMap d x)).eval r = 0 ∧
    (affineWronskian (matrixJetMap d x)).derivative.eval r = 0
  rw [hW]
  simp only [Polynomial.eval_mul, Polynomial.derivative_mul, Polynomial.derivative_C,
    zero_mul, zero_add, hJ.1, hJ.2, mul_zero]
  exact ⟨trivial, trivial⟩

theorem exists_matrixJetMap_of_double_root {d : ℕ} (hd : 2 ≤ d)
    (H : Parameter d) (r : ℂ) (hD : (affineDenominator d).eval r ≠ 0)
    (hroot : (affineWronskian H).eval r = 0 ∧ (affineWronskian H).derivative.eval r = 0) :
    ∃ x : MatrixJetVariable d → ℂ,
      x (Sum.inl (Sum.inl 0)) = r ∧ matrixJetMap d x = H := by
  obtain ⟨a0, tail, hN⟩ :=
    (affine_double_Wronskian_root_iff_finite_parameterization hd H r hD).mp hroot
  let c := 2 * (affineDenominator d).eval r
  have hc : c ≠ 0 := mul_ne_zero (by norm_num) hD
  let jx := jetPoint d r (c⁻¹ * a0) (c⁻¹ • tail)
  let x : MatrixJetVariable d → ℂ := Sum.elim jx H
  have hP : (clearedJetNumerator d).map (MvPolynomial.eval jx) = affineNumerator H := by
    rw [map_clearedJetNumerator d jx (by simpa [jx, jetPoint] using hD)]
    simp only [jx, jetPoint, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [nonisotropicJetNumerator_smul, ← hN]
    rw [← Polynomial.smul_eq_C_mul]
    change c • (c⁻¹ • affineNumerator H) = affineNumerator H
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hcoeff : (fun k : Fin (2 * d + 1) =>
      MvPolynomial.eval jx (clearedJetCoefficient d k)) = numeratorCoefficientMap d H := by
    ext k
    change MvPolynomial.eval jx ((clearedJetNumerator d).coeff k.val) = (affineNumerator H).coeff k.val
    rw [← Polynomial.coeff_map, hP]
  refine ⟨x, by simp [x, jx, jetPoint], ?_⟩
  rw [matrixJetMap_eq]
  change numeratorLift d (fun k => MvPolynomial.eval jx (clearedJetCoefficient d k)) +
    numeratorKernelProjection H = H
  rw [hcoeff, numeratorLift_add_kernelProjection]

theorem affine_double_Wronskian_root_iff_matrixJetMap {d : ℕ} (hd : 2 ≤ d)
    (H : Parameter d) (r : ℂ) (hD : (affineDenominator d).eval r ≠ 0) :
    ((affineWronskian H).eval r = 0 ∧ (affineWronskian H).derivative.eval r = 0) ↔
    ∃ x : MatrixJetVariable d → ℂ,
      x (Sum.inl (Sum.inl 0)) = r ∧ matrixJetMap d x = H := by
  constructor
  · exact exists_matrixJetMap_of_double_root hd H r hD
  · rintro ⟨x, hxr, rfl⟩
    have h := matrixJetMap_double_root hd x (by rwa [hxr])
    simpa only [hxr] using h

theorem exists_matrixJetPolynomial_ne_zero {d : ℕ} (hd : 2 ≤ d) :
    ∃ ij : SymIndex d, matrixJetPolynomial d ij ≠ 0 := by
  classical
  let D := affineDenominator d
  let H := numeratorLift d (Polynomial.toFn (2 * d + 1) D)
  have hN : affineNumerator H = D :=
    affineNumerator_lift_toFn D (affineDenominator_natDegree d).le
  have hH : H ≠ 0 := by
    intro hz
    have hzero : affineNumerator H = 0 := by
      rw [hz]
      exact (affineNumeratorLinear d).map_zero
    exact affineDenominator_ne_zero d (hN.symm.trans hzero)
  have hW : affineWronskian H = 0 := by
    change (affineNumerator H).derivative * D - affineNumerator H * D.derivative = 0
    rw [hN]
    ring
  obtain ⟨x, _, hx⟩ := exists_matrixJetMap_of_double_root hd H 0
    (by rw [affineDenominator_eval_zero]; exact one_ne_zero)
    (by simp [hW])
  have hi : ∃ ij, H ij ≠ 0 := by
    by_contra! h
    exact hH (_root_.funext h)
  obtain ⟨ij, hij⟩ := hi
  refine ⟨ij, ?_⟩
  intro hz
  have heval := congrArg (MvPolynomial.eval x) hz
  change matrixJetMap d x ij = 0 at heval
  rw [hx] at heval
  exact hij heval

def finiteDoubleWronskianImage (d : ℕ) : Set (Parameter d) :=
  {H | H ≠ 0 ∧ ∃ r : ℂ, (affineDenominator d).eval r ≠ 0 ∧
    (affineWronskian H).eval r = 0 ∧ (affineWronskian H).derivative.eval r = 0}

theorem finiteDoubleWronskianImage_eq_matrixJetImage {d : ℕ} (hd : 2 ≤ d) :
    finiteDoubleWronskianImage d =
      {H | ∃ x : MatrixJetVariable d → ℂ,
        MvPolynomial.eval x (matrixJetDenominator d) ≠ 0 ∧
        matrixJetMap d x ≠ 0 ∧ matrixJetMap d x = H} := by
  ext H
  constructor
  · rintro ⟨hH, r, hD, hW, hW'⟩
    obtain ⟨x, hxr, hx⟩ := exists_matrixJetMap_of_double_root hd H r hD ⟨hW, hW'⟩
    refine ⟨x, ?_, by rwa [hx], hx⟩
    rw [eval_matrixJetDenominator, hxr]
    exact mul_ne_zero (by norm_num) hD
  · rintro ⟨x, hden, hH, rfl⟩
    rw [eval_matrixJetDenominator] at hden
    have hD := (mul_ne_zero_iff.mp hden).2
    exact ⟨hH, x (Sum.inl (Sum.inl 0)), hD, matrixJetMap_double_root hd x hD⟩

#assert_trust kernel affineNumerator_lift_eq_ofFn
#assert_trust kernel affineNumerator_lift_toFn
#assert_trust kernel numeratorLift_sub
#assert_trust kernel affineNumerator_kernelProjection
#assert_trust kernel numeratorLift_add_kernelProjection
#assert_trust kernel map_coordinateEntry
#assert_trust kernel map_affineNumeratorOver
#assert_trust kernel eval_matrixJetFreeNumeratorCoefficient
#assert_trust kernel matrixJetMap_eq
#assert_trust kernel eval_matrixJetDenominator
#assert_trust kernel matrixJetDenominator_ne_zero
#assert_trust kernel secondJetPolynomial_smul
#assert_trust kernel nonisotropicJetNumerator_smul
#assert_trust kernel affineNumerator_matrixJetMap
#assert_trust kernel matrixJetMap_double_root
#assert_trust kernel exists_matrixJetMap_of_double_root
#assert_trust kernel affine_double_Wronskian_root_iff_matrixJetMap
#assert_trust kernel exists_matrixJetPolynomial_ne_zero
#assert_trust kernel finiteDoubleWronskianImage_eq_matrixJetImage
#print axioms matrixJetMap_eq
#print axioms affine_double_Wronskian_root_iff_matrixJetMap
#print axioms finiteDoubleWronskianImage_eq_matrixJetImage
end NLA.Proofs.TR26
