import NLA.Proofs.TR26.WronskianJetParameterization
import NLA.Proofs.TR26.Denominator

/-! A polynomial graph for the actual nonisotropic double-root incidence.
All output coordinates share the explicit denominator `2 * D(r)`; no
inverse occurs in the polynomial coefficient ring. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
open Polynomial
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

abbrev JetVariable (d : ℕ) := Sum (Fin 2) (Fin (2 * d - 2))
abbrev JetRing (d : ℕ) := MvPolynomial (JetVariable d) ℂ

def jetRoot (d : ℕ) : JetRing d := MvPolynomial.X (Sum.inl 0)
def jetHeight (d : ℕ) : JetRing d := MvPolynomial.X (Sum.inl 1)
def jetTail (d : ℕ) : Fin (2 * d - 2) → JetRing d := fun i => MvPolynomial.X (Sum.inr i)

def jetPoint (d : ℕ) (r a0 : ℂ) (tail : Fin (2 * d - 2) → ℂ) : JetVariable d → ℂ :=
  Sum.elim ![r, a0] tail

def jetScalarValue (d : ℕ) (P : Polynomial ℂ) : JetRing d :=
  (P.map MvPolynomial.C).eval (jetRoot d)

def jetGraphDenominator (d : ℕ) : JetRing d := 2 * jetScalarValue d (affineDenominator d)

def clearedJetNumerator (d : ℕ) : Polynomial (JetRing d) :=
  let r := jetRoot d
  let a0 := jetHeight d
  let D0 := jetScalarValue d (affineDenominator d)
  let D1 := jetScalarValue d (affineDenominator d).derivative
  let D2 := jetScalarValue d (affineDenominator d).derivative.derivative
  C (2 * a0 * D0) + C (2 * a0 * D1) * (X - C r) +
    C (a0 * D2) * (X - C r) ^ 2 +
      C (2 * D0) * (X - C r) ^ 3 * Polynomial.ofFn (2 * d - 2) (jetTail d)

def clearedJetCoefficient (d : ℕ) (i : Fin (2 * d + 1)) : JetRing d :=
  (clearedJetNumerator d).coeff i.val

abbrev CoefficientJetVariable (d : ℕ) := Sum (Fin (2 * d + 1)) (JetVariable d)

def clearedJetGraphEquation (d : ℕ) (i : Fin (2 * d + 1)) :
    MvPolynomial (CoefficientJetVariable d) ℂ :=
  MvPolynomial.rename Sum.inr (jetGraphDenominator d) * MvPolynomial.X (Sum.inl i) -
    MvPolynomial.rename Sum.inr (clearedJetCoefficient d i)

theorem eval_jetScalarValue (d : ℕ) (P : Polynomial ℂ) (x : JetVariable d → ℂ) :
    MvPolynomial.eval x (jetScalarValue d P) = P.eval (x (Sum.inl 0)) := by
  unfold jetScalarValue
  rw [← Polynomial.eval_map_apply]
  simp only [Polynomial.map_map, MvPolynomial.eval_X, jetRoot]
  have hc : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℂ := by ext; simp
  rw [hc, Polynomial.map_id]

theorem map_ofFn_eq {R S : Type*} [CommSemiring R] [CommSemiring S] [DecidableEq R] [DecidableEq S]
    (f : R →+* S) (n : ℕ) (a : Fin n → R) :
    (Polynomial.ofFn n a).map f = Polynomial.ofFn n (fun i => f (a i)) := by
  classical
  rw [Polynomial.ofFn_eq_sum_monomial, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum]
  simp only [Polynomial.map_monomial]

theorem eval_jetGraphDenominator (d : ℕ) (x : JetVariable d → ℂ) :
    MvPolynomial.eval x (jetGraphDenominator d) =
      2 * (affineDenominator d).eval (x (Sum.inl 0)) := by
  simp only [jetGraphDenominator, map_mul, map_ofNat, eval_jetScalarValue]

theorem jetGraphDenominator_ne_zero (d : ℕ) : jetGraphDenominator d ≠ 0 := by
  intro h
  have heval := congrArg (MvPolynomial.eval (fun _ : JetVariable d => (0 : ℂ))) h
  rw [eval_jetGraphDenominator, affineDenominator_eval_zero, mul_one, map_zero] at heval
  norm_num at heval

theorem eval_clearedJetGraphEquation (d : ℕ) (c : Fin (2 * d + 1) → ℂ)
    (x : JetVariable d → ℂ) (i : Fin (2 * d + 1)) :
    MvPolynomial.eval (Sum.elim c x) (clearedJetGraphEquation d i) =
      MvPolynomial.eval x (jetGraphDenominator d) * c i -
        MvPolynomial.eval x (clearedJetCoefficient d i) := by
  simp [clearedJetGraphEquation, MvPolynomial.eval_rename, Function.comp_def]

theorem map_clearedJetNumerator (d : ℕ) (x : JetVariable d → ℂ)
    (hD : (affineDenominator d).eval (x (Sum.inl 0)) ≠ 0) :
    (clearedJetNumerator d).map (MvPolynomial.eval x) =
      C (2 * (affineDenominator d).eval (x (Sum.inl 0))) *
        nonisotropicJetNumerator d (x (Sum.inl 0)) (x (Sum.inl 1))
          (fun i => x (Sum.inr i)) := by
  simp only [clearedJetNumerator, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_ofNat, map_mul, map_ofNat,
    eval_jetScalarValue, jetRoot, jetHeight, MvPolynomial.eval_X,
    map_ofFn_eq, jetTail, nonisotropicJetNumerator, secondJetPolynomial]
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have h1 : 2 * (affineDenominator d).eval (x (Sum.inl 0)) *
      (x (Sum.inl 1) * (affineDenominator d).derivative.eval (x (Sum.inl 0)) /
        (affineDenominator d).eval (x (Sum.inl 0))) =
      2 * x (Sum.inl 1) * (affineDenominator d).derivative.eval (x (Sum.inl 0)) := by
    field_simp
    <;> ring
  have h2 : 2 * (affineDenominator d).eval (x (Sum.inl 0)) *
      (x (Sum.inl 1) * (affineDenominator d).derivative.derivative.eval (x (Sum.inl 0)) /
        (2 * (affineDenominator d).eval (x (Sum.inl 0)))) =
      x (Sum.inl 1) * (affineDenominator d).derivative.derivative.eval (x (Sum.inl 0)) := by
    field_simp
    <;> ring
  have hc0 : (C (2 * (affineDenominator d).eval (x (Sum.inl 0))) : Polynomial ℂ) *
      C (x (Sum.inl 1)) = C (2 * x (Sum.inl 1) *
        (affineDenominator d).eval (x (Sum.inl 0))) := by
    rw [← Polynomial.C_mul]
    congr 1
    ring
  have hc1 := congrArg (C : ℂ → Polynomial ℂ) h1
  have hc2 := congrArg (C : ℂ → Polynomial ℂ) h2
  simp only [Polynomial.C_mul, map_ofNat] at hc0 hc1 hc2
  rw [mul_add, mul_add, mul_add]
  simp only [← mul_assoc]
  rw [hc0, hc1, hc2]


theorem eval_clearedJetCoefficient (d : ℕ) (x : JetVariable d → ℂ)
    (hD : (affineDenominator d).eval (x (Sum.inl 0)) ≠ 0)
    (i : Fin (2 * d + 1)) :
    MvPolynomial.eval x (clearedJetCoefficient d i) =
      (2 * (affineDenominator d).eval (x (Sum.inl 0))) *
        (nonisotropicJetNumerator d (x (Sum.inl 0)) (x (Sum.inl 1))
          (fun j => x (Sum.inr j))).coeff i.val := by
  have h := congrArg (fun P : Polynomial ℂ => P.coeff i.val) (map_clearedJetNumerator d x hD)
  simpa only [clearedJetCoefficient, Polynomial.coeff_map, Polynomial.coeff_C_mul] using h

theorem numerator_eq_iff_clearedJetGraph {d : ℕ} (hd : 2 ≤ d) (H : Parameter d)
    (x : JetVariable d → ℂ) (hD : (affineDenominator d).eval (x (Sum.inl 0)) ≠ 0) :
    affineNumerator H = nonisotropicJetNumerator d (x (Sum.inl 0)) (x (Sum.inl 1))
      (fun j => x (Sum.inr j)) ↔
    ∀ i : Fin (2 * d + 1),
      MvPolynomial.eval x (jetGraphDenominator d) * numeratorCoefficientMap d H i =
        MvPolynomial.eval x (clearedJetCoefficient d i) := by
  have hden : 2 * (affineDenominator d).eval (x (Sum.inl 0)) ≠ 0 := mul_ne_zero (by norm_num) hD
  simp only [eval_jetGraphDenominator, eval_clearedJetCoefficient d x hD]
  constructor
  · intro h i
    change _ * (affineNumerator H).coeff i.val = _
    rw [h]
  · intro h
    have hcoeff : Polynomial.toFn (2 * d + 1) (affineNumerator H) =
        Polynomial.toFn (2 * d + 1)
          (nonisotropicJetNumerator d (x (Sum.inl 0)) (x (Sum.inl 1)) (fun j => x (Sum.inr j))) :=
      _root_.funext (fun i => mul_left_cancel₀ hden (h i))
    have heq := congrArg (Polynomial.ofFn (2 * d + 1)) hcoeff
    have hN : (affineNumerator H).natDegree < 2 * d + 1 := by
      have h := affineNumerator_natDegree_le H
      omega
    have hJ : (nonisotropicJetNumerator d (x (Sum.inl 0)) (x (Sum.inl 1))
        (fun j => x (Sum.inr j))).natDegree < 2 * d + 1 := by
      have h := nonisotropicJetNumerator_natDegree_le hd (x (Sum.inl 0))
        (x (Sum.inl 1)) (fun j => x (Sum.inr j))
      omega
    simpa only [Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hN,
      Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hJ] using heq

theorem affine_double_Wronskian_root_iff_clearedJetGraph {d : ℕ} (hd : 2 ≤ d)
    (H : Parameter d) (r : ℂ) (hD : (affineDenominator d).eval r ≠ 0) :
    ((affineWronskian H).eval r = 0 ∧ (affineWronskian H).derivative.eval r = 0) ↔
    ∃ x : JetVariable d → ℂ, x (Sum.inl 0) = r ∧
      ∀ i : Fin (2 * d + 1),
        MvPolynomial.eval (Sum.elim (numeratorCoefficientMap d H) x)
          (clearedJetGraphEquation d i) = 0 := by
  rw [affine_double_Wronskian_root_iff_finite_parameterization hd H r hD]
  constructor
  · rintro ⟨a0, tail, hN⟩
    refine ⟨jetPoint d r a0 tail, by simp [jetPoint], ?_⟩
    have hDx : (affineDenominator d).eval (jetPoint d r a0 tail (Sum.inl 0)) ≠ 0 := by
      simpa only [jetPoint, Sum.elim_inl, Matrix.cons_val_zero] using hD
    have hg := (numerator_eq_iff_clearedJetGraph hd H (jetPoint d r a0 tail) hDx).mp
      (by simpa [jetPoint] using hN)
    intro i
    rw [eval_clearedJetGraphEquation, hg i, sub_self]
  · rintro ⟨x, hxr, hx⟩
    have hDx : (affineDenominator d).eval (x (Sum.inl 0)) ≠ 0 := by rwa [hxr]
    have hg : ∀ i, MvPolynomial.eval x (jetGraphDenominator d) * numeratorCoefficientMap d H i =
        MvPolynomial.eval x (clearedJetCoefficient d i) := by
      intro i
      exact sub_eq_zero.mp (by simpa only [eval_clearedJetGraphEquation] using hx i)
    refine ⟨x (Sum.inl 1), (fun i => x (Sum.inr i)), ?_⟩
    simpa only [hxr] using (numerator_eq_iff_clearedJetGraph hd H x hDx).mpr hg


#assert_trust kernel eval_jetScalarValue
#assert_trust kernel map_ofFn_eq
#assert_trust kernel eval_jetGraphDenominator
#assert_trust kernel jetGraphDenominator_ne_zero
#assert_trust kernel eval_clearedJetGraphEquation
#assert_trust kernel map_clearedJetNumerator
#assert_trust kernel eval_clearedJetCoefficient
#assert_trust kernel numerator_eq_iff_clearedJetGraph
#assert_trust kernel affine_double_Wronskian_root_iff_clearedJetGraph
#print axioms numerator_eq_iff_clearedJetGraph
#print axioms affine_double_Wronskian_root_iff_clearedJetGraph
end NLA.Proofs.TR26
