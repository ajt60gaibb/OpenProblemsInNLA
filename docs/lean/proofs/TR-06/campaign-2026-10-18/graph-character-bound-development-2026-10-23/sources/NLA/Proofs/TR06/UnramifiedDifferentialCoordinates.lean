/-
Copyright (c) 2026. Released under Apache 2.0 license.
Actual polynomial pullback from the ordered Segre source to pivot parameters.
-/
import NLA.TR06.SegreCoordinates
import NLA.TR06.SegreAlgebra
import NLA.Proofs.TR06.UnramifiedDifferentialAlgebra

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open NLA.TR06 NLA.TR06.Segre NLA.TR06.Proposed
namespace NLA.Proofs.TR06.UnramifiedDifferential

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- Raw factor entries with the amplitude absorbed in one fixed actual mode. -/
def rawPivotPolynomial (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d)
    (c : OrderedFactorIndex d n r) : MvPolynomial (Coordinate q₀) ℂ :=
  (if c.2.1 = j₀ then MvPolynomial.X ⟨c.1, none⟩ else 1) *
    factorPolynomial ℂ q₀ c.1 c.2.1 c.2.2

/-- Restriction of actual raw-factor polynomial substitution to SegreSource. -/
def pivotSourceHom (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d) :
    SegreSource d n r →ₐ[ℂ] MvPolynomial (Coordinate q₀) ℂ :=
  (MvPolynomial.aeval (R := ℂ) (rawPivotPolynomial q₀ j₀)).comp
    (segreSourceSubalgebra d n r).val

@[simp] theorem pivotSourceHom_coordinate (q₀ : Fin r → TensorIndex d n)
    (j₀ : Fin d) (i : Fin r) (q : TensorIndex d n) :
    pivotSourceHom q₀ j₀ (segreCoordinate (i,q)) = summandPolynomial ℂ q₀ i q := by
  change (MvPolynomial.aeval (R := ℂ) (rawPivotPolynomial q₀ j₀))
      (∏ j : Fin d, MvPolynomial.X (i, ⟨j, q j⟩)) = _
  rw [map_prod]
  have hv (j : Fin d) :
      (MvPolynomial.aeval (R := ℂ) (rawPivotPolynomial q₀ j₀)) (MvPolynomial.X (i, ⟨j,q j⟩)) =
        (if j = j₀ then MvPolynomial.X ⟨i,none⟩ else 1) *
          factorPolynomial ℂ q₀ i j (q j) := MvPolynomial.aeval_X (R := ℂ) _ _
  simp_rw [hv]
  rw [Finset.prod_mul_distrib]
  simp [summandPolynomial]

@[simp] theorem pivotSourceHom_addition (q₀ : Fin r → TensorIndex d n)
    (j₀ : Fin d) (q : TensorIndex d n) :
    pivotSourceHom q₀ j₀ (additionAlgebraHom d n r (MvPolynomial.X q)) =
      sumPolynomial ℂ q₀ q := by
  simp [additionAlgebraHom, sumPolynomial]

/-- The genuine dual-number first jet at a parameter point and direction. -/
def pivotJet {q₀ : Fin r → TensorIndex d n} (z v : Parameter ℂ q₀) :
    MvPolynomial (Coordinate q₀) ℂ →ₐ[ℂ] TrivSqZeroExt ℂ ℂ :=
  MvPolynomial.aeval (R := ℂ) (fun c => ((z c, v c) : TrivSqZeroExt ℂ ℂ))

@[simp] theorem pivotJet_X {q₀ : Fin r → TensorIndex d n}
    (z v : Parameter ℂ q₀) (c : Coordinate q₀) :
    pivotJet z v (MvPolynomial.X c) = (z c, v c) := by
  exact MvPolynomial.aeval_X (R := ℂ) _ _

@[simp] theorem pivotJet_fst {q₀ : Fin r → TensorIndex d n}
    (z v : Parameter ℂ q₀) (p : MvPolynomial (Coordinate q₀) ℂ) :
    (pivotJet z v p).fst = MvPolynomial.eval (fun c => z c) p := by
  have h : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp (pivotJet z v) =
      MvPolynomial.aeval (R := ℂ) (fun c => z c) := by
    ext c
    change (pivotJet z v (MvPolynomial.X c)).fst =
      (MvPolynomial.aeval (R := ℂ) (fun c => z c)) (MvPolynomial.X c)
    rw [pivotJet_X, MvPolynomial.aeval_X]
    rfl
  exact AlgHom.congr_fun h p

@[simp] theorem pivotJet_C {q₀ : Fin r → TensorIndex d n}
    (z v : Parameter ℂ q₀) (c : ℂ) :
    pivotJet z v (MvPolynomial.C c) = TrivSqZeroExt.inl c := by
  exact MvPolynomial.aeval_C _ _

@[simp] theorem pivotJet_add_snd {q₀ : Fin r → TensorIndex d n}
    (z v : Parameter ℂ q₀) (p q : MvPolynomial (Coordinate q₀) ℂ) :
    (pivotJet z v (p+q)).snd = (pivotJet z v p).snd + (pivotJet z v q).snd := by
  rw [map_add]
  rfl

theorem pivotJet_mul_snd {q₀ : Fin r → TensorIndex d n}
    (z v : Parameter ℂ q₀) (p q : MvPolynomial (Coordinate q₀) ℂ) :
    (pivotJet z v (p*q)).snd =
      MvPolynomial.eval (fun c => z c) p * (pivotJet z v q).snd +
      (pivotJet z v p).snd * MvPolynomial.eval (fun c => z c) q := by
  rw [map_mul]
  change (pivotJet z v p).fst * (pivotJet z v q).snd +
    (pivotJet z v p).snd * (pivotJet z v q).fst = _
  rw [pivotJet_fst, pivotJet_fst]

/-- The amplitude is exactly one of the actual summand coordinate functions. -/
@[simp] theorem summandPolynomial_pivot (q₀ : Fin r → TensorIndex d n) (i : Fin r) :
    summandPolynomial ℂ q₀ i (q₀ i) = MvPolynomial.X ⟨i, none⟩ := by
  simp [summandPolynomial, factorPolynomial]

/-- A one-mode replacement gives amplitude times the corresponding actual
non-anchor parameter coordinate. -/
theorem summandPolynomial_update (q₀ : Fin r → TensorIndex d n) (i : Fin r)
    (j : Fin d) (u : {u : Fin (n j) // u ≠ q₀ i j}) :
    summandPolynomial ℂ q₀ i (Function.update (q₀ i) j u.val) =
      MvPolynomial.X ⟨i, none⟩ * MvPolynomial.X ⟨i, some ⟨j,u⟩⟩ := by
  unfold summandPolynomial
  congr 1
  rw [Finset.prod_eq_single j]
  · simp [factorPolynomial, u.property]
  · intro b _hb hbj
    simp [Function.update_of_ne hbj, factorPolynomial]
  · simp

/-- Vanishing of every actual Segre coordinate jet forces the literal pivot
parameter direction to vanish whenever all amplitudes are nonzero. -/
theorem pivotJet_direction_zero (q₀ : Fin r → TensorIndex d n)
    (z v : Parameter ℂ q₀) (hz : ∀ i, z ⟨i,none⟩ ≠ 0)
    (hzero : ∀ i q, (pivotJet z v (summandPolynomial ℂ q₀ i q)).snd = 0) : v = 0 := by
  have ha (i : Fin r) : v ⟨i,none⟩ = 0 := by
    simpa using hzero i (q₀ i)
  ext c
  rcases c with ⟨i, _ | ⟨j,u⟩⟩
  · exact ha i
  · have h := hzero i (Function.update (q₀ i) j u.val)
    rw [summandPolynomial_update, map_mul, pivotJet_X, pivotJet_X] at h
    change z ⟨i,none⟩ * v ⟨i,some ⟨j,u⟩⟩ + v ⟨i,none⟩ * z ⟨i,some ⟨j,u⟩⟩ = 0 at h
    rw [ha, zero_mul, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (hz i)

#print axioms pivotSourceHom_coordinate
#print axioms pivotSourceHom_addition
#print axioms pivotJet_direction_zero
#assert_trust kernel pivotSourceHom_coordinate
#assert_trust kernel pivotSourceHom_addition
#assert_trust kernel pivotJet_direction_zero
end NLA.Proofs.TR06.UnramifiedDifferential
