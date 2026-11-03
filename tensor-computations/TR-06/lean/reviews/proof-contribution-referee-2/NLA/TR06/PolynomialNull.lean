/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical proof of TR-06: Matthew J. Colbrook.
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory
namespace NLA.TR06

/-- Complex polynomial evaluation along real coordinates is continuous. -/
theorem continuous_real_polynomial_eval {m : ℕ} (p : MvPolynomial (Fin m) ℂ) :
    Continuous (fun x : Fin m → ℝ => MvPolynomial.eval (fun i => (x i : ℂ)) p) :=
  (MvPolynomial.continuous_eval p).comp
    (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))

/-- Splitting off coordinate zero preserves ordinary product Lebesgue measure. -/
theorem measurePreserving_fin_cons (m : ℕ) :
    MeasurePreserving (fun z : (Fin m → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (m + 1) → ℝ)) volume volume := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0)
  have hs : MeasurePreserving (Prod.swap : (Fin m → ℝ) × ℝ → ℝ × (Fin m → ℝ))
      volume volume := Measure.measurePreserving_swap
  have hf : (fun z : (Fin m → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (m + 1) → ℝ)) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm ∘ Prod.swap := by
    funext z
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  rw [hf]
  exact h.comp hs

/-- A nonzero complex polynomial vanishes on a Lebesgue-null subset of real
coordinate space. No generic-rank or semialgebraic-volume conclusion is assumed. -/
theorem real_polynomial_zero_locus_null (m : ℕ) (p : MvPolynomial (Fin m) ℂ)
    (hp : p ≠ 0) :
    (volume : Measure (Fin m → ℝ))
      {x | MvPolynomial.eval (fun i => (x i : ℂ)) p = 0} = 0 := by
  classical
  induction m with
  | zero =>
    have hc : MvPolynomial.coeff 0 p ≠ 0 := by
      intro h
      apply hp
      rw [MvPolynomial.eq_C_of_isEmpty p, h, map_zero]
    have hempty : {x : Fin 0 → ℝ | MvPolynomial.eval (fun i => (x i : ℂ)) p = 0} = ∅ := by
      ext x
      rw [MvPolynomial.eq_C_of_isEmpty p]
      simp only [MvPolynomial.eval_C, hc, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
    rw [hempty, measure_empty]
  | succ m ih =>
    let P := MvPolynomial.finSuccEquiv ℂ m p
    have hP : P ≠ 0 := by
      intro h
      exact hp ((MvPolynomial.finSuccEquiv ℂ m).injective (h.trans (map_zero _).symm))
    obtain ⟨j, hj⟩ : ∃ j : ℕ, P.coeff j ≠ 0 := by
      by_contra! h
      apply hP
      apply Polynomial.ext
      intro j
      simpa only [Polynomial.coeff_zero] using h j
    have hcoeff : ∀ᵐ x : Fin m → ℝ ∂volume,
        MvPolynomial.eval (fun i => (x i : ℂ)) (P.coeff j) ≠ 0 := by
      rw [ae_iff]
      simpa using ih (P.coeff j) hj
    let S : Set (Fin (m + 1) → ℝ) :=
      {x | MvPolynomial.eval (fun i => (x i : ℂ)) p = 0}
    have hS : MeasurableSet S :=
      (isClosed_eq (continuous_real_polynomial_eval p) continuous_const).measurableSet
    have hcons := measurePreserving_fin_cons m
    rw [← hcons.measure_preimage hS.nullMeasurableSet]
    apply Measure.measure_prod_null_of_ae_null (hS.preimage hcons.measurable)
    filter_upwards [hcoeff] with x hx
    let Q : Polynomial ℂ := Polynomial.map (MvPolynomial.eval (fun i => (x i : ℂ))) P
    have hQ : Q ≠ 0 := by
      intro h
      have hc := congrArg (fun q : Polynomial ℂ => q.coeff j) h
      simp only [Q, Polynomial.coeff_map, Polynomial.coeff_zero] at hc
      exact hx hc
    have hfinite : {t : ℝ | Polynomial.eval (t : ℂ) Q = 0}.Finite := by
      exact Set.Finite.preimage Complex.ofReal_injective.injOn
        (Polynomial.finite_setOfPred_isRoot hQ)
    have hnull := hfinite.countable.measure_zero (volume : Measure ℝ)
    change volume {t : ℝ | MvPolynomial.eval
      (fun i => (((Fin.cons t x : Fin (m + 1) → ℝ) i) : ℂ)) p = 0} = 0
    have hset : {t : ℝ | MvPolynomial.eval
        (fun i => (((Fin.cons t x : Fin (m + 1) → ℝ) i) : ℂ)) p = 0} =
        {t : ℝ | Polynomial.eval (t : ℂ) Q = 0} := by
      ext t
      have heval : (fun i => (((Fin.cons t x : Fin (m + 1) → ℝ) i) : ℂ)) =
          (Fin.cons (t : ℂ) (fun i => (x i : ℂ)) : Fin (m + 1) → ℂ) := by
        funext i
        refine Fin.cases ?_ (fun k => ?_) i <;> simp
      simp only [Set.mem_ofPred_eq, heval, MvPolynomial.eval_eq_eval_mv_eval', Q, P]
    rw [hset]
    exact hnull

#print axioms continuous_real_polynomial_eval
#print axioms measurePreserving_fin_cons
#print axioms real_polynomial_zero_locus_null
#assert_trust kernel continuous_real_polynomial_eval
#assert_trust kernel measurePreserving_fin_cons
#assert_trust kernel real_polynomial_zero_locus_null
end NLA.TR06
