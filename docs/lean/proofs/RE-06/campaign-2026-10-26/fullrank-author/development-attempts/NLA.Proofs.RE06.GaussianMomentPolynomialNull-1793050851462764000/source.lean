import Mathlib
import LeanCert.Tactic.Verification

/-! Nonzero polynomials vanish only on a null set under the actual finite
product standard Gaussian law. The proof uses finite roots and Tonelli. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace NLA.Proofs.RE06.GaussianMoment

theorem polynomial_eval_ne_zero_ae (P : Polynomial ℝ) (hP : P ≠ 0) :
    ∀ᵐ x ∂gaussianReal 0 1, P.eval x ≠ 0 := by
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  rw [ae_iff]
  simpa only [not_ne_iff, Polynomial.IsRoot] using
    (Polynomial.finite_setOfPred_isRoot hP).measure_zero (gaussianReal 0 1)

theorem mvPolynomial_eval_ne_zero_ae (d : ℕ) (P : MvPolynomial (Fin d) ℝ) (hP : P ≠ 0) :
    ∀ᵐ x : Fin d → ℝ ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1),
      MvPolynomial.eval x P ≠ 0 := by
  induction d with
  | zero =>
    apply Filter.Eventually.of_forall
    intro x hx
    apply hP
    apply MvPolynomial.funext
    intro y
    have he : y = x := Subsingleton.elim _ _
    simpa [he] using hx
  | succ d ih =>
    let Q := MvPolynomial.finSuccEquiv ℝ d P
    have hQ : Q ≠ 0 := by
      intro h
      apply hP
      apply (MvPolynomial.finSuccEquiv ℝ d).injective
      simpa [Q] using h
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Q.coeff k ≠ 0 := by
      by_contra h
      push Not at h
      exact hQ (Polynomial.ext (by simpa using h))
    have htail := ih (Q.coeff k) hk
    have htailhead : ∀ᵐ x : Fin d → ℝ ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1),
        ∀ᵐ y ∂gaussianReal 0 1, MvPolynomial.eval (Fin.cons y x) P ≠ 0 := by
      filter_upwards [htail] with x hx
      have hPx : Polynomial.map (MvPolynomial.eval x) Q ≠ 0 := by
        intro hz
        have hc := congrArg (fun R : Polynomial ℝ => R.coeff k) hz
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
        exact hx hc
      simpa only [MvPolynomial.eval_eq_eval_mv_eval', Q] using
        polynomial_eval_ne_zero_ae (Polynomial.map (MvPolynomial.eval x) Q) hPx
    have hcons : Continuous (fun z : ℝ × (Fin d → ℝ) =>
        (Fin.cons z.1 z.2 : Fin (d + 1) → ℝ)) := by
      apply continuous_pi
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using continuous_fst
      · simpa only [Fin.cons_succ, Function.comp_def] using (continuous_apply j).comp continuous_snd
    have hpair : MeasurableSet {z : ℝ × (Fin d → ℝ) |
        MvPolynomial.eval (Fin.cons z.1 z.2) P ≠ 0} :=
      (isOpen_ne_fun ((MvPolynomial.continuous_eval (p := P)).comp hcons) continuous_const).measurableSet
    have hprod : ∀ᵐ z ∂(gaussianReal 0 1).prod (Measure.pi (fun _ : Fin d => gaussianReal 0 1)),
        MvPolynomial.eval (Fin.cons z.1 z.2) P ≠ 0 :=
      (Measure.ae_prod_iff_ae_ae hpair).mpr ((Measure.ae_ae_comm hpair).mpr htailhead)
    have hsplit : HasLaw (fun z : ℝ × (Fin d → ℝ) => Fin.cons z.1 z.2)
        (Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1))
        ((gaussianReal 0 1).prod (Measure.pi (fun _ : Fin d => gaussianReal 0 1))) := by
      have hraw :=
        ((measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => gaussianReal 0 1) 0).symm).hasLaw
      convert hraw using 1
      funext z
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Fin.zero_succAbove, cast_eq]
      rfl
    have hm : Measurable (fun x : Fin (d + 1) → ℝ => MvPolynomial.eval x P ≠ 0) :=
      measurableSet_setOfPred.mp (isOpen_ne_fun (MvPolynomial.continuous_eval (p := P))
        continuous_const).measurableSet
    exact (hsplit.ae_iff hm).mp hprod

theorem mvPolynomial_fintype_eval_ne_zero_ae {ι : Type*} [Fintype ι]
    (P : MvPolynomial ι ℝ) (hP : P ≠ 0) :
    ∀ᵐ x : ι → ℝ ∂Measure.pi (fun _ : ι => gaussianReal 0 1), MvPolynomial.eval x P ≠ 0 := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let Q := MvPolynomial.rename e P
  have hQ : Q ≠ 0 := by
    intro h
    apply hP
    apply MvPolynomial.rename_injective e e.injective
    simpa [Q] using h
  have ha := mvPolynomial_eval_ne_zero_ae (Fintype.card ι) Q hQ
  have hsource : ∀ᵐ x : Fin (Fintype.card ι) → ℝ
      ∂Measure.pi (fun _ : Fin (Fintype.card ι) => gaussianReal 0 1),
      MvPolynomial.eval (fun i => x (e i)) P ≠ 0 := by
    simpa only [Q, MvPolynomial.eval_rename, Function.comp_def] using ha
  have hLaw : HasLaw (fun x : Fin (Fintype.card ι) → ℝ => fun i : ι => x (e i))
      (Measure.pi (fun _ : ι => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin (Fintype.card ι) => gaussianReal 0 1)) := by
    have hraw := (measurePreserving_piCongrLeft (α := fun _ : ι => ℝ)
      (fun _ : ι => gaussianReal 0 1) e.symm).hasLaw
    convert hraw using 1
    funext x i
    simpa only [Equiv.symm_apply_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply e.symm x (e i)).symm
  have hm : Measurable (fun x : ι → ℝ => MvPolynomial.eval x P ≠ 0) :=
    measurableSet_setOfPred.mp
      (isOpen_ne_fun (MvPolynomial.continuous_eval (p := P)) continuous_const).measurableSet
  exact (hLaw.ae_iff hm).mp hsource

#assert_trust kernel polynomial_eval_ne_zero_ae
#assert_trust kernel mvPolynomial_eval_ne_zero_ae
#assert_trust kernel mvPolynomial_fintype_eval_ne_zero_ae
#print axioms mvPolynomial_eval_ne_zero_ae
end NLA.Proofs.RE06.GaussianMoment
