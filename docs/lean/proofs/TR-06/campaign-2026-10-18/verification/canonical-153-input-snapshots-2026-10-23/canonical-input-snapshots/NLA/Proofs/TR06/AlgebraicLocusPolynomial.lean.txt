import NLA.TR06.PolynomialNull
import NLA.TR06.SegreCoordinates
import NLA.TR06.NullImage
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Polynomial exceptional loci in the exact-dimensional real Euclidean
Segre parameters. No nullity in the ambient tensor dimension is used. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.AlgebraicLocus
open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory

theorem real_polynomial_zero_null_fintype {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℂ) (hp : p ≠ 0) :
    (volume : Measure (σ → ℝ)) {x | MvPolynomial.eval (fun i => (x i : ℂ)) p = 0} = 0 := by
  classical
  let e := Fintype.equivFin σ
  let p' := MvPolynomial.rename e p
  have hp' : p' ≠ 0 := by
    intro hzero
    apply hp
    apply MvPolynomial.rename_injective e e.injective
    exact hzero.trans (map_zero _).symm
  have hzero := NLA.TR06.real_polynomial_zero_locus_null (Fintype.card σ) p' hp'
  have hclosed : MeasurableSet {x : Fin (Fintype.card σ) → ℝ |
      MvPolynomial.eval (fun i => (x i : ℂ)) p' = 0} :=
    (isClosed_eq (NLA.TR06.continuous_real_polynomial_eval p') continuous_const).measurableSet
  have hpres := volume_measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card σ) => ℝ) e
  have hset : (MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card σ) => ℝ) e) ⁻¹'
      {x | MvPolynomial.eval (fun i => (x i : ℂ)) p' = 0} =
      {x : σ → ℝ | MvPolynomial.eval (fun i => (x i : ℂ)) p = 0} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,p',MvPolynomial.eval_rename,
      Function.comp_def,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply_apply]
  rw [← hset,hpres.measure_preimage hclosed.nullMeasurableSet]
  exact hzero

theorem real_polynomial_zero_null_euclidean {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℂ) (hp : p ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ σ))
      {z | MvPolynomial.eval (fun i => (z i : ℂ)) p = 0} = 0 := by
  have hcont : Continuous (fun x : σ → ℝ => MvPolynomial.eval (fun i => (x i : ℂ)) p) :=
    (MvPolynomial.continuous_eval p).comp
      (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))
  have hclosed : MeasurableSet {x : σ → ℝ |
      MvPolynomial.eval (fun i => (x i : ℂ)) p = 0} :=
    (isClosed_eq hcont continuous_const).measurableSet
  have h := (PiLp.volume_preserving_ofLp σ).measure_preimage hclosed.nullMeasurableSet
  rw [real_polynomial_zero_null_fintype p hp] at h
  exact h

theorem contDiff_real_polynomial {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℝ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (fun z : EuclideanSpace ℝ σ => MvPolynomial.eval (fun i => z i) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval_C] using
      (contDiff_const : ContDiff ℝ k (fun _ : EuclideanSpace ℝ σ => c))
  | add p q hp hq => simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p c hp =>
    simpa only [MvPolynomial.eval_mul,MvPolynomial.eval_X] using
      hp.mul (contDiff_piLp_apply (p := 2) (i := c))

theorem contDiff_segreSum {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (q₀ : Fin r → NLA.TR06.TensorIndex d n) (k : WithTop ℕ∞) :
    ContDiff ℝ k (NLA.TR06.Segre.sum (𝕜 := ℝ) q₀) := by
  apply (contDiff_piLp 2).mpr
  intro q
  simpa only [NLA.TR06.Segre.eval_sumPolynomial] using
    contDiff_real_polynomial (NLA.TR06.Segre.sumPolynomial ℝ q₀ q) k

#assert_trust kernel real_polynomial_zero_null_fintype
#assert_trust kernel real_polynomial_zero_null_euclidean
#assert_trust kernel contDiff_real_polynomial
#assert_trust kernel contDiff_segreSum
#print axioms real_polynomial_zero_null_euclidean
#print axioms contDiff_segreSum
end NLA.Proofs.TR06.AlgebraicLocus
