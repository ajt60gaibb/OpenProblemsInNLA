/-
Gaussian nonsingularity from atomless independent entries.
Proof structure adapted from the local AI-assisted RRF formalization
RRF/Proofs/SketchRank.lean; source identity is retained in
source/gaussian-null-provenance.json. No RRF module or axiom is imported.
The exact statements were independently approved before implementation in
reviews/gaussian-nonsingularity-specification.md.
-/
import NLA.IE06.Definitions
import Mathlib

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped BigOperators
namespace NLA.IE06.GaussianNull

abbrev RectMat (m n : ℕ) := Fin m → Fin n → ℝ

def gaussianRect (m n : ℕ) : Measure (RectMat m n) :=
  Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => gaussianReal 0 1

/-- A nonzero polynomial does not vanish with positive probability under an
independent atomless real product law, including a zero-variable law. -/
theorem polynomial_ne_zero_ae (n : ℕ) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (P : MvPolynomial (Fin n) ℝ) (hP : P ≠ 0) :
    ∀ᵐ x ∂ Measure.pi μ, MvPolynomial.eval x P ≠ 0 := by
  classical
  induction n with
  | zero =>
    apply ae_of_all
    intro x hx
    have hconst := P.eq_C_of_isEmpty
    rw [hconst, MvPolynomial.eval_C] at hx
    apply hP
    simpa [hx] using hconst
  | succ n ih =>
    let Q := MvPolynomial.finSuccEquiv ℝ n P
    have hQ : Q ≠ 0 := by
      intro hz
      apply hP
      exact (MvPolynomial.finSuccEquiv ℝ n).injective (by simpa [Q] using hz)
    obtain ⟨d, hd⟩ : ∃ d : ℕ, Q.coeff d ≠ 0 := by
      by_contra h
      apply hQ
      apply Polynomial.ext
      intro d
      simp only [not_exists, not_not] at h
      simpa using h d
    have hcoef := ih (fun j : Fin n => μ j.succ) (Q.coeff d) hd
    have hcont : Continuous (fun z : ℝ × (Fin n → ℝ) =>
        MvPolynomial.eval (Fin.cons z.1 z.2) P) := by
      apply P.continuous_eval.comp
      apply continuous_pi
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact continuous_fst
      · exact (continuous_apply j).comp continuous_snd
    have hm : MeasurableSet {z : ℝ × (Fin n → ℝ) |
        MvPolynomial.eval (Fin.cons z.1 z.2) P ≠ 0} :=
      (isClosed_eq hcont continuous_const).measurableSet.compl
    have hae : ∀ᵐ z ∂ (μ 0).prod (Measure.pi fun j : Fin n => μ j.succ),
        MvPolynomial.eval (Fin.cons z.1 z.2) P ≠ 0 := by
      apply (ae_prod_iff_ae_ae hm).2
      apply (ae_ae_comm hm).2
      filter_upwards [hcoef] with x hx
      have hqx : Q.map (MvPolynomial.eval x) ≠ 0 := by
        intro hz
        have hd' := congrArg (fun q : Polynomial ℝ => q.coeff d) hz
        apply hx
        simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using hd'
      have hfinite := Polynomial.finite_setOfPred_isRoot hqx
      have hzero := hfinite.measure_zero (μ 0)
      have hne : ∀ᵐ y ∂ μ 0, (Q.map (MvPolynomial.eval x)).eval y ≠ 0 := by
        simpa only [ae_iff, not_not, Polynomial.IsRoot] using hzero
      filter_upwards [hne] with y hy
      simpa only [MvPolynomial.eval_eq_eval_mv_eval', Q] using hy
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
    have hmp := measurePreserving_piFinSuccAbove μ (0 : Fin (n+1))
    have hmap : Measure.map e (Measure.pi μ) =
        (μ 0).prod (Measure.pi fun j : Fin n => μ j.succ) := by
      simpa only [Fin.succAbove_zero] using hmp.map_eq
    rw [← hmap] at hae
    have hpull := ae_of_ae_map e.measurable.aemeasurable hae
    filter_upwards [hpull] with x hx
    have he : Fin.cons (e x).1 (e x).2 = x := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    simpa only [he] using hx


/-- The actual nested sketch law becomes the flat independent entry law. -/
theorem gaussian_uncurry_map (N ell : ℕ) :
    Measure.map (Function.uncurry : RectMat N ell → (Fin N × Fin ell → ℝ))
      (gaussianRect N ell) =
        Measure.pi (fun _ : Fin N × Fin ell => gaussianReal 0 1) := by
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  have hm : Measurable (Function.uncurry : RectMat N ell → (Fin N × Fin ell → ℝ)) := by
    apply measurable_pi_lambda
    intro ij
    exact (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1)
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hset : Function.uncurry ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i : Fin N => Set.univ.pi (fun j : Fin ell => s (i,j))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    exact ⟨fun h i j => h (i,j), fun h ij => h ij.1 ij.2⟩
  rw [hset]
  simp only [gaussianRect, Measure.pi_pi]
  simp only [Fintype.prod_prod_type]

def vectorize {N ell : ℕ} (Ω : RectMat N ell) : Fin (N*ell) → ℝ :=
  fun i => Ω (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

theorem gaussian_vectorize_map (N ell : ℕ) :
    Measure.map (@vectorize N ell) (gaussianRect N ell) =
      Measure.pi (fun _ : Fin (N*ell) => gaussianReal 0 1) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin (N*ell) => ℝ)
    (finProdFinEquiv : (Fin N × Fin ell) ≃ Fin (N*ell))
  have heq : (@vectorize N ell) = e ∘ Function.uncurry := by
    funext Ω z
    simp [vectorize, e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [heq, ← Measure.map_map e.measurable (by
    apply measurable_pi_lambda
    intro ij
    exact (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1))]
  rw [gaussian_uncurry_map]
  exact Measure.pi_map_piCongrLeft finProdFinEquiv (fun _ => gaussianReal 0 1)

/-- Polynomial for the fixed leading square minor, before drawing the sketch. -/
def minorPolynomial (N ell : ℕ) (h : ell ≤ N) : MvPolynomial (Fin (N*ell)) ℝ :=
  Matrix.det (fun i j : Fin ell => MvPolynomial.X (finProdFinEquiv (Fin.castLE h i, j)))

theorem eval_minorPolynomial (N ell : ℕ) (h : ell ≤ N) (x : Fin (N*ell) → ℝ) :
    MvPolynomial.eval x (minorPolynomial N ell h) =
      Matrix.det (fun i j : Fin ell => x (finProdFinEquiv (Fin.castLE h i, j))) := by
  unfold minorPolynomial
  erw [(MvPolynomial.eval x).map_det]
  congr 1
  change (fun i j : Fin ell => MvPolynomial.eval x (MvPolynomial.X (finProdFinEquiv (Fin.castLE h i, j)))) = _
  simp only [MvPolynomial.eval_X]

theorem minorPolynomial_ne_zero (N ell : ℕ) (h : ell ≤ N) : minorPolynomial N ell h ≠ 0 := by
  intro hp
  let x : Fin (N*ell) → ℝ := fun z =>
    if (finProdFinEquiv.symm z).1.val = (finProdFinEquiv.symm z).2.val then 1 else 0
  have hh := congrArg (MvPolynomial.eval x) hp
  rw [eval_minorPolynomial] at hh
  have hm : (fun i j : Fin ell => x (finProdFinEquiv (Fin.castLE h i, j))) =
      (1 : Matrix (Fin ell) (Fin ell) ℝ) := by
    ext i j
    simp only [x, Equiv.symm_apply_apply, Fin.val_castLE, Matrix.one_apply, Fin.ext_iff]
  rw [hm, Matrix.det_one, map_zero] at hh
  exact one_ne_zero hh

theorem gaussian_minor_det_ne_zero (N ell : ℕ) (h : ell ≤ N) :
    ∀ᵐ Ω ∂ gaussianRect N ell,
      Matrix.det (fun i j : Fin ell => Ω (Fin.castLE h i) j) ≠ 0 := by
  let _ : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hp := polynomial_ne_zero_ae (N*ell) (fun _ => gaussianReal 0 1)
    (minorPolynomial N ell h) (minorPolynomial_ne_zero N ell h)
  rw [← gaussian_vectorize_map] at hp
  have hm : Measurable (@vectorize N ell) := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  have hpull := ae_of_ae_map hm.aemeasurable hp
  filter_upwards [hpull] with Ω hΩ
  simpa only [eval_minorPolynomial, vectorize, Equiv.symm_apply_apply] using hΩ


#assert_trust kernel polynomial_ne_zero_ae
#assert_trust kernel gaussian_uncurry_map
#assert_trust kernel gaussian_vectorize_map
#assert_trust kernel eval_minorPolynomial
#assert_trust kernel minorPolynomial_ne_zero
#assert_trust kernel gaussian_minor_det_ne_zero
#print axioms polynomial_ne_zero_ae
#print axioms gaussian_minor_det_ne_zero
end NLA.IE06.GaussianNull

namespace NLA.IE06

theorem gaussianMatrix_singular_null_proved (n : ℕ) :
    gaussianMatrix n {A : Mat n | A.det = 0} = 0 := by
  have h := GaussianNull.gaussian_minor_det_ne_zero n n le_rfl
  have h' : ∀ᵐ A ∂ gaussianMatrix n, A.det ≠ 0 := by
    change ∀ᵐ A ∂ GaussianNull.gaussianRect n n, Matrix.det A ≠ 0
    filter_upwards [h] with A hA
    change (Matrix.det (fun i j : Fin n => A (Fin.castLE le_rfl i) j)) ≠ 0 at hA
    have heq : (fun i j : Fin n => A (Fin.castLE le_rfl i) j) = A := by
      funext i j
      rfl
    rw [heq] at hA
    exact hA
  simpa only [ae_iff, not_not] using h'

#assert_trust kernel gaussianMatrix_singular_null_proved
#print axioms gaussianMatrix_singular_null_proved
end NLA.IE06
