import NLA.Proofs.TR06.AlgebraicLocusPolynomial
import NLA.Proofs.TR06.AlgebraicLocusPullback

/-! Actual expected-dimensional Hausdorff nullity of bad sampling tensors,
using every finite Segre pivot pattern and source-dimensional null images. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.AlgebraicLocus
open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory Set NLA.TR06 NLA.TR06.Proposed
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem eval_real_pivot_pullback (q₀ : Fin r → TensorIndex d n)
    (p : MvPolynomial (TensorIndex d n) ℂ) (z : Segre.Parameter ℝ q₀) :
    MvPolynomial.eval (fun c => (z c : ℂ)) (Segre.pullback q₀ p) =
      MvPolynomial.eval (fun q => complexify (Segre.sum q₀ z) q) p := by
  have h := Segre.eval_pullback q₀ (Segre.complexParameter q₀ z) p
  rw [Segre.sum_complexParameter] at h
  exact h

theorem pivot_bad_image_null (q₀ : Fin r → TensorIndex d n)
    (p : MvPolynomial (TensorIndex d n) ℂ) (hp : Segre.pullback q₀ p ≠ 0) :
    (Measure.euclideanHausdorffMeasure (expectedDimension d n r) : Measure (Tensor ℝ d n))
      (Segre.sum q₀ '' {z : Segre.Parameter ℝ q₀ |
        MvPolynomial.eval (fun q => complexify (Segre.sum q₀ z) q) p = 0}) = 0 := by
  have hsource : (volume : Measure (Segre.Parameter ℝ q₀))
      {z | MvPolynomial.eval (fun q => complexify (Segre.sum q₀ z) q) p = 0} = 0 := by
    simpa only [eval_real_pivot_pullback] using
      real_polynomial_zero_null_euclidean (Segre.pullback q₀ p) hp
  have h := contDiff_image_null (Segre.sum q₀) _ (contDiff_segreSum q₀ 1) hsource
  rwa [(Segre.dimension_statement d n r q₀).2.1] at h

theorem decomposable_bad_hausdorff_null
    (p : MvPolynomial (TensorIndex d n) ℂ) (hp : additionAlgebraHom d n r p ≠ 0) :
    (Measure.euclideanHausdorffMeasure (expectedDimension d n r) : Measure (Tensor ℝ d n))
      {A | (∃ a : Fin r → Tensor ℝ d n, Decomposes a A) ∧
        MvPolynomial.eval (fun q => complexify A q) p = 0} = 0 := by
  classical
  have hcover : {A : Tensor ℝ d n | (∃ a : Fin r → Tensor ℝ d n, Decomposes a A) ∧
        MvPolynomial.eval (fun q => complexify A q) p = 0} ⊆
      ⋃ q₀ : Fin r → TensorIndex d n, Segre.sum q₀ ''
        {z : Segre.Parameter ℝ q₀ |
          MvPolynomial.eval (fun q => complexify (Segre.sum q₀ z) q) p = 0} := by
    rintro A ⟨⟨a,ha⟩,hbad⟩
    have hpivot (i : Fin r) : ∃ q : TensorIndex d n, a i q ≠ 0 := by
      by_contra! h
      apply (ha.1 i).1
      ext q
      exact h q
    choose q₀ hq₀ using hpivot
    obtain ⟨z,_hz,hz⟩ := Segre.represented_of_nonzero_pivots q₀ a ha.1 hq₀
    have hsum : Segre.sum q₀ z = A := by
      change (∑ i, Segre.summands q₀ z i) = A
      rw [hz]
      exact ha.2
    apply mem_iUnion.mpr
    refine ⟨q₀,z,?_,hsum⟩
    change MvPolynomial.eval (fun q => complexify (Segre.sum q₀ z) q) p = 0
    rwa [hsum]
  apply measure_mono_null hcover
  apply measure_iUnion_null
  intro q₀
  exact pivot_bad_image_null q₀ p (pivot_pullback_ne_zero_of_source_pullback q₀ p hp)

theorem measurableSet_real_polynomial_zero (p : MvPolynomial (TensorIndex d n) ℂ) :
    MeasurableSet {A : Tensor ℝ d n | MvPolynomial.eval (fun q => complexify A q) p = 0} := by
  have hcont : Continuous (fun A : Tensor ℝ d n =>
      MvPolynomial.eval (fun q => complexify A q) p) :=
    (MvPolynomial.continuous_eval p).comp
      (continuous_pi fun q => Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ q))
  exact (isClosed_eq hcont continuous_const).measurableSet

theorem sampling_bad_polynomial_null
    (p : MvPolynomial (TensorIndex d n) ℂ) (hp : additionAlgebraHom d n r p ≠ 0) :
    tensorVolume d n r {A | MvPolynomial.eval (fun q => complexify A q) p = 0} = 0 := by
  rw [tensorVolume,Measure.restrict_apply (measurableSet_real_polynomial_zero p)]
  have hsubset : {A : Tensor ℝ d n | MvPolynomial.eval (fun q => complexify A q) p = 0} ∩
      identifiableRealSet d n r ⊆
      {A | (∃ a : Fin r → Tensor ℝ d n, Decomposes a A) ∧
        MvPolynomial.eval (fun q => complexify A q) p = 0} :=
    fun A hA => ⟨hA.2.1.1,hA.1⟩
  exact measure_mono_null hsubset (decomposable_bad_hausdorff_null p hp)

theorem sampling_ae_polynomial_ne_zero
    (p : MvPolynomial (TensorIndex d n) ℂ) (hp : additionAlgebraHom d n r p ≠ 0) :
    ∀ᵐ A ∂tensorVolume d n r, MvPolynomial.eval (fun q => complexify A q) p ≠ 0 := by
  rw [ae_iff]
  simpa only [not_ne_iff] using sampling_bad_polynomial_null p hp

theorem exists_real_decomposition_good (hd : 0 < d)
    (q₀ : Fin r → TensorIndex d n) (p : MvPolynomial (TensorIndex d n) ℂ)
    (hp : additionAlgebraHom d n r p ≠ 0) :
    ∃ (A : Tensor ℝ d n) (a : Fin r → Tensor ℝ d n),
      Decomposes a A ∧ MvPolynomial.eval (fun q => complexify A q) p ≠ 0 := by
  obtain ⟨A,a,ha,hpA⟩ := exists_decomposition_eval_ne_zero_of_source_pullback q₀ p hp
  obtain ⟨z,_hz,hdec,hgood⟩ := Segre.real_witness_statement d n r hd q₀ p A a ha hpA
  exact ⟨Segre.sum q₀ z,Segre.summands q₀ z,hdec,hgood⟩

#assert_trust kernel eval_real_pivot_pullback
#assert_trust kernel pivot_bad_image_null
#assert_trust kernel decomposable_bad_hausdorff_null
#assert_trust kernel measurableSet_real_polynomial_zero
#assert_trust kernel sampling_bad_polynomial_null
#assert_trust kernel sampling_ae_polynomial_ne_zero
#assert_trust kernel exists_real_decomposition_good
#print axioms decomposable_bad_hausdorff_null
#print axioms sampling_ae_polynomial_ne_zero
#print axioms exists_real_decomposition_good
end NLA.Proofs.TR06.AlgebraicLocus
