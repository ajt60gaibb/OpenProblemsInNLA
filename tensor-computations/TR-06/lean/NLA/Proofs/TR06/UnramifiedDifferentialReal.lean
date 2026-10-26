/-
Copyright (c) 2026. Released under Apache 2.0 license.
Actual real derivative injectivity and the retained ordered-pivot coordinate
bridge, using the genuine nonzero unramified addition denominator.
-/
import NLA.Proofs.TR06.UnramifiedDifferentialGoodLocus
import NLA.Proofs.TR06.UnramifiedDifferentialRealJet
import NLA.TR06.RankOneCharts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open NLA.TR06 NLA.TR06.Segre NLA.TR06.Proposed
namespace NLA.Proofs.TR06.UnramifiedDifferential

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- Literal flattening of amplitude and non-anchor entries into the actual
Euclidean Segre parameter space. This changes no mathematical coordinate. -/
def pivotParameterLinearEquiv (q₀ : Fin r → TensorIndex d n) :
    OrderedPivotData q₀ ≃ₗ[ℝ] Parameter ℝ q₀ where
  toFun p := WithLp.toLp 2 (fun c => c.2.elim (p c.1).1 (p c.1).2)
  invFun z := fun i => (z ⟨i,none⟩, fun t => z ⟨i,some t⟩)
  left_inv p := by funext i; apply Prod.ext <;> rfl
  right_inv z := by ext c; rcases c with ⟨i,_ | t⟩ <;> rfl
  map_add' p q := by ext c; rcases c with ⟨i,_ | t⟩ <;> rfl
  map_smul' t p := by ext c; rcases c with ⟨i,_ | s⟩ <;> rfl

/-- The flattening is an actual continuous linear equivalence between the
finite-dimensional normed spaces used by the two retained interfaces. -/
def pivotParameterEquiv (q₀ : Fin r → TensorIndex d n) :
    OrderedPivotData q₀ ≃L[ℝ] Parameter ℝ q₀ :=
  (pivotParameterLinearEquiv q₀).toContinuousLinearEquiv

@[simp] theorem pivotParameterEquiv_amplitude (q₀ : Fin r → TensorIndex d n)
    (p : OrderedPivotData q₀) (i : Fin r) : pivotParameterEquiv q₀ p ⟨i,none⟩ = (p i).1 := rfl

@[simp] theorem summands_pivotParameterEquiv (q₀ : Fin r → TensorIndex d n)
    (p : OrderedPivotData q₀) (i : Fin r) :
    summands q₀ (pivotParameterEquiv q₀ p) i = tensorFromPivotData (q₀ i) (p i) := by
  ext q
  change (p i).1 * (∏ j, factor q₀ (pivotParameterEquiv q₀ p) i j (q j)) = _
  change _ = (p i).1 * ∏ j, expandedPivotFactors (q₀ i) (p i).2 j (q j)
  congr 1

@[simp] theorem sum_pivotParameterEquiv (q₀ : Fin r → TensorIndex d n)
    (p : OrderedPivotData q₀) : sum q₀ (pivotParameterEquiv q₀ p) = pivotSum q₀ p := by
  unfold sum pivotSum
  apply Finset.sum_congr rfl
  intro i _
  exact summands_pivotParameterEquiv q₀ p i

/-- The same genuine unramified denominator controls the actual real Jacobian. -/
theorem fderiv_real_pivot_sum_injective_of_unramified
    (t : AdditionImage d n r)
    (hunram : Algebra.FormallyUnramified (Localization.Away t)
      (Localization (Algebra.algebraMapSubmonoid (SegreSource d n r) (Submonoid.powers t))))
    (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d) (z : Parameter ℝ q₀)
    (hz : ∀ i, z ⟨i,none⟩ ≠ 0)
    (hden : sourceCharacter q₀ j₀ (complexParameter q₀ z) t.val ≠ 0) :
    Function.Injective (fderiv ℝ (sum q₀) z) := by
  have hker (v : Parameter ℝ q₀) (hv : fderiv ℝ (sum q₀) z v = 0) : v = 0 := by
    have hzero := pivot_direction_zero_of_unramified t hunram q₀ j₀
      (complexParameter q₀ z) (complexParameter q₀ v)
      (by intro i; change ((z ⟨i,none⟩ : ℝ) : ℂ) ≠ 0; exact_mod_cast hz i) hden
      (pivotJet_sum_zero_of_real_fderiv_eq_zero q₀ z v hv)
    ext c
    have hc := congrArg (fun w : Parameter ℂ q₀ => w c) hzero
    exact Complex.ofReal_injective hc
  intro x y hxy
  have hv : fderiv ℝ (sum q₀) z (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hker (x-y) hv)

/-- Actual real ordered-pivot derivative injectivity, in precisely the
coordinate space consumed by the retained proper-immersion chart theorem. -/
theorem fderiv_ordered_pivotSum_injective_of_unramified
    (t : AdditionImage d n r)
    (hunram : Algebra.FormallyUnramified (Localization.Away t)
      (Localization (Algebra.algebraMapSubmonoid (SegreSource d n r) (Submonoid.powers t))))
    (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d) (p : OrderedPivotData q₀)
    (hp : ∀ i, (p i).1 ≠ 0)
    (hden : sourceCharacter q₀ j₀ (complexParameter q₀ (pivotParameterEquiv q₀ p)) t.val ≠ 0) :
    Function.Injective (fderiv ℝ (pivotSum q₀) p) := by
  let e := pivotParameterEquiv q₀
  have h := fderiv_real_pivot_sum_injective_of_unramified t hunram q₀ j₀ (e p)
    (by simpa [e] using hp) hden
  have hc := (differentiable_real_pivot_sum q₀ (e p)).hasFDerivAt.comp p e.hasFDerivAt
  have heq : (fun p : OrderedPivotData q₀ => sum q₀ (e p)) = pivotSum q₀ := by
    funext p
    exact sum_pivotParameterEquiv q₀ p
  change HasFDerivAt (fun p : OrderedPivotData q₀ => sum q₀ (e p))
    ((fderiv ℝ (sum q₀) (e p)).comp e.toContinuousLinearMap) p at hc
  rw [heq] at hc
  rw [hc.fderiv]
  intro x y hxy
  exact e.injective (h hxy)

/-- The original generic complex hypothesis supplies an actual ambient
polynomial denominator, nonzero on the addition image, whose nonvanishing
forces injectivity of every actual real ordered-pivot addition derivative. -/
theorem exists_ambient_real_derivative_denominator (hd : 0 < d)
    (hgeneric : GenericComplexIdentifiable d n r) :
    ∃ P : MvPolynomial (TensorIndex d n) ℂ,
      additionAlgebraHom d n r P ≠ 0 ∧
      ∀ (q₀ : Fin r → TensorIndex d n) (p : OrderedPivotData q₀),
        (∀ i, (p i).1 ≠ 0) →
        MvPolynomial.eval (fun q => complexify (pivotSum q₀ p) q) P ≠ 0 →
        Function.Injective (fderiv ℝ (pivotSum q₀) p) := by
  obtain ⟨t,ht,hu⟩ := exists_unramified_addition_denominator hd hgeneric
  obtain ⟨P,hP⟩ := t.property
  change additionAlgebraHom d n r P = t.val at hP
  refine ⟨P,?_,?_⟩
  · rw [hP]
    exact fun h => ht (Subtype.ext h)
  · intro q₀ p hp hden
    let j₀ : Fin d := ⟨0,hd⟩
    apply fderiv_ordered_pivotSum_injective_of_unramified t hu q₀ j₀ p hp
    rw [← hP, sourceCharacter_addition_polynomial, sum_complexParameter,
      sum_pivotParameterEquiv]
    exact hden

#print axioms pivotParameterEquiv
#print axioms fderiv_real_pivot_sum_injective_of_unramified
#print axioms fderiv_ordered_pivotSum_injective_of_unramified
#print axioms exists_ambient_real_derivative_denominator
#assert_trust kernel pivotParameterEquiv
#assert_trust kernel fderiv_real_pivot_sum_injective_of_unramified
#assert_trust kernel fderiv_ordered_pivotSum_injective_of_unramified
#assert_trust kernel exists_ambient_real_derivative_denominator
end NLA.Proofs.TR06.UnramifiedDifferential
