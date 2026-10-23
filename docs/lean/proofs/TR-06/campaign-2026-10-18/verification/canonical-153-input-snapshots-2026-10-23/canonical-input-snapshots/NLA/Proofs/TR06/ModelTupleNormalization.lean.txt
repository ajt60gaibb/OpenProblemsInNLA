import NLA.Proofs.TR06.ModelNormalization
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-! Exact derivative of the actual individually normalized tuple. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.Model
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- No maximum norm is substituted for the actual l2 output norm. -/
def tupleNormalizationDerivative (a : Fin r → NLA.TR06.Tensor ℝ d n) :
    (Fin r → NLA.TR06.Tensor ℝ d n) →L[ℝ] NLA.TR06.AngularOutput d n r :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r × NLA.TR06.TensorIndex d n => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun q => (PiLp.proj 2 (fun _ : NLA.TR06.TensorIndex d n => ℝ) q.2).comp
      ((normalizationDerivative (a q.1)).comp (ContinuousLinearMap.proj q.1))))

theorem tupleNormalizationDerivative_apply
    (a v : Fin r → NLA.TR06.Tensor ℝ d n) :
    tupleNormalizationDerivative a v = NLA.Statements.TR06.AngularProductVariation a v := by
  ext q
  exact normalizationDerivative_eq_variation (a q.1) (v q.1) |>
    congrArg (fun x : NLA.TR06.Tensor ℝ d n => x q.2)

theorem hasFDerivAt_normalizedTuple (a : Fin r → NLA.TR06.Tensor ℝ d n)
    (ha : ∀ i, a i ≠ 0) :
    HasFDerivAt NLA.TR06.normalizedTuple (tupleNormalizationDerivative a) a := by
  let g := fun b : Fin r → NLA.TR06.Tensor ℝ d n =>
    fun q : Fin r × NLA.TR06.TensorIndex d n => normalize (b q.1) q.2
  have hg : HasFDerivAt g (ContinuousLinearMap.pi (fun q =>
      (PiLp.proj 2 (fun _ : NLA.TR06.TensorIndex d n => ℝ) q.2).comp
        ((normalizationDerivative (a q.1)).comp (ContinuousLinearMap.proj q.1)))) a := by
    apply hasFDerivAt_pi.mpr
    intro q
    have hp := hasFDerivAt_apply (𝕜 := ℝ) q.1 a
    have hn := (hasFDerivAt_normalize (a q.1) (ha q.1)).comp a hp
    exact (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (normalize (a q.1)) q.2).comp a hn
  have h := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (g a)).comp a hg
  convert! h using 1
  funext b
  ext q
  simp [NLA.TR06.normalizedTuple,g,normalize,div_eq_mul_inv,mul_comm]

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The chain rule for arbitrary actual differentiable summand branches. -/
theorem fderiv_normalizedTuple_apply
    (a : H → Fin r → NLA.TR06.Tensor ℝ d n) (x w : H)
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x) (hne : ∀ i, a x i ≠ 0) :
    fderiv ℝ (fun y => NLA.TR06.normalizedTuple (a y)) x w =
      NLA.Statements.TR06.AngularProductVariation (a x)
        (fun i => fderiv ℝ (fun y => a y i) x w) := by
  have ha' : DifferentiableAt ℝ a x := differentiableAt_pi.mpr ha
  change (fderiv ℝ (NLA.TR06.normalizedTuple ∘ a) x) w = _
  rw [((hasFDerivAt_normalizedTuple (a x) hne).comp x ha'.hasFDerivAt).fderiv]
  change tupleNormalizationDerivative (a x) (fderiv ℝ a x w) = _
  rw [tupleNormalizationDerivative_apply]
  congr 1
  funext i
  exact congrArg (fun L : H →L[ℝ] NLA.TR06.Tensor ℝ d n => L w)
    (fderiv_apply ha' i).symm

#assert_trust kernel tupleNormalizationDerivative_apply
#assert_trust kernel hasFDerivAt_normalizedTuple
#assert_trust kernel fderiv_normalizedTuple_apply
#print axioms fderiv_normalizedTuple_apply
end NLA.Proofs.TR06.Model
