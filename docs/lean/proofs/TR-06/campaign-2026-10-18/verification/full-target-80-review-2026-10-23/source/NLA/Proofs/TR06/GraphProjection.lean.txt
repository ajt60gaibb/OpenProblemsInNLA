/-
Copyright (c) 2026. Released under Apache 2.0 license.
Actual selected normalized-graph coordinate projections are quasi-finite at
actual real characters when their genuine projected derivative is injective.
-/
import NLA.Proofs.TR06.GraphProjectionJet
import NLA.Proofs.TR06.GraphProjectionFiniteType

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR06.GraphProjection
open NLA.TR06 NLA.TR06.Segre GraphAlgebra GraphCharacter
variable {d : ℕ} {n : Fin d → ℕ} {r k : ℕ}
attribute [local instance] RingHom.ker_isPrime

/-- The actual selected coordinate map on real pivot parameters. -/
def projectedValues (q₀ : Fin r → TensorIndex d n)
    (σ : Fin k ↪ OutputCoordinate d n r) (z : Parameter ℝ q₀) : Fin k → ℝ :=
  fun j => realGraphValues q₀ z (σ j)

/-- The projection polynomial ring acts through the actual graph coordinates. -/
def projectionHom (q₀ : Fin r → TensorIndex d n)
    (σ : Fin k ↪ OutputCoordinate d n r) : MvPolynomial (Fin k) ℂ →ₐ[ℂ] Source q₀ :=
  MvPolynomial.aeval (fun j => graphCoordinate q₀ (σ j))

theorem differentiableAt_realGraphValues (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) (hz : ∀ i, z ⟨i,none⟩ ≠ 0) (c : OutputCoordinate d n r) :
    DifferentiableAt ℝ (fun y => realGraphValues q₀ y c) z := by
  cases c with
  | inl q =>
    have h := (UnramifiedDifferential.contDiff_real_pivot_polynomial
      (sumPolynomial ℝ q₀ q) 1).differentiable one_ne_zero z
    simpa only [realGraphValues,eval_sumPolynomial] using h
  | inr c =>
    rcases c with ⟨i,q⟩
    have hs : Differentiable ℝ (fun y : Parameter ℝ q₀ => summands q₀ y i) := by
      apply (differentiable_piLp (p := 2)).mpr
      intro s
      have h := (UnramifiedDifferential.contDiff_real_pivot_polynomial
        (summandPolynomial ℝ q₀ i s) 1).differentiable one_ne_zero
      simpa only [eval_summandPolynomial] using h
    have hc : DifferentiableAt ℝ (fun y : Parameter ℝ q₀ => summands q₀ y i q) z := by
      simpa only [eval_summandPolynomial] using
        (UnramifiedDifferential.contDiff_real_pivot_polynomial
          (summandPolynomial ℝ q₀ i q) 1).differentiable one_ne_zero z
    have hn : DifferentiableAt ℝ (fun y : Parameter ℝ q₀ => ‖summands q₀ y i‖) z := ((Model.hasFDerivAt_norm_actual (summands q₀ z i)
      (summands_ne_zero q₀ z hz i)).comp z (hs z).hasFDerivAt).differentiableAt
    have hi : DifferentiableAt ℝ (fun y : Parameter ℝ q₀ => (‖summands q₀ y i‖)⁻¹) z :=
      (hasDerivAt_inv (norm_ne_zero_iff.mpr (summands_ne_zero q₀ z hz i))).differentiableAt.comp z hn
    convert! hc.mul hi using 1

theorem differentiableAt_projectedValues (q₀ : Fin r → TensorIndex d n)
    (σ : Fin k ↪ OutputCoordinate d n r) (z : Parameter ℝ q₀)
    (hz : ∀ i, z ⟨i,none⟩ ≠ 0) : DifferentiableAt ℝ (projectedValues q₀ σ) z :=
  differentiableAt_pi.mpr (fun j => differentiableAt_realGraphValues q₀ z hz (σ j))

/-- Genuine real projected derivative injectivity kills every actual complex
point derivation annihilating the selected graph coordinates. The real and
imaginary components produce two actual real derivative-kernel directions. -/
theorem point_derivation_zero_of_projected_fderiv_injective
    (q₀ : Fin r → TensorIndex d n) (σ : Fin k ↪ OutputCoordinate d n r)
    (z : Parameter ℝ q₀) (hz : ∀ i, z ⟨i,none⟩ ≠ 0)
    (hinj : Function.Injective (fderiv ℝ (projectedValues q₀ σ) z))
    (δ : Source q₀ →ₗ[ℂ] ℂ)
    (hmul : ∀ a b, δ (a*b) = character q₀ z hz a * δ b + character q₀ z hz b * δ a)
    (hbase : ∀ j, δ (graphCoordinate q₀ (σ j)) = 0) : δ = 0 := by
  have hdir (L : ℂ →ₗ[ℝ] ℝ) : direction q₀ δ L = 0 := by
    have hline : HasDerivAt (fun t : ℝ => projectedValues q₀ σ (z+t•direction q₀ δ L))
        (fun j => L (δ (graphCoordinate q₀ (σ j)))) 0 :=
      hasDerivAt_pi.mpr (fun j =>
        hasDerivAt_graphCoordinate_of_point_derivation q₀ z hz δ hmul L (σ j))
    have hp : HasDerivAt (fun t : ℝ => z+t•direction q₀ δ L) (direction q₀ δ L) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (direction q₀ δ L)).const_add z
    have hf : HasFDerivAt (projectedValues q₀ σ) (fderiv ℝ (projectedValues q₀ σ) z)
        (z+(0:ℝ)•direction q₀ δ L) := by
      simpa using (differentiableAt_projectedValues q₀ σ z hz).hasFDerivAt
    have hc := hf.comp_hasDerivAt 0 hp
    change HasDerivAt (fun t : ℝ => projectedValues q₀ σ (z+t•direction q₀ δ L))
      (fderiv ℝ (projectedValues q₀ σ) z (direction q₀ δ L)) 0 at hc
    have he := hc.unique hline
    have hv : fderiv ℝ (projectedValues q₀ σ) z (direction q₀ δ L) = 0 := by
      rw [he]
      funext j
      rw [hbase,map_zero]
      rfl
    exact hinj (by simpa only [map_zero] using hv)
  apply point_derivation_zero_of_pivot_variables q₀ z hz δ hmul
  intro c
  apply Complex.ext
  · exact congrArg (fun v : Parameter ℝ q₀ => v c) (hdir Complex.reLm)
  · exact congrArg (fun v : Parameter ℝ q₀ => v c) (hdir Complex.imLm)

/-- The actual selected projection is genuinely algebraically quasi-finite
at the actual positive-radius real point. Its derivative premise is local
geometric information to be supplied by the separate graph projection atlas. -/
theorem quasiFiniteAt_projection_of_fderiv_injective
    (q₀ : Fin r → TensorIndex d n) (σ : Fin k ↪ OutputCoordinate d n r)
    (z : Parameter ℝ q₀) (hz : ∀ i, z ⟨i,none⟩ ≠ 0)
    (hinj : Function.Injective (fderiv ℝ (projectedValues q₀ σ) z)) :
    (projectionHom q₀ σ).toRingHom.QuasiFiniteAt (RingHom.ker (character q₀ z hz).toRingHom) := by
  exact quasiFiniteAt_aeval_of_point_derivations
    (fun j => graphCoordinate q₀ (σ j)) (character q₀ z hz)
    (fun δ hmul hbase => point_derivation_zero_of_projected_fderiv_injective
      q₀ σ z hz hinj δ hmul hbase)

#print axioms point_derivation_zero_of_projected_fderiv_injective
#print axioms quasiFiniteAt_projection_of_fderiv_injective
#assert_trust kernel point_derivation_zero_of_projected_fderiv_injective
#assert_trust kernel quasiFiniteAt_projection_of_fderiv_injective
end NLA.Proofs.TR06.GraphProjection
