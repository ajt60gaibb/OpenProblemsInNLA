/-
Copyright (c) 2026. Released under Apache 2.0 license.
Arbitrary real row projections of the actual normalized-graph coordinate ring.
-/
import NLA.Proofs.TR06.GraphProjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR06.GraphProjection
open NLA.TR06 NLA.TR06.Segre GraphAlgebra GraphCharacter
variable {d : ℕ} {n : Fin d → ℕ} {r k : ℕ}
attribute [local instance] RingHom.ker_isPrime

/-- Actual real row coordinates, allowing arbitrary Euclidean orthonormal
coordinate choices before selecting a finite coordinate projection. -/
def rowProjectedValues (q₀ : Fin r → TensorIndex d n)
    (rows : Fin k → OutputCoordinate d n r → ℝ) (z : Parameter ℝ q₀) : Fin k → ℝ :=
  fun j => ∑ c, rows j c * realGraphValues q₀ z c

/-- The exact same real rows act by complex linear combinations of the actual
algebraic graph coordinates. -/
def rowProjectionCoordinate (q₀ : Fin r → TensorIndex d n)
    (rows : Fin k → OutputCoordinate d n r → ℝ) (j : Fin k) : Source q₀ :=
  ∑ c, (rows j c : ℂ) • graphCoordinate q₀ c

def rowProjectionHom (q₀ : Fin r → TensorIndex d n)
    (rows : Fin k → OutputCoordinate d n r → ℝ) : MvPolynomial (Fin k) ℂ →ₐ[ℂ] Source q₀ :=
  MvPolynomial.aeval (rowProjectionCoordinate q₀ rows)

@[simp] theorem character_rowProjectionCoordinate (q₀ : Fin r → TensorIndex d n)
    (rows : Fin k → OutputCoordinate d n r → ℝ) (z : Parameter ℝ q₀)
    (hz : ∀ i, z ⟨i,none⟩ ≠ 0) (j : Fin k) :
    character q₀ z hz (rowProjectionCoordinate q₀ rows j) = (rowProjectedValues q₀ rows z j : ℂ) := by
  simp only [rowProjectionCoordinate,map_sum,map_smul,character_graphCoordinate,
    smul_eq_mul,rowProjectedValues,Complex.ofReal_sum,Complex.ofReal_mul]

/-- The true row-projected real graph is differentiable at all actual nonzero
amplitude data. -/
theorem differentiableAt_rowProjectedValues (q₀ : Fin r → TensorIndex d n)
    (rows : Fin k → OutputCoordinate d n r → ℝ) (z : Parameter ℝ q₀)
    (hz : ∀ i, z ⟨i,none⟩ ≠ 0) : DifferentiableAt ℝ (rowProjectedValues q₀ rows) z := by
  apply differentiableAt_pi.mpr
  intro j
  exact DifferentiableAt.fun_sum (fun c _ =>
    (differentiableAt_realGraphValues q₀ z hz c).const_mul (rows j c))

/-- Exact real-row jets of every real-linear component of an actual complex
point derivation. -/
theorem hasDerivAt_rowProjection_of_point_derivation
    (q₀ : Fin r → TensorIndex d n) (rows : Fin k → OutputCoordinate d n r → ℝ)
    (z : Parameter ℝ q₀) (hz : ∀ i, z ⟨i,none⟩ ≠ 0) (δ : Source q₀ →ₗ[ℂ] ℂ)
    (hmul : ∀ a b, δ (a*b) = character q₀ z hz a * δ b + character q₀ z hz b * δ a)
    (L : ℂ →ₗ[ℝ] ℝ) :
    HasDerivAt (fun t : ℝ => rowProjectedValues q₀ rows (z+t•direction q₀ δ L))
      (fun j => L (δ (rowProjectionCoordinate q₀ rows j))) 0 := by
  apply hasDerivAt_pi.mpr
  intro j
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun c _ =>
    (hasDerivAt_graphCoordinate_of_point_derivation q₀ z hz δ hmul L c).const_mul (rows j c))
  simpa only [rowProjectedValues,rowProjectionCoordinate,map_sum,map_smul,
    smul_eq_mul,realLinearMap_ofReal_mul] using h

/-- Actual projected derivative injectivity forces zero of every genuine
complex relative point derivation, for arbitrary fixed real row maps. -/
theorem point_derivation_zero_of_rowProjected_fderiv_injective
    (q₀ : Fin r → TensorIndex d n) (rows : Fin k → OutputCoordinate d n r → ℝ)
    (z : Parameter ℝ q₀) (hz : ∀ i, z ⟨i,none⟩ ≠ 0)
    (hinj : Function.Injective (fderiv ℝ (rowProjectedValues q₀ rows) z))
    (δ : Source q₀ →ₗ[ℂ] ℂ)
    (hmul : ∀ a b, δ (a*b) = character q₀ z hz a * δ b + character q₀ z hz b * δ a)
    (hbase : ∀ j, δ (rowProjectionCoordinate q₀ rows j) = 0) : δ = 0 := by
  have hdir (L : ℂ →ₗ[ℝ] ℝ) : direction q₀ δ L = 0 := by
    have hline := hasDerivAt_rowProjection_of_point_derivation q₀ rows z hz δ hmul L
    have hp : HasDerivAt (fun t : ℝ => z+t•direction q₀ δ L) (direction q₀ δ L) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (direction q₀ δ L)).const_add z
    have hf : HasFDerivAt (rowProjectedValues q₀ rows) (fderiv ℝ (rowProjectedValues q₀ rows) z)
        (z+(0:ℝ)•direction q₀ δ L) := by
      simpa using (differentiableAt_rowProjectedValues q₀ rows z hz).hasFDerivAt
    have hc := hf.comp_hasDerivAt 0 hp
    change HasDerivAt (fun t : ℝ => rowProjectedValues q₀ rows (z+t•direction q₀ δ L))
      (fderiv ℝ (rowProjectedValues q₀ rows) z (direction q₀ δ L)) 0 at hc
    have he := hc.unique hline
    have hv : fderiv ℝ (rowProjectedValues q₀ rows) z (direction q₀ δ L) = 0 := by
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

/-- The actual finite-type coordinate projection is quasi-finite at its actual
real character, whenever the genuine real row-projected derivative is injective.
The derivative premise is discharged by the separate geometric projection atlas. -/
theorem quasiFiniteAt_rowProjection_of_fderiv_injective
    (q₀ : Fin r → TensorIndex d n) (rows : Fin k → OutputCoordinate d n r → ℝ)
    (z : Parameter ℝ q₀) (hz : ∀ i, z ⟨i,none⟩ ≠ 0)
    (hinj : Function.Injective (fderiv ℝ (rowProjectedValues q₀ rows) z)) :
    (rowProjectionHom q₀ rows).toRingHom.QuasiFiniteAt (RingHom.ker (character q₀ z hz).toRingHom) := by
  exact quasiFiniteAt_aeval_of_point_derivations
    (rowProjectionCoordinate q₀ rows) (character q₀ z hz)
    (fun δ hmul hbase => point_derivation_zero_of_rowProjected_fderiv_injective
      q₀ rows z hz hinj δ hmul hbase)

#print axioms hasDerivAt_rowProjection_of_point_derivation
#print axioms point_derivation_zero_of_rowProjected_fderiv_injective
#print axioms quasiFiniteAt_rowProjection_of_fderiv_injective
#assert_trust kernel hasDerivAt_rowProjection_of_point_derivation
#assert_trust kernel point_derivation_zero_of_rowProjected_fderiv_injective
#assert_trust kernel quasiFiniteAt_rowProjection_of_fderiv_injective
end NLA.Proofs.TR06.GraphProjection
