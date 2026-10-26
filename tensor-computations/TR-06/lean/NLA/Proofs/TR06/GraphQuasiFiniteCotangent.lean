/-
Copyright (c) 2026. Released under Apache 2.0 license.
Vanishing of actual relative point derivations kills the cotangent fiber.
-/
import Mathlib
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped TensorProduct
open TensorProduct
namespace NLA.Proofs.TR06.GraphQuasiFinite

/-- Actual relative derivations detect every linear functional on the actual
cotangent fiber. No topological local-injectivity hypothesis is used. -/
theorem cotangent_fiber_subsingleton_of_derivations
    {R S K : Type*} [CommRing R] [CommRing S] [Field K]
    [Algebra R S] [Algebra S K] [Algebra R K] [IsScalarTower R S K]
    (hD : ∀ D : Derivation R S K, D = 0) :
    Subsingleton (K ⊗[S] KaehlerDifferential R S) := by
  apply (Module.subsingleton_dual_iff K).mp
  apply subsingleton_of_forall_eq (0 : Module.Dual K (K ⊗[S] KaehlerDifferential R S))
  intro f
  let L : KaehlerDifferential R S →ₗ[S] K :=
    (f.restrictScalars S).comp (TensorProduct.mk S K (KaehlerDifferential R S) 1)
  have hL : L = 0 := by
    apply (KaehlerDifferential.linearMapEquivDerivation R S).injective
    exact (hD ((KaehlerDifferential.linearMapEquivDerivation R S) L)).trans
      (map_zero (KaehlerDifferential.linearMapEquivDerivation R S)).symm
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx,hy]
  | tmul a x =>
    have hx : f (1 ⊗ₜ[S] x) = 0 := LinearMap.congr_fun hL x
    have heq : a ⊗ₜ[S] x = a • (1 ⊗ₜ[S] x : K ⊗[S] KaehlerDifferential R S) := by
      simp only [smul_tmul', smul_eq_mul, mul_one]
    rw [heq, map_smul, hx, smul_zero]
    rfl

/-- Local Nakayama, already proved for actual finitely generated modules in
Mathlib, turns zero residue cotangent fiber into genuine unramifiedness. -/
theorem isUnramifiedAt_of_cotangent_fiber_subsingleton
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (q : Ideal S) [q.IsPrime]
    (hfiber : Subsingleton (q.ResidueField ⊗[S] KaehlerDifferential R S)) :
    Algebra.IsUnramifiedAt R q := by
  let p : PrimeSpectrum S := ⟨q,inferInstance⟩
  have hnot : p ∉ Module.support S (KaehlerDifferential R S) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.mpr hfiber
  have hmem : p ∈ Algebra.unramifiedLocus R S := by
    rw [Algebra.unramifiedLocus_eq_compl_support]
    exact hnot
  exact hmem

/-- Actual finite-type unramifiedness implies actual local quasi-finiteness. -/
theorem quasiFiniteAt_of_cotangent_fiber_subsingleton
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (q : Ideal S) [q.IsPrime]
    (hfiber : Subsingleton (q.ResidueField ⊗[S] KaehlerDifferential R S)) :
    Algebra.QuasiFiniteAt R q := by
  let : Algebra.IsUnramifiedAt R q := isUnramifiedAt_of_cotangent_fiber_subsingleton q hfiber
  infer_instance

#print axioms cotangent_fiber_subsingleton_of_derivations
#print axioms isUnramifiedAt_of_cotangent_fiber_subsingleton
#print axioms quasiFiniteAt_of_cotangent_fiber_subsingleton
#assert_trust kernel cotangent_fiber_subsingleton_of_derivations
#assert_trust kernel isUnramifiedAt_of_cotangent_fiber_subsingleton
#assert_trust kernel quasiFiniteAt_of_cotangent_fiber_subsingleton
end NLA.Proofs.TR06.GraphQuasiFinite
