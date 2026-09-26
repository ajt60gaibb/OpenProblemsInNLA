/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
-/
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.TR06

variable {R A K : Type*} [CommRing R] [CommRing A] [Field K]
  [Algebra R A] [Algebra R K] {N : ℕ}

/-- Evaluation on a spanning family embeds the space of R-linear maps into
K^N, even when the original R-module is not free. -/
def generatorEvaluation (g : Fin N → A) : (A →ₗ[R] K) →ₗ[K] (Fin N → K) where
  toFun h j := h (g j)
  map_add' h₁ h₂ := by ext j; rfl
  map_smul' c h := by ext j; rfl

theorem generatorEvaluation_injective (g : Fin N → A)
    (hg : Submodule.span R (Set.range g) = ⊤) :
    Function.Injective (generatorEvaluation (R := R) (K := K) g) := by
  intro h₁ h₂ heq
  exact LinearMap.ext_on_range hg (fun j => congrFun heq j)

/-- Uniform finite-subset character bound from a finite module generating
family. No freeness of A over R, finite field extension, or geometric fiber
identification is assumed. The R-algebra action on K may vary between uses. -/
theorem card_algHom_finset_le_of_span_eq_top (g : Fin N → A)
    (hg : Submodule.span R (Set.range g) = ⊤) (q : Finset (A →ₐ[R] K)) :
    q.card ≤ N := by
  classical
  have hind := (linearIndependent_algHom_toLinearMap R A K).comp
    (fun h : q => h.val) Subtype.val_injective
  have hev := hind.map' (generatorEvaluation (R := R) (K := K) g)
    (LinearMap.ker_eq_bot.mpr (generatorEvaluation_injective (R := R) (K := K) g hg))
  have hcard := hev.fintype_card_le_finrank
  simpa only [Fintype.card_coe, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hcard

#print axioms generatorEvaluation_injective
#print axioms card_algHom_finset_le_of_span_eq_top
#assert_trust kernel generatorEvaluation_injective
#assert_trust kernel card_algHom_finset_le_of_span_eq_top
end NLA.TR06
