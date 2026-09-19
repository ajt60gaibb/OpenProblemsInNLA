/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Actual affine coordinate normalization in the planar implementation of
Matthew J. Colbrook's NR-04 argument, University of Cambridge. The center
is an actual selected family point, and other images have positive x.
-/
import NLA.NR04.PlaneSeparation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.NR04

/-- The actual linear shear `(x,y) ↦ (x+t*y,y)`. -/
def planeShear (t : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun p := ![planeFirst t p, p 1]
  map_add' p q := by
    funext i
    fin_cases i <;> simp [planeFirst] <;> ring
  map_smul' a p := by
    funext i
    fin_cases i <;> simp [planeFirst, smul_eq_mul] <;> ring

/-- Translate the selected center to zero, then apply the actual linear shear. -/
def planeShearShift (t : ℝ) (o : Fin 2 → ℝ) :
    (Fin 2 → ℝ) →ᵃ[ℝ] (Fin 2 → ℝ) :=
  (planeShear t).toAffineMap.comp (AffineEquiv.vaddConst ℝ (-o)).toAffineMap

lemma plane_shear_shift_apply_zero (t : ℝ) (o p : Fin 2 → ℝ) :
    planeShearShift t o p 0 = planeFirst t p - planeFirst t o := by
  change (p 0 + -o 0) + t * (p 1 + -o 1) =
    (p 0 + t * p 1) - (o 0 + t * o 1)
  ring

lemma plane_shear_shift_apply_one (t : ℝ) (o p : Fin 2 → ℝ) :
    planeShearShift t o p 1 = p 1 - o 1 := by
  change p 1 + -o 1 = p 1 - o 1
  ring

lemma plane_shear_shift_center (t : ℝ) (o : Fin 2 → ℝ) :
    planeShearShift t o o = 0 := by
  funext i
  fin_cases i
  · change planeShearShift t o o 0 = (0 : ℝ)
    rw [plane_shear_shift_apply_zero]
    exact sub_self _
  · change planeShearShift t o o 1 = (0 : ℝ)
    rw [plane_shear_shift_apply_one]
    exact sub_self _

lemma plane_shear_shift_injective (t : ℝ) (o : Fin 2 → ℝ) :
    Function.Injective (planeShearShift t o) := by
  intro p q heq
  have hy := congrFun heq 1
  rw [plane_shear_shift_apply_one, plane_shear_shift_apply_one] at hy
  have hy' : p 1 = q 1 := by linarith only [hy]
  have hx := congrFun heq 0
  rw [plane_shear_shift_apply_zero, plane_shear_shift_apply_zero] at hx
  have hfirst : planeFirst t p = planeFirst t q := by linarith only [hx]
  have hx' : p 0 = q 0 := by
    dsimp [planeFirst] at hfirst
    rw [hy'] at hfirst
    linarith only [hfirst]
  funext i
  fin_cases i
  · exact hx'
  · exact hy'

/-- Generic finite separation and its strict minimum produce an injective
affine normalization with one actual origin and positive x on every other point. -/
theorem finite_plane_family_positive_shear {n : ℕ}
    (w : Fin n → Fin 2 → ℝ) (hw : Function.Injective w) (hn : 0 < n) :
    ∃ t : ℝ, ∃ i0 : Fin n,
      Function.Injective (planeShearShift t (w i0)) ∧
      planeShearShift t (w i0) (w i0) = 0 ∧
      (∀ i, i ≠ i0 → 0 < planeShearShift t (w i0) (w i) 0) ∧
      Function.Injective (fun i => planeShearShift t (w i0) (w i)) := by
  obtain ⟨t, hsep⟩ := finite_plane_family_separating_coordinate w hw
  obtain ⟨i0, hmin⟩ := separated_plane_family_strict_minimum w t hsep hn
  refine ⟨t, i0, plane_shear_shift_injective t (w i0),
    plane_shear_shift_center t (w i0), ?_, ?_⟩
  · intro i hi
    rw [plane_shear_shift_apply_zero]
    exact sub_pos.mpr (hmin i hi)
  · exact (plane_shear_shift_injective t (w i0)).comp hw

#print axioms plane_shear_shift_apply_zero
#print axioms plane_shear_shift_apply_one
#print axioms plane_shear_shift_center
#print axioms plane_shear_shift_injective
#print axioms finite_plane_family_positive_shear
#assert_trust kernel plane_shear_shift_apply_zero
#assert_trust kernel plane_shear_shift_apply_one
#assert_trust kernel plane_shear_shift_center
#assert_trust kernel plane_shear_shift_injective
#assert_trust kernel finite_plane_family_positive_shear

end NLA.NR04
