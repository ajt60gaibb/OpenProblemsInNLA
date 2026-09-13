/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

The arbitrary selected spectral decomposition gives the genuine CFC.
The uniqueness construction adapts the architecture of Mathlib's
Analysis/Matrix/HermitianFunctionalCalculus.lean by Jon Bannon and Jireh
Loreaux (Apache 2.0), replacing the preferred eigenbasis with the complete
reviewed OrderedSpectralData. No continuity assumption on a bare function
is needed because the actual matrix spectrum is finite.
-/
import NLA.RA08.Definitions
import Mathlib.Tactic.FunProp
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
open Matrix Unitary Topology
noncomputable section
namespace NLA.RA08

theorem selected_data_psd {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A) : A.PosSemidef := by
  have h := (Matrix.PosSemidef.diagonal d.nonnegative).mul_mul_conjTranspose_same
    (d.orthogonal : RealMatrix n)
  have he : (d.orthogonal : RealMatrix n) * diagonal d.eigenvalues *
      (d.orthogonal : RealMatrix n).conjTranspose = A := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using d.reconstruct.symm
  rwa [he] at h

theorem selected_data_spectrum {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A) :
    spectrum ℝ A = Set.range d.eigenvalues := by
  calc
    spectrum ℝ A = spectrum ℝ
      ((d.orthogonal : RealMatrix n) * diagonal d.eigenvalues *
        (star d.orthogonal : RealMatrix n)) := by
      have he := congrArg (fun X : RealMatrix n => spectrum ℝ X) d.reconstruct
      simpa only [Unitary.coe_star, star_eq_conjTranspose,
        conjTranspose_eq_transpose_of_trivial] using he
    _ = spectrum ℝ (diagonal d.eigenvalues) := Unitary.spectrum_star_right_conjugate
    _ = Set.range d.eigenvalues := spectrum_diagonal d.eigenvalues

def selectedEvaluation {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A) :
    C(spectrum ℝ A, ℝ) →⋆ₐ[ℝ] (Fin n → ℝ) where
  toFun g := fun i => g ⟨d.eigenvalues i,
    (selected_data_spectrum d).symm ▸ Set.mem_range_self i⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def realDiagonalStarAlgHom (n : ℕ) : (Fin n → ℝ) →⋆ₐ[ℝ] RealMatrix n :=
  { Matrix.diagonalAlgHom (n := Fin n) (α := ℝ) ℝ with
    map_star' := by
      intro f
      change diagonal (star f) = (diagonal f).conjTranspose
      rw [diagonal_conjTranspose] }

def selectedCfcAux {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A) :
    C(spectrum ℝ A, ℝ) →⋆ₐ[ℝ] RealMatrix n :=
  (Unitary.conjStarAlgAut ℝ (RealMatrix n) d.orthogonal).toStarAlgHom.comp
    ((realDiagonalStarAlgHom n).comp (selectedEvaluation d))

theorem selectedCfcAux_continuous {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A) :
    Continuous (selectedCfcAux d) := by
  have : FiniteDimensional ℝ C(spectrum ℝ A, ℝ) :=
    FiniteDimensional.of_injective (ContinuousMap.coeFnLinearMap ℝ (M := ℝ)) DFunLike.coe_injective
  exact (selectedCfcAux d).toLinearMap.continuous_of_finiteDimensional

theorem selectedCfcAux_id {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A) :
    selectedCfcAux d (.restrict (spectrum ℝ A) (.id ℝ)) = A := by
  change Unitary.conjStarAlgAut ℝ (RealMatrix n) d.orthogonal (diagonal d.eigenvalues) = A
  simpa only [Unitary.conjStarAlgAut_apply,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    using d.reconstruct.symm

theorem selected_cfc_eq {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A) (f : ℝ → ℝ) :
    functionalCalculus f A = spectralCombination d (fun i => f (d.eigenvalues i)) := by
  have hA : IsSelfAdjoint A := (selected_data_psd d).isHermitian
  have haux := cfcHom_eq_of_continuous_of_map_id hA (selectedCfcAux d)
    (selectedCfcAux_continuous d) (selectedCfcAux_id d)
  have hf : ContinuousOn f (spectrum ℝ A) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  unfold functionalCalculus
  rw [cfc_apply f A hA hf, haux]
  change Unitary.conjStarAlgAut ℝ (RealMatrix n) d.orthogonal
      (diagonal (fun i => f (d.eigenvalues i))) =
    spectralCombination d (fun i => f (d.eigenvalues i))
  simp only [Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    spectralCombination]

theorem functionalCalculus_spectral_proved {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) :
    functionalCalculus f A = spectralCombination d (fun i => f (d.eigenvalues i)) ∧
      (∀ g : ℝ → ℝ, Set.EqOn f g (Set.Ici 0) →
        functionalCalculus f A = functionalCalculus g A) := by
  refine ⟨selected_cfc_eq d f, ?_⟩
  intro g hfg
  rw [selected_cfc_eq d f, selected_cfc_eq d g]
  have h : (fun i => f (d.eigenvalues i)) = (fun i => g (d.eigenvalues i)) := by
    funext i
    exact hfg (d.nonnegative i)
  rw [h]

#assert_trust kernel selected_data_spectrum
#assert_trust kernel selectedCfcAux_continuous
#assert_trust kernel selectedCfcAux_id
#assert_trust kernel selected_cfc_eq
#assert_trust kernel functionalCalculus_spectral_proved
#print axioms selected_data_spectrum
#print axioms selectedCfcAux_continuous
#print axioms selectedCfcAux_id
#print axioms selected_cfc_eq
#print axioms functionalCalculus_spectral_proved

end NLA.RA08
