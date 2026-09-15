/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.

The semantic bridge uses Mathlib's complete ordered singular-value sequence.
Equal characteristic polynomials retain every repeated eigenvalue and zero.
-/
import NLA.MF24.Definitions
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24

lemma gram_operator_charpoly {N : ℕ} (A : Square N) :
    ((Matrix.toEuclideanLin A).adjoint.comp (Matrix.toEuclideanLin A)).charpoly =
      (gram A).charpoly := by
  have hg : Matrix.toEuclideanLin (gram A) =
      (Matrix.toEuclideanLin A).adjoint.comp (Matrix.toEuclideanLin A) := by
    change Matrix.toLpLin 2 2 (A.conjTranspose * A) = _
    rw [Matrix.toLpLin_mul_same]
    exact congrArg (fun F => F.comp (Matrix.toEuclideanLin A))
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A)
  rw [← hg]
  exact Matrix.charpoly_toLin (gram A) (PiLp.basisFun 2 ℂ (Fin N))

theorem gram_singular_bridge (N : ℕ) (A B : Square N)
    (h : (gram A).charpoly = (gram B).charpoly) :
    ∀ j : Fin N, singularValue A j = singularValue B j := by
  have hn : Module.finrank ℂ (EuclideanVector N) = N := finrank_euclideanSpace_fin
  have hc :
      ((Matrix.toEuclideanLin A).adjoint.comp (Matrix.toEuclideanLin A)).charpoly =
      ((Matrix.toEuclideanLin B).adjoint.comp (Matrix.toEuclideanLin B)).charpoly := by
    rw [gram_operator_charpoly, gram_operator_charpoly]
    exact h
  have he :=
    ((Matrix.toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvalues_eq_eigenvalues_iff
      hn (Matrix.toEuclideanLin B).isSymmetric_adjoint_comp_self hn).mpr hc
  intro j
  dsimp only [singularValue]
  rw [(Matrix.toEuclideanLin A).singularValues_fin hn j,
    (Matrix.toEuclideanLin B).singularValues_fin hn j]
  exact congrArg Real.sqrt (congrFun he j)

lemma spectralNorm_nonneg {N : ℕ} (A : Square N) : 0 ≤ spectralNorm A :=
  norm_nonneg _

lemma spectralNorm_eq_zero_iff {N : ℕ} (A : Square N) :
    spectralNorm A = 0 ↔ A = 0 := by
  unfold spectralNorm
  rw [norm_eq_zero]
  exact (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ)).map_eq_zero_iff

lemma spectralNorm_pos {N : ℕ} {A : Square N} (hA : A ≠ 0) :
    0 < spectralNorm A :=
  lt_of_le_of_ne (spectralNorm_nonneg A)
    (fun h => hA ((spectralNorm_eq_zero_iff A).mp h.symm))

#assert_trust kernel gram_singular_bridge
#print axioms gram_singular_bridge

end NLA.MF24
