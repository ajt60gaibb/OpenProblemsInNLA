/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.

Exact two-dimensional transfer algebra. Only fixed 2 by 2 expressions are
expanded; every arbitrary matrix power is first reduced to a linear span.
-/
import NLA.MF24.Definitions
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24
open scoped BigOperators

lemma matrix_two_square (R : Square 2) :
    R * R = (R 0 0 + R 1 1) • R +
      (R 0 1 * R 1 0 - R 0 0 * R 1 1) • (1 : Square 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  all_goals norm_num <;> ring

/-- The 2 by 2 Cayley--Hamilton reduction in a form that includes singular
matrices and the zeroth power, without division or selected eigenvalues. -/
lemma matrix_two_power_span (R : Square 2) (n : ℕ) :
    ∃ a b : ℂ, R ^ n = a • R + b • (1 : Square 2) := by
  induction n with
  | zero => exact ⟨0, 1, by simp⟩
  | succ n ih =>
      obtain ⟨a, b, hab⟩ := ih
      refine ⟨a * (R 0 0 + R 1 1) + b,
        a * (R 0 1 * R 1 0 - R 0 0 * R 1 1), ?_⟩
      rw [pow_succ, hab, add_mul, Matrix.smul_mul, Matrix.smul_mul,
        one_mul, matrix_two_square, smul_add, smul_smul, smul_smul]
      module

/-- Only the compressed commutator vanishes. The two transfer matrices need
not commute as matrices. This is an algebraic first coordinate, with no
complex conjugation and no restrictions on the parameters. -/
lemma transfer_compressed_commutator (P : Square 2) (u ρ a b : ℂ) :
    (Matrix.mulVec ((P * transferMatrix u ρ a) * (P * transferMatrix u ρ b))
      (Matrix.mulVec P (transferInitial u))) 0 =
    (Matrix.mulVec ((P * transferMatrix u ρ b) * (P * transferMatrix u ρ a))
      (Matrix.mulVec P (transferInitial u))) 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  dsimp [transferMatrix, transferInitial]
  ring

theorem transfer_bridge (P : Square 2) (u ρ a b : ℂ) (n : ℕ) :
    let R := P * transferMatrix u ρ a
    let S := P * transferMatrix u ρ b
    let v := Matrix.mulVec P (transferInitial u)
    (Matrix.mulVec (R ^ n * S) v) 0 = (Matrix.mulVec (S * R ^ n) v) 0 := by
  dsimp only
  obtain ⟨α, β, hpow⟩ := matrix_two_power_span (P * transferMatrix u ρ a) n
  rw [hpow]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one, Matrix.add_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [transfer_compressed_commutator]

#assert_trust kernel transfer_bridge
#print axioms transfer_bridge

end NLA.MF24
