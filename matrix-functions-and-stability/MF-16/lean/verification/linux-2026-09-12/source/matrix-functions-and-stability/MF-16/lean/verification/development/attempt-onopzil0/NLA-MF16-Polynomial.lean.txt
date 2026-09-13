/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Mathematical counterexample: Matthew J. Colbrook. The polynomial system is a
reviewed certificate adaptation; every connection to actual matrix operations
is proved here and in the Cayley–Hamilton bridge.
-/
import NLA.MF16.Algebra

set_option autoImplicit false
noncomputable section
namespace NLA.MF16
open LeanCert.Core LeanCert.Engine

@[simp] theorem linearCoefficientExpr_eval (ρ : ℕ → ℝ) (e : Expr) :
    Expr.eval ρ (linearCoefficientExpr e) = linearCoefficient (Expr.eval ρ e) := by
  simp [linearCoefficientExpr,linearCoefficient,exprSub,sub_eq_add_neg]

@[simp] theorem identityCoefficientExpr_eval (ρ : ℕ → ℝ) (e : Expr) :
    Expr.eval ρ (identityCoefficientExpr e) = identityCoefficient (Expr.eval ρ e) := by
  simp [identityCoefficientExpr,identityCoefficient,exprSub,exprScale,sub_eq_add_neg]

/-- An intermediate actual matrix product; equality to the original word will
be derived from Cayley–Hamilton when the first system equation gives det(S)=3. -/
def reducedWord (v : Fin 3 → ℝ) : RealMatrix :=
  symmetricMatrix v * realB *
    (linearCoefficient (Matrix.trace (symmetricMatrix v)) • symmetricMatrix v -
      identityCoefficient (Matrix.trace (symmetricMatrix v)) • (1 : RealMatrix)) *
    realB * symmetricMatrix v

theorem polynomial_eval_zero (v : Fin 3 → ℝ) :
    evalFin (polynomialSystem 0) v = (symmetricMatrix v).det - 3 := by
  simp [polynomialSystem,evalFin,finEnv,exprSub,exprScale,
    symmetricMatrix,Matrix.det_fin_two,sub_eq_add_neg]

theorem polynomial_eval_one (v : Fin 3 → ℝ) :
    evalFin (polynomialSystem 1) v = reducedWord v 0 0 - realP 0 0 := by
  simp [polynomialSystem,evalFin,finEnv,exprSub,exprScale,reducedWord,
    symmetricMatrix,realB,realP,Matrix.mul_apply,Fin.sum_univ_two,Matrix.trace,
    Matrix.vecMul,dotProduct,Matrix.smul_apply,smul_eq_mul]
  ring

theorem polynomial_eval_two (v : Fin 3 → ℝ) :
    evalFin (polynomialSystem 2) v = reducedWord v 0 1 - realP 0 1 := by
  simp [polynomialSystem,evalFin,finEnv,exprSub,exprScale,reducedWord,
    symmetricMatrix,realB,realP,Matrix.mul_apply,Fin.sum_univ_two,Matrix.trace,
    Matrix.vecMul,dotProduct,Matrix.smul_apply,smul_eq_mul]
  ring

/-- All three genuine Expr components are retained, including the determinant. -/
theorem polynomial_reduced_equivalence (v : Fin 3 → ℝ) :
    SystemZero polynomialSystem v ↔
      (symmetricMatrix v).det = 3 ∧
      reducedWord v 0 0 = realP 0 0 ∧ reducedWord v 0 1 = realP 0 1 := by
  constructor
  · intro h
    exact ⟨sub_eq_zero.mp ((polynomial_eval_zero v).symm.trans (h 0)),
      sub_eq_zero.mp ((polynomial_eval_one v).symm.trans (h 1)),
      sub_eq_zero.mp ((polynomial_eval_two v).symm.trans (h 2))⟩
  · rintro ⟨hd,h00,h01⟩ i
    fin_cases i
    · change evalFin (polynomialSystem 0) v = 0
      rw [polynomial_eval_zero,hd,sub_self]
    · change evalFin (polynomialSystem 1) v = 0
      rw [polynomial_eval_one,h00,sub_self]
    · change evalFin (polynomialSystem 2) v = 0
      rw [polynomial_eval_two,h01,sub_self]

end NLA.MF16
