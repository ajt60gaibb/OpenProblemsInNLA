import NLA.Proofs.SP11.Final
import NLA.Statements.SP12
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Actual real specialization and independence of LSS inputs

Specializing the determinant coefficients commutes with the actual recursive
construction. A nonzero output then forces its earlier-nonneighbor inputs to
be linearly independent, by alternation. No general-position or probability
hypothesis is supplied.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open NLA.Proofs.SP11

namespace NLA.Proofs.SP12

/-- Evaluation of a concrete alternating tensor is its real coefficient tensor. -/
theorem eval_weightedMinorForm {σ : Type*} {d r : ℕ} (x : σ → ℝ)
    (c : CoordinateSubset d r → MvPolynomial σ ℝ)
    (w : Fin r → CoordinateVector (MvPolynomial σ ℝ) d) :
    MvPolynomial.eval x (weightedMinorForm c w) =
      weightedMinorForm (fun s => MvPolynomial.eval x (c s))
        (fun i k => MvPolynomial.eval x (w i k)) := by
  classical
  simp only [weightedMinorForm_apply, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  exact (MvPolynomial.eval x).map_det _

/-- The actual coordinate contraction commutes with evaluation of all variables. -/
theorem eval_polynomialContraction {σ : Type*} {d k : ℕ} (x : σ → ℝ)
    (name : CoordinateSubset d (k + 1) → σ)
    (w : Fin k → CoordinateVector (MvPolynomial σ ℝ) d) :
    (fun q => MvPolynomial.eval x (alternatingContraction (polynomialAlternatingForm name) w q)) =
      alternatingContraction (weightedMinorForm (fun s => x (name s)))
        (fun i q => MvPolynomial.eval x (w i q)) := by
  funext q
  change MvPolynomial.eval x (weightedMinorForm (fun s => MvPolynomial.X (name s))
      (Fin.cons (Pi.single q (1 : MvPolynomial σ ℝ) : CoordinateVector (MvPolynomial σ ℝ) d) w)) = _
  rw [eval_weightedMinorForm]
  simp only [MvPolynomial.eval_X]
  have ht : (fun (i : Fin (k + 1)) (a : Fin d) => MvPolynomial.eval x
      ((Fin.cons (Pi.single q 1) w : Fin (k + 1) → CoordinateVector (MvPolynomial σ ℝ) d) i a)) =
      (Fin.cons (Pi.single q 1) (fun i a => MvPolynomial.eval x (w i a)) :
        Fin (k + 1) → CoordinateVector ℝ d) := by
    funext i
    refine Fin.cases ?_ (fun s => ?_) i
    · funext a
      by_cases h : a = q <;> simp [h]
    · rfl
  rw [ht]
  rfl

/-- Real tensors use exactly the assignment to each original shared coefficient. -/
noncomputable def realVertexForms {n d : ℕ} (G : SimpleGraph (Fin n))
    (x : LSSVariable G d → ℝ) : VertexForms G ℝ d :=
  fun j => weightedMinorForm (fun s => x ⟨j, s⟩)

/-- The actual polynomial vectors specialize to the actual real LSS recursion. -/
theorem eval_polynomialLSS {n d : ℕ} (G : SimpleGraph (Fin n))
    (x : LSSVariable G d → ℝ) (j : Fin n) :
    (fun q => MvPolynomial.eval x (polynomialLSS G d j q)) =
      uniformLSS G (realVertexForms G x) j := by
  induction j using (measure (fun j : Fin n => j.val)).wf.induction with
  | h j ih =>
    change (fun q => MvPolynomial.eval x (uniformLSS G (universalVertexForms G) j q)) = _
    rw [uniformLSS_eq G (universalVertexForms G) j,
      uniformLSS_eq G (realVertexForms G x) j]
    dsimp only [universalVertexForms, realVertexForms]
    rw [eval_polynomialContraction]
    congr 1
    funext s
    exact ih (priorVertex G j s) (priorVertex_lt G j s)

/-- A dependent input family annihilates every coordinate of its contraction. -/
theorem alternatingContraction_eq_zero_of_dependent {d k : ℕ}
    (a : (CoordinateVector ℝ d) [⋀^Fin (k + 1)]→ₗ[ℝ] ℝ)
    (w : Fin k → CoordinateVector ℝ d) (hw : ¬ LinearIndependent ℝ w) :
    alternatingContraction a w = 0 := by
  funext q
  change a (Fin.cons (Pi.single q 1) w) = 0
  apply a.map_linearDependent
  intro hi
  apply hw
  simpa only [Function.comp_def, Fin.cons_succ] using hi.comp Fin.succ (Fin.succ_injective _)

/-- Every nonzero actual output certifies the independence of all its inputs. -/
theorem uniformLSS_prior_linearIndependent {n d : ℕ} (G : SimpleGraph (Fin n))
    (a : VertexForms G ℝ d) (j : Fin n) (hj : uniformLSS G a j ≠ 0) :
    LinearIndependent ℝ (fun s => uniformLSS G a (priorVertex G j s)) := by
  by_contra hdep
  apply hj
  rw [uniformLSS_eq]
  exact alternatingContraction_eq_zero_of_dependent _ _ hdep

/-- The already-proved nonzero diagonal specialization supplies local input
independence in the same actual shared polynomial representation. -/
theorem evaluated_polynomialLSS_prior_linearIndependent {n d : ℕ}
    (G : SimpleGraph (Fin n)) (x : LSSVariable G d → ℝ) (j : Fin n)
    (hj : (fun q => MvPolynomial.eval x (polynomialLSS G d j q)) ≠ 0) :
    LinearIndependent ℝ (fun s q => MvPolynomial.eval x (polynomialLSS G d (priorVertex G j s) q)) := by
  have h := uniformLSS_prior_linearIndependent G (realVertexForms G x) j
    (by rwa [← eval_polynomialLSS])
  simpa only [← eval_polynomialLSS G x] using h

#assert_trust kernel eval_polynomialLSS
#assert_trust kernel uniformLSS_prior_linearIndependent
#assert_trust kernel evaluated_polynomialLSS_prior_linearIndependent
#print axioms evaluated_polynomialLSS_prior_linearIndependent

end NLA.Proofs.SP12
