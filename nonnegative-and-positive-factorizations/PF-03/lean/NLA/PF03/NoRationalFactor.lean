import NLA.PF03.ConeRationalZeros
import NLA.PF03.ConePointed
import NLA.PF03.PointedHalfspaces
import NLA.PF03.GramTransport
import NLA.PF03.TraceObstruction
import NLA.PF03.PaddedFactor

/-! C21: all arbitrary finite rational factor widths are excluded by the
zero-trace quadratic obstruction. No bound on a factor width is introduced.
Sidney Holden: original mathematics. George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology: formalization;
Codex assistance. Author: /root. -/
set_option autoImplicit false
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.PF03

lemma castMatrix_one (d : ℕ) : castMatrix (1 : QMat d d) = (1 : RMat d d) := by
  ext i j
  by_cases hij : i = j <;> simp [castMatrix, Matrix.one_apply, hij]

theorem no_rational_factor {N : ℕ} (R : QMat N 7) (hR : HSet R = K)
    (hker : ∀ x : Fin 7 → ℝ, (castMatrix R).mulVec x = 0 → x = 0) :
    ∀ m : ℕ, 1 ≤ m → ∀ C : QMat N m, (∀ i j, 0 ≤ C i j) →
      C * Cᵀ ≠ R * Rᵀ := by
  intro m _hm C hnonneg hgram
  have hpoint : NoLine (HSet R) := by rw [hR]; exact K_noLine
  obtain ⟨L, hLR⟩ := (pointed_halfspaces_injective R hpoint).2.2
  let X : QMat 7 m := L * C
  have htrans := gram_factor_transport R L C hLR hgram
  have hX : X * Xᵀ = 1 := htrans.2
  have hreal : castMatrix X * (castMatrix X)ᵀ = 1 := by
    rw [← castMatrix_transpose, ← castMatrix_mul, hX, castMatrix_one]
  have hcol (j : Fin m) : castVector (fun r => X r j) ∈ K := by
    rw [← hR]
    intro i
    have heq : ((castMatrix R).mulVec (castVector (fun r => X r j))) i = (C i j : ℝ) := by
      have h := congrArg (fun M : QMat N m => (M i j : ℝ)) htrans.1
      simpa [X, Matrix.mul_apply, castMatrix, castVector, Matrix.mulVec, dotProduct] using h
    rw [heq]
    exact_mod_cast hnonneg i j
  have hqpos (j : Fin m) :
      0 ≤ quad quadraticSeed (fun r => castMatrix X r j) :=
    (cone_quadratic_zeros _ (hcol j)).1
  have hsum : (∑ j : Fin m, quad quadraticSeed (fun r => castMatrix X r j)) = 0 :=
    (trace_obstruction (castMatrix X) hreal).trans seed_quadratic_form.2
  have hzero : X = 0 := by
    ext r j
    have hqj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hqpos j)).mp hsum
        j (Finset.mem_univ j)
    have hrat := cone_rational_zeros (fun r => X r j) (hcol j) hqj
    exact congrFun hrat r
  have hbad := congrArg (fun M : QMat 7 7 => M 0 0) hX
  norm_num [hzero] at hbad

#print axioms no_rational_factor
#assert_trust kernel no_rational_factor
end NLA.PF03
