import NLA.PF03.RationalProjection

/-!
Every finitely generated rational cone has a rational homogeneous halfspace
representation. The cone coefficients remain arbitrary nonnegative reals.
The proof includes zero ambient dimension and an empty generator family.

Original mathematics and seed: Sidney Holden, Center for Computational Biology,
Flatiron Institute, Simons Foundation. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, with Codex assistance. Proof author: /root/recover_lean_sources;
final proof reviewers must be different nonauthors.
-/

set_option autoImplicit false
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.PF03

/-- The retained coefficients of `x-Vλ`, `-x+Vλ`, and `λ`. -/
private def rcA (d s : ℕ) : QMat (d + d + s) d :=
  Fin.append
    (Fin.append (1 : QMat d d) (-(1 : QMat d d)))
    (0 : QMat s d)

/-- The eliminated coefficients of `x-Vλ`, `-x+Vλ`, and `λ`. -/
private def rcB {d s : ℕ} (V : QMat d s) : QMat (d + d + s) s :=
  Fin.append (Fin.append (-V) V) (1 : QMat s s)

private theorem rc_first_value {d s : ℕ} (V : QMat d s)
    (x : Fin d → ℝ) (lam : Fin s → ℝ) (i : Fin d) :
    ((castMatrix (rcA d s)).mulVec x) (Fin.castAdd s (Fin.castAdd d i)) +
        ((castMatrix (rcB V)).mulVec lam) (Fin.castAdd s (Fin.castAdd d i)) =
      x i - ((castMatrix V).mulVec lam) i := by
  have hi : (i : ℕ) < d + d := lt_of_lt_of_le i.isLt (Nat.le_add_right d d)
  simp [rcA, rcB, castMatrix, Matrix.map, Fin.append, Fin.addCases, Matrix.mulVec, dotProduct,
    Matrix.one_apply, sub_eq_add_neg, hi, apply_ite]

private theorem rc_second_value {d s : ℕ} (V : QMat d s)
    (x : Fin d → ℝ) (lam : Fin s → ℝ) (i : Fin d) :
    ((castMatrix (rcA d s)).mulVec x) (Fin.castAdd s (Fin.natAdd d i)) +
        ((castMatrix (rcB V)).mulVec lam) (Fin.castAdd s (Fin.natAdd d i)) =
      -x i + ((castMatrix V).mulVec lam) i := by
  simp [rcA, rcB, castMatrix, Matrix.map, Fin.append, Fin.addCases, Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite]

private theorem rc_last_value {d s : ℕ} (V : QMat d s)
    (x : Fin d → ℝ) (lam : Fin s → ℝ) (j : Fin s) :
    ((castMatrix (rcA d s)).mulVec x) (Fin.natAdd (d + d) j) +
        ((castMatrix (rcB V)).mulVec lam) (Fin.natAdd (d + d) j) =
      lam j := by
  simp [rcA, rcB, castMatrix, Matrix.map, Fin.append, Fin.addCases, Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite]

private theorem rc_encoding {d s : ℕ} (V : QMat d s)
    (x : Fin d → ℝ) (lam : Fin s → ℝ) :
    MixedHolds (rcA d s) (rcB V) x lam ↔
      (∀ j, 0 ≤ lam j) ∧ x = (castMatrix V).mulVec lam := by
  constructor
  · intro h
    constructor
    · intro j
      have hj := h (Fin.natAdd (d + d) j)
      rwa [rc_last_value] at hj
    · ext i
      have h₁ := h (Fin.castAdd s (Fin.castAdd d i))
      have h₂ := h (Fin.castAdd s (Fin.natAdd d i))
      rw [rc_first_value] at h₁
      rw [rc_second_value] at h₂
      linarith only [h₁, h₂]
  · rintro ⟨hlam, hx⟩
    intro row
    refine Fin.addCases ?_ ?_ row
    · intro k
      refine Fin.addCases ?_ ?_ k
      · intro i
        rw [rc_first_value, hx]
        simp
      · intro i
        rw [rc_second_value, hx]
        simp
    · intro j
      rw [rc_last_value]
      exact hlam j

/-- C17: an exact rational halfspace representation of the whole real cone. -/
theorem rational_cone_halfspaces {d s : ℕ} (V : QMat d s) :
    ∃ N : ℕ, ∃ R : QMat N d, ∀ x : Fin d → ℝ,
      x ∈ Cone V ↔ x ∈ HSet R := by
  obtain ⟨N, R, hR⟩ := rational_projection (rcA d s) (rcB V)
  refine ⟨N, R, ?_⟩
  intro x
  rw [hR x]
  constructor
  · rintro ⟨lam, hlam, hx⟩
    exact ⟨lam, (rc_encoding V x lam).mpr ⟨hlam, hx⟩⟩
  · rintro ⟨lam, h⟩
    exact ⟨lam, (rc_encoding V x lam).mp h⟩

#print axioms rational_cone_halfspaces
#assert_trust kernel rational_cone_halfspaces

end NLA.PF03
