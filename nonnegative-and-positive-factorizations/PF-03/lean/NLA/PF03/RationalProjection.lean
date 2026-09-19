import NLA.PF03.FourierMotzkin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
Successive exact rational Fourier–Motzkin elimination. Every quantified
eliminated coordinate is real, and all finite dimensions may be zero.

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

private def rpLeft {d m : ℕ} (rows : List (Fin (d + m) → ℚ)) :
    QMat rows.length d :=
  fun i j => rows.get i (Fin.castAdd m j)

private def rpRight {d m : ℕ} (rows : List (Fin (d + m) → ℚ)) :
    QMat rows.length m :=
  fun i j => rows.get i (Fin.natAdd d j)

private theorem rp_split_row {d m : ℕ} (r : Fin (d + m) → ℚ)
    (x : Fin d → ℝ) (z : Fin m → ℝ) :
    (∑ j : Fin (d + m), (r j : ℝ) * Fin.append x z j) =
      (∑ j : Fin d, (r (Fin.castAdd m j) : ℝ) * x j) +
        ∑ j : Fin m, (r (Fin.natAdd d j) : ℝ) * z j := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- Indexing all list entries neither loses duplicate rows nor creates a premise. -/
private theorem rp_listHolds_iff {d m : ℕ}
    (rows : List (Fin (d + m) → ℚ)) (x : Fin d → ℝ) (z : Fin m → ℝ) :
    (∀ r ∈ rows, rowHolds r (Fin.append x z)) ↔
      MixedHolds (rpLeft rows) (rpRight rows) x z := by
  constructor
  · intro h i
    have hi := h (rows.get i) (List.get_mem rows i)
    unfold rowHolds at hi
    rw [rp_split_row] at hi
    exact hi
  · intro h r hr
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hr
    unfold rowHolds
    rw [rp_split_row]
    exact h i

private def rpJoined {N d m : ℕ} (A : QMat N d) (B : QMat N (m + 1)) :
    QMat N (d + m) :=
  fun i => Fin.append (A i) (fun j : Fin m => B i j.succ)

private theorem rp_split_evaluation {N d m : ℕ}
    (A : QMat N d) (B : QMat N (m + 1))
    (x : Fin d → ℝ) (z : Fin m → ℝ) (t : ℝ) (i : Fin N) :
    (B i 0 : ℝ) * t +
        ((castMatrix (rpJoined A B)).mulVec (Fin.append x z)) i =
      ((castMatrix A).mulVec x) i +
        ((castMatrix B).mulVec (Fin.cons t z)) i := by
  change (B i 0 : ℝ) * t +
      (∑ j : Fin (d + m), (rpJoined A B i j : ℝ) * Fin.append x z j) =
    (∑ j : Fin d, (A i j : ℝ) * x j) +
      ∑ j : Fin (m + 1), (B i j : ℝ) * (Fin.cons t z : Fin (m + 1) → ℝ) j
  rw [Fin.sum_univ_add, Fin.sum_univ_succ]
  simp only [rpJoined, Fin.append_left, Fin.append_right, Fin.cons_zero, Fin.cons_succ]
  ring

/-- C16: a rational halfspace representation of every real coordinate projection. -/
theorem rational_projection {N d m : ℕ} (A : QMat N d) (B : QMat N m) :
    ∃ k : ℕ, ∃ R : QMat k d, ∀ x : Fin d → ℝ,
      x ∈ HSet R ↔ ∃ y : Fin m → ℝ, MixedHolds A B x y := by
  induction m generalizing N with
  | zero =>
    refine ⟨N, A, ?_⟩
    intro x
    constructor
    · intro hx
      refine ⟨Fin.elim0, ?_⟩
      intro i
      simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_zero, add_zero] using hx i
    · rintro ⟨y, hy⟩
      intro i
      simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_zero, add_zero] using hy i
  | succ m ih =>
    let C : QMat N (d + m) := rpJoined A B
    let a : Fin N → ℚ := fun i => B i 0
    let rows : List (Fin (d + m) → ℚ) := eliminateOne C a
    obtain ⟨k, R, hR⟩ := ih (rpLeft rows) (rpRight rows)
    refine ⟨k, R, ?_⟩
    intro x
    rw [hR x]
    constructor
    · rintro ⟨z, hz⟩
      have hr := (rp_listHolds_iff rows x z).mpr hz
      obtain ⟨t, ht⟩ :=
        (one_variable_projection C a (Fin.append x z)).mp hr
      refine ⟨Fin.cons t z, ?_⟩
      intro i
      have hi := ht i
      change 0 ≤ (B i 0 : ℝ) * t +
        ((castMatrix (rpJoined A B)).mulVec (Fin.append x z)) i at hi
      rw [rp_split_evaluation] at hi
      exact hi
    · rintro ⟨y, hy⟩
      let z : Fin m → ℝ := fun j => y j.succ
      refine ⟨z, (rp_listHolds_iff rows x z).mp ?_⟩
      apply (one_variable_projection C a (Fin.append x z)).mpr
      refine ⟨y 0, ?_⟩
      intro i
      change 0 ≤ (B i 0 : ℝ) * y 0 +
        ((castMatrix (rpJoined A B)).mulVec (Fin.append x z)) i
      rw [rp_split_evaluation]
      have heq : Fin.cons (y 0) z = y := Fin.cons_self_tail y
      rw [heq]
      exact hy i

#print axioms rational_projection
#assert_trust kernel rational_projection

end NLA.PF03
