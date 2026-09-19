import NLA.PF03.PositiveSlice

/-!
A strictly positive functional on every listed generator proves that a finite
real conical combination has zero functional value only when it is zero.
This handles zero coefficients and empty generator lists, and supplies the
literal no-line property needed by the frozen C14/C18 contracts.
Original mathematics: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance. Author: /root.
-/
set_option autoImplicit false
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.PF03

theorem cone_zero_mem {d s : ℕ} (V : QMat d s) : (0 : Fin d → ℝ) ∈ Cone V := by
  exact ⟨0, fun _ => le_rfl, (Matrix.mulVec_zero _).symm⟩

theorem positive_functional_on_cone {d s : ℕ} (V : QMat d s) (ell : Fin d → ℝ)
    (hpos : ∀ j : Fin s, 0 < ∑ r : Fin d, ell r * (V r j : ℝ))
    (x : Fin d → ℝ) (hx : x ∈ Cone V) :
    0 ≤ ell ⬝ᵥ x ∧ (ell ⬝ᵥ x = 0 → x = 0) := by
  obtain ⟨lam, hlam, rfl⟩ := hx
  have hsum : ell ⬝ᵥ (castMatrix V).mulVec lam =
      ∑ j : Fin s, (∑ r : Fin d, ell r * (V r j : ℝ)) * lam j := by
    rw [Matrix.dotProduct_mulVec]
    rfl
  have hnonneg (j : Fin s) :
      0 ≤ (∑ r : Fin d, ell r * (V r j : ℝ)) * lam j :=
    mul_nonneg (hpos j).le (hlam j)
  constructor
  · rw [hsum]
    exact Finset.sum_nonneg (fun j _ => hnonneg j)
  · intro hz
    have hzero : lam = 0 := by
      funext j
      have hj := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin s))) => hnonneg j)).mp
          (hsum ▸ hz) j (Finset.mem_univ j)
      exact (mul_eq_zero.mp hj).resolve_left (hpos j).ne'
    rw [hzero, Matrix.mulVec_zero]

theorem positive_functional_noLine {d s : ℕ} (V : QMat d s) (ell : Fin d → ℝ)
    (hpos : ∀ j : Fin s, 0 < ∑ r : Fin d, ell r * (V r j : ℝ)) :
    NoLine (Cone V) := by
  intro x hx hnx
  have hp := positive_functional_on_cone V ell hpos x hx
  have hn := (positive_functional_on_cone V ell hpos (-x) hnx).1
  rw [dotProduct_neg] at hn
  exact hp.2 (le_antisymm (by linarith only [hn]) hp.1)

theorem K_slice_generator_positive (j : Fin 21) :
    0 < ∑ r : Fin 7, (positiveSlice r : ℝ) * (generatorMatrix r j : ℝ) := by
  unfold generatorMatrix
  exact_mod_cast positive_slice_certificate.2
    ((finProdFinEquiv : Fin 7 × Fin 3 ≃ Fin 21).symm j).1
    ((finProdFinEquiv : Fin 7 × Fin 3 ≃ Fin 21).symm j).2

theorem K_noLine : NoLine K :=
  positive_functional_noLine generatorMatrix (castVector positiveSlice)
    K_slice_generator_positive

theorem K_inter_neg_eq_zero : K ∩ {x : Fin 7 → ℝ | -x ∈ K} = {0} := by
  ext x
  constructor
  · intro hx
    exact K_noLine x hx.1 hx.2
  · intro hx
    have hx0 : x = 0 := hx
    subst x
    have hz : (0 : Fin 7 → ℝ) ∈ K := cone_zero_mem generatorMatrix
    exact ⟨hz, by simpa using hz⟩

#print axioms positive_functional_on_cone
#assert_trust kernel positive_functional_on_cone
#print axioms K_noLine
#assert_trust kernel K_noLine
#print axioms K_inter_neg_eq_zero
#assert_trust kernel K_inter_neg_eq_zero
end NLA.PF03
