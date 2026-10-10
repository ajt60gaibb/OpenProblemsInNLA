import NLA.Proofs.SP14.EndpointFiniteMatrixSchur
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
Square summability of each actual negative Fourier row. This is the absolute
series gate for the infinite endpoint operator, not yet that operator itself.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- Each finite actual Fourier row has square energy at most `C_r²`. -/
theorem endpointFiniteFourierRow_square_sum_le (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (t N : ℕ) :
    (∑ k : Fin N, ‖endpointFiniteFourierEntry r t k.val‖ ^ 2) ≤
      endpointSchurConstant r ^ 2 := by
  classical
  let B : Fin N → ℂ := fun k => endpointFiniteFourierEntry r t k.val
  let S : ℝ := ∑ k : Fin N, ‖B k‖ ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun k hk => sq_nonneg _)
  have hcomplex : (∑ k : Fin N, B k * star (B k)) = (S : ℂ) := by
    calc
      _ = ∑ k : Fin N, ((‖B k‖ ^ 2 : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      _ = (S : ℂ) := by simp [S]
  have hrow : ‖∑ k : Fin N, B k * star (B k)‖ ^ 2 = S ^ 2 := by
    rw [hcomplex, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
  let it : Fin (t + 1) := ⟨t, by omega⟩
  have hselected :
      ‖∑ k : Fin N, endpointFiniteFourierEntry r it.val k.val *
          star (B k)‖ ^ 2 ≤
        ∑ i : Fin (t + 1),
          ‖∑ k : Fin N, endpointFiniteFourierEntry r i.val k.val *
            star (B k)‖ ^ 2 := by
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin (t + 1))))
      (f := fun i : Fin (t + 1) =>
        ‖∑ k : Fin N, endpointFiniteFourierEntry r i.val k.val * star (B k)‖ ^ 2)
      (fun i hi => sq_nonneg _) (Finset.mem_univ it)
  have hmatrix := endpointFiniteFourierMatrix_bound r hr hr1 (t + 1) N
    (fun k : Fin N => star (B k))
  have hSq : S ^ 2 ≤ endpointSchurConstant r ^ 2 * S := by
    calc
      S ^ 2 = ‖∑ k : Fin N, endpointFiniteFourierEntry r it.val k.val *
          star (B k)‖ ^ 2 := by simpa [it, B] using hrow.symm
      _ ≤ ∑ i : Fin (t + 1),
          ‖∑ k : Fin N, endpointFiniteFourierEntry r i.val k.val *
            star (B k)‖ ^ 2 := hselected
      _ ≤ endpointSchurConstant r ^ 2 *
          (∑ k : Fin N, ‖star (B k)‖ ^ 2) := hmatrix
      _ = endpointSchurConstant r ^ 2 * S := by simp [S]
  have hSC : S ≤ endpointSchurConstant r ^ 2 := by
    by_contra hn
    have hlt : endpointSchurConstant r ^ 2 < S := lt_of_not_ge hn
    have hSpos : 0 < S := lt_of_le_of_lt (sq_nonneg _) hlt
    nlinarith [mul_pos hSpos (sub_pos.mpr hlt)]
  exact hSC

#assert_trust kernel endpointFiniteFourierRow_square_sum_le
#print axioms endpointFiniteFourierRow_square_sum_le

end NLA.Proofs.SP14
