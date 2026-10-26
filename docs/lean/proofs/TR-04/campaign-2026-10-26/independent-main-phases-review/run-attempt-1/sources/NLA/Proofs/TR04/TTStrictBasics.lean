import NLA.Proofs.TR04.TTCompletionProjected
import NLA.Proofs.TR04.TTCompletionOriginal
import NLA.Proofs.TR04.SVDFrameSpace

/-! Exact tensor/matrix and finite-minimum bridges for the strict TR-04
mathematical construction. These do not claim a RAM program or its cost. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04.TensorFormat.TTStrict

theorem error_eq_zero_iff (ns : List ℕ) (A X : Tensor ns) : error ns A X = 0 ↔ X = A := by
  constructor
  · intro h
    funext x
    have hc : (A x - X x)^2 ≤ error ns A X :=
      Finset.single_le_sum (fun i _ => sq_nonneg (A i - X i)) (Finset.mem_univ x)
    rw [h] at hc
    nlinarith [sq_nonneg (A x - X x)]
  · rintro rfl
    simp [error, energy]

theorem error_denseFirst {m : ℕ} {ns : List ℕ} (A X : Tensor (m :: ns)) :
    error (m :: ns) A X = SVD.matrixEnergy (denseFirst A - denseFirst X) := by
  rw [← denseFirst_sub, energy_denseFirst]
  rfl

theorem energy_projection_le {m k : ℕ} {ns : List ℕ}
    {Q : Matrix (Fin m) (Fin k) ℝ} (hQ : SVD.OrthonormalColumns Q)
    (A : Tensor (m :: ns)) :
    energy (m :: ns) (lift Q (contract Q A)) ≤ energy (m :: ns) A := by
  rw [energy_lift hQ]
  exact energy_contract_le hQ A

theorem energy_projection_eq {m k : ℕ} {ns : List ℕ}
    (Q : Matrix (Fin m) (Fin k) ℝ) (S : Submodule ℝ (SVD.Space m))
    (hQ : ∀ B : Matrix (Fin m) (Fin (suffixSize ns)) ℝ,
      Q * (Q.transpose * B) = SVD.projectMatrix S B) (A : Tensor (m :: ns)) :
    energy (m :: ns) (lift Q (contract Q A)) =
      SVD.matrixEnergy (SVD.projectMatrix S (denseFirst A)) := by
  rw [← energy_denseFirst]
  change SVD.matrixEnergy (Q * (Q.transpose * denseFirst A)) = _
  rw [hQ]

theorem error_projection_eq {m k : ℕ} {ns : List ℕ}
    (Q : Matrix (Fin m) (Fin k) ℝ) (S : Submodule ℝ (SVD.Space m))
    (hQ : ∀ B : Matrix (Fin m) (Fin (suffixSize ns)) ℝ,
      Q * (Q.transpose * B) = SVD.projectMatrix S B) (A : Tensor (m :: ns)) :
    error (m :: ns) A (lift Q (contract Q A)) =
      SVD.matrixEnergy (denseFirst A - SVD.projectMatrix S (denseFirst A)) := by
  rw [error_denseFirst]
  change SVD.matrixEnergy (denseFirst A - Q * (Q.transpose * denseFirst A)) = _
  rw [hQ]

def completionOutput {m k n : ℕ} {ns : List ℕ}
    (Q : Matrix (Fin m) (Fin k) ℝ) (Z : Tensor ((k * n) :: ns)) : Tensor (m :: n :: ns) :=
  lift Q ((merge k n ns).symm Z)

def IsMinimum {ι : Type*} {ns : List ℕ} (A : Tensor ns) (X : ι → Tensor ns) (i : ι) : Prop :=
  ∀ j, error ns A (X i) ≤ error ns A (X j)

theorem exists_minimum {ι : Type*} [Fintype ι] [Nonempty ι] {ns : List ℕ}
    (A : Tensor ns) (X : ι → Tensor ns) : ∃ i, IsMinimum A X i := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun j => error ns A (X j)) Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

theorem completionOutput_bound {m k n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    {Q : Matrix (Fin m) (Fin k) ℝ} (hQ : SVD.OrthonormalColumns Q)
    (A Y : Tensor (m :: n :: ns)) (hY : RankFeasible (m :: n :: ns) r Y)
    {Z : Tensor ((k * n) :: ns)}
    (hZ : Completion ((k * n) :: ns) (fun j => r (j + 1))
      (merge k n ns (contract Q A)) Z) :
    error (m :: n :: ns) A (completionOutput Q Z) ≤
      error (m :: n :: ns) A (lift Q (contract Q A)) +
        (ns.length : ℝ) * energy (m :: n :: ns) (lift Q (contract Q (A - Y))) :=
  projected_completion_bound hQ A Y hY hZ

theorem completionOutput_strict_of_first_lt {m k n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    {Q : Matrix (Fin m) (Fin k) ℝ} (hQ : SVD.OrthonormalColumns Q)
    (A Y : Tensor (m :: n :: ns)) (hY : RankFeasible (m :: n :: ns) r Y)
    {Z : Tensor ((k * n) :: ns)}
    (hZ : Completion ((k * n) :: ns) (fun j => r (j + 1))
      (merge k n ns (contract Q A)) Z)
    (hfirst : error (m :: n :: ns) A (lift Q (contract Q A)) < error (m :: n :: ns) A Y) :
    error (m :: n :: ns) A (completionOutput Q Z) <
      ((ns.length : ℝ) + 1) * error (m :: n :: ns) A Y := by
  have hb := completionOutput_bound hQ A Y hY hZ
  have hp := energy_projection_le hQ (A - Y)
  have hc := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg ns.length : (0 : ℝ) ≤ ns.length)
  change (ns.length : ℝ) * energy (m :: n :: ns) (lift Q (contract Q (A - Y))) ≤
    (ns.length : ℝ) * error (m :: n :: ns) A Y at hc
  nlinarith

#assert_trust kernel error_eq_zero_iff
#assert_trust kernel exists_minimum
#assert_trust kernel completionOutput_strict_of_first_lt
#print axioms completionOutput_strict_of_first_lt
end NLA.Proofs.TR04.TensorFormat.TTStrict
