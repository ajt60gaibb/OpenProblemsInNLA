import NLA.Proofs.TR04.TTStrictFrames

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04.TensorFormat.TTStrict
open NLA.Computation.SVDMachine

theorem rank_denseFirst_le_first {m n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    {Y : Tensor (m :: n :: ns)} (hY : RankFeasible (m :: n :: ns) r Y) :
    Matrix.rank (denseFirst Y) ≤ r 0 := by
  rw [rank_denseFirst, ← rank_unfold_one]
  exact hY 1 (by decide) (by simp)

theorem family_first_error {m n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    (A : Tensor (m :: n :: ns)) (F : FirstFrames m (r 0))
    (e : ℝ) (hfirst : ∀ j, SVD.matrixEnergy
      (denseFirst A - F.frame j * ((F.frame j).transpose * denseFirst A)) = e) (j : Fin F.count) :
    error (m :: n :: ns) A (lift (F.frame j) (contract (F.frame j) A)) = e := by
  rw [error_denseFirst]
  exact hfirst j

theorem family_projected_energy {m n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    (A Y : Tensor (m :: n :: ns)) (F : FirstFrames m (r 0)) (j : Fin F.count) :
    energy (m :: n :: ns) (lift (F.frame j) (contract (F.frame j) (A - Y))) =
      SVD.matrixEnergy (F.frame j * ((F.frame j).transpose * (denseFirst A - denseFirst Y))) := by
  rw [← energy_denseFirst]
  rfl

theorem family_completion_feasible {m n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    (A : Tensor (m :: n :: ns)) (F : FirstFrames m (r 0))
    (Z : Fin F.count → Tensor ((F.width * n) :: ns))
    (hZ : ∀ j, Completion ((F.width * n) :: ns) (fun i => r (i + 1))
      (merge F.width n ns (contract (F.frame j) A)) (Z j)) (j : Fin F.count) :
    RankFeasible (m :: n :: ns) r (completionOutput (F.frame j) (Z j)) :=
  projected_completion_feasible (F.frame j) F.width_le A (hZ j)

theorem family_completion_bound {m n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    {A : Tensor (m :: n :: ns)}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m (suffixSize (n :: ns))) → ℝ}
    {V : Matrix (Fin (suffixSize (n :: ns))) (Fin (suffixSize (n :: ns))) ℝ}
    (h : ValidSVD (denseFirst A) U sigma V) (F : FirstFrames m (r 0))
    (hfirst : ∀ j, SVD.matrixEnergy
      (denseFirst A - F.frame j * ((F.frame j).transpose * denseFirst A)) = SVD.tailEnergy sigma (r 0))
    (Z : Fin F.count → Tensor ((F.width * n) :: ns))
    (hZ : ∀ j, Completion ((F.width * n) :: ns) (fun i => r (i + 1))
      (merge F.width n ns (contract (F.frame j) A)) (Z j))
    (Y : Tensor (m :: n :: ns)) (hY : RankFeasible (m :: n :: ns) r Y) (j : Fin F.count) :
    error (m :: n :: ns) A (completionOutput (F.frame j) (Z j)) ≤
      ((ns.length : ℝ) + 1) * error (m :: n :: ns) A Y := by
  have hb := completionOutput_bound (F.orthonormal j) A Y hY (hZ j)
  rw [family_first_error A F _ hfirst j] at hb
  have he := SVD.validSVD_eckartYoung h (r 0) (denseFirst Y) (rank_denseFirst_le_first hY)
  rw [← error_denseFirst] at he
  have hp := energy_projection_le (F.orthonormal j) (A - Y)
  have hc := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg ns.length : (0 : ℝ) ≤ ns.length)
  change (ns.length : ℝ) * energy (m :: n :: ns) (lift (F.frame j) (contract (F.frame j) (A - Y))) ≤
    (ns.length : ℝ) * error (m :: n :: ns) A Y at hc
  nlinarith

theorem family_min_strict {m n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    (hlen : 1 ≤ ns.length) {A : Tensor (m :: n :: ns)}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m (suffixSize (n :: ns))) → ℝ}
    {V : Matrix (Fin (suffixSize (n :: ns))) (Fin (suffixSize (n :: ns))) ℝ}
    (h : ValidSVD (denseFirst A) U sigma V) (F : FirstFrames m (r 0))
    (hfirst : ∀ j, SVD.matrixEnergy
      (denseFirst A - F.frame j * ((F.frame j).transpose * denseFirst A)) = SVD.tailEnergy sigma (r 0))
    (hgate : ∀ Y : Matrix (Fin m) (Fin (suffixSize (n :: ns))) ℝ, Matrix.rank Y ≤ r 0 →
      SVD.matrixEnergy (denseFirst A - Y) = SVD.tailEnergy sigma (r 0) →
      0 < SVD.matrixEnergy (denseFirst A - Y) →
      ∃ j, SVD.matrixEnergy (F.frame j * ((F.frame j).transpose * (denseFirst A - Y))) <
        SVD.matrixEnergy (denseFirst A - Y))
    (Z : Fin F.count → Tensor ((F.width * n) :: ns))
    (hZ : ∀ j, Completion ((F.width * n) :: ns) (fun i => r (i + 1))
      (merge F.width n ns (contract (F.frame j) A)) (Z j))
    (imin : Fin F.count)
    (hmin : IsMinimum A (fun j => completionOutput (F.frame j) (Z j)) imin)
    (Y : Tensor (m :: n :: ns)) (hY : RankFeasible (m :: n :: ns) r Y)
    (hpos : 0 < error (m :: n :: ns) A Y) :
    error (m :: n :: ns) A (completionOutput (F.frame imin) (Z imin)) <
      ((ns.length : ℝ) + 1) * error (m :: n :: ns) A Y := by
  have he := SVD.validSVD_eckartYoung h (r 0) (denseFirst Y) (rank_denseFirst_le_first hY)
  rw [← error_denseFirst] at he
  rcases lt_or_eq_of_le he with hlt | heq
  · apply completionOutput_strict_of_first_lt (F.orthonormal imin) A Y hY (hZ imin)
    rw [family_first_error A F _ hfirst imin]
    exact hlt
  · obtain ⟨j, hj⟩ := hgate (denseFirst Y) (rank_denseFirst_le_first hY)
      (by rw [← error_denseFirst]; exact heq.symm) (by rwa [← error_denseFirst])
    have hb := completionOutput_bound (F.orthonormal j) A Y hY (hZ j)
    rw [family_first_error A F _ hfirst j, heq] at hb
    rw [← family_projected_energy A Y F j, ← error_denseFirst] at hj
    have hn : (0 : ℝ) < ns.length := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hlen)
    have hstrict : error (m :: n :: ns) A (completionOutput (F.frame j) (Z j)) <
        ((ns.length : ℝ) + 1) * error (m :: n :: ns) A Y := by nlinarith
    exact (hmin j).trans_lt hstrict

theorem family_completion_exact_of_error_zero {m n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    {A : Tensor (m :: n :: ns)}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m (suffixSize (n :: ns))) → ℝ}
    {V : Matrix (Fin (suffixSize (n :: ns))) (Fin (suffixSize (n :: ns))) ℝ}
    (h : ValidSVD (denseFirst A) U sigma V) (F : FirstFrames m (r 0))
    (hfirst : ∀ j, SVD.matrixEnergy
      (denseFirst A - F.frame j * ((F.frame j).transpose * denseFirst A)) = SVD.tailEnergy sigma (r 0))
    (Z : Fin F.count → Tensor ((F.width * n) :: ns))
    (hZ : ∀ j, Completion ((F.width * n) :: ns) (fun i => r (i + 1))
      (merge F.width n ns (contract (F.frame j) A)) (Z j))
    (Y : Tensor (m :: n :: ns)) (hY : RankFeasible (m :: n :: ns) r Y)
    (hzero : error (m :: n :: ns) A Y = 0) (j : Fin F.count) :
    completionOutput (F.frame j) (Z j) = A := by
  have hb := family_completion_bound h F hfirst Z hZ Y hY j
  rw [hzero, mul_zero] at hb
  apply (error_eq_zero_iff _ _ _).mp
  exact le_antisymm hb (error_nonneg _ _ _)

#assert_trust kernel family_completion_bound
#assert_trust kernel family_min_strict
#assert_trust kernel family_completion_exact_of_error_zero
#print axioms family_min_strict
end NLA.Proofs.TR04.TensorFormat.TTStrict
