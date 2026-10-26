import NLA.Proofs.TR04.SVDTotal
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Energy identities for every tuple satisfying the literal machine SVD
relation, independently of the spectral basis chosen by a legal response. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Matrix

namespace NLA.Proofs.TR04.SVD
open NLA.Computation.SVDMachine

def OrthonormalColumns {α β : Type*} [Fintype α] [DecidableEq β]
    (Q : Matrix α β ℝ) : Prop :=
  ∀ i j, (∑ a, Q a i * Q a j) = if i = j then 1 else 0

theorem transpose_mul_eq_one {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    {Q : Matrix α β ℝ} (hQ : OrthonormalColumns Q) : Q.transpose * Q = 1 := by
  ext i j
  exact hQ i j

theorem orthonormalColumns_submatrix {α β γ : Type*} [Fintype α]
    [DecidableEq β] [DecidableEq γ] {Q : Matrix α β ℝ}
    (hQ : OrthonormalColumns Q) (f : γ → β) (hf : Function.Injective f) :
    OrthonormalColumns (Q.submatrix id f) := by
  intro i j
  simpa only [Matrix.submatrix_apply, id_eq, hf.eq_iff] using hQ (f i) (f j)

theorem orthonormalColumns_inner {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    {Q : Matrix α β ℝ} (hQ : OrthonormalColumns Q) (c d : β → ℝ) :
    (Q *ᵥ c) ⬝ᵥ (Q *ᵥ d) = c ⬝ᵥ d := by
  calc
    (Q *ᵥ c) ⬝ᵥ (Q *ᵥ d) = c ⬝ᵥ (Q.transpose *ᵥ (Q *ᵥ d)) := by
      rw [Matrix.dotProduct_transpose_mulVec]
      exact dotProduct_comm _ _
    _ = c ⬝ᵥ ((Q.transpose * Q) *ᵥ d) := by rw [Matrix.mulVec_mulVec]
    _ = c ⬝ᵥ d := by rw [transpose_mul_eq_one hQ, Matrix.one_mulVec]

theorem orthonormalColumns_sum_sq {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] {Q : Matrix α β ℝ} (hQ : OrthonormalColumns Q) (c : β → ℝ) :
    (∑ a, (∑ k, Q a k * c k)^2) = ∑ k, (c k)^2 := by
  simpa only [Matrix.mulVec, dotProduct, ← pow_two] using orthonormalColumns_inner hQ c c

def matrixEnergy {α β : Type*} [Fintype α] [Fintype β] (M : Matrix α β ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j)^2

def synthesis {m l : ℕ}
    (U : Matrix (Fin m) (Fin m) ℝ) (c : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) : Matrix (Fin m) (Fin l) ℝ :=
  fun i j => ∑ k, U i (Fin.castLE (Nat.min_le_left m l) k) * c k *
    V j (Fin.castLE (Nat.min_le_right m l) k)

theorem validSVD_eq_synthesis {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V) :
    B = synthesis U sigma V := by
  ext i j
  exact h.2.2.2.2 i j

theorem synthesis_energy {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin l) (Fin l) ℝ}
    (hU : OrthonormalColumns U) (hV : OrthonormalColumns V)
    (c : Fin (min m l) → ℝ) :
    matrixEnergy (synthesis U c V) = ∑ k, (c k)^2 := by
  classical
  let L := U.submatrix id (Fin.castLE (Nat.min_le_left m l))
  let R := V.submatrix id (Fin.castLE (Nat.min_le_right m l))
  have hL : OrthonormalColumns L := orthonormalColumns_submatrix hU _
    (fun _ _ h => Fin.ext (congrArg (fun i : Fin m => i.val) h))
  have hR : OrthonormalColumns R := orthonormalColumns_submatrix hV _
    (fun _ _ h => Fin.ext (congrArg (fun i : Fin l => i.val) h))
  unfold matrixEnergy
  rw [Finset.sum_comm]
  calc
    ∑ j : Fin l, ∑ i : Fin m, (synthesis U c V i j)^2 =
        ∑ j : Fin l, ∑ k : Fin (min m l), (c k * R j k)^2 := by
      apply Finset.sum_congr rfl
      intro j _
      have h := orthonormalColumns_sum_sq hL (fun k => c k * R j k)
      simpa only [synthesis, L, R, Matrix.submatrix_apply, id_eq, mul_assoc] using h
    _ = ∑ k : Fin (min m l), ∑ j : Fin l, (c k)^2 * (R j k)^2 := by
      simp_rw [mul_pow]
      rw [Finset.sum_comm]
    _ = ∑ k : Fin (min m l), (c k)^2 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.mul_sum]
      have hk : ∑ j : Fin l, (R j k)^2 = 1 := by
        simpa only [← pow_two, ite_true] using hR k k
      rw [hk, mul_one]

theorem validSVD_energy {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V) :
    matrixEnergy B = ∑ k, (sigma k)^2 := by
  rw [validSVD_eq_synthesis h]
  exact synthesis_energy h.1 h.2.1 sigma

theorem synthesis_sub {m l : ℕ}
    (U : Matrix (Fin m) (Fin m) ℝ) (c d : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) :
    synthesis U c V - synthesis U d V = synthesis U (c - d) V := by
  ext i j
  simp only [Matrix.sub_apply, synthesis, Pi.sub_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib]

theorem validSVD_error_energy {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (c : Fin (min m l) → ℝ) :
    matrixEnergy (B - synthesis U c V) = ∑ k, (sigma k - c k)^2 := by
  rw [validSVD_eq_synthesis h, synthesis_sub]
  exact synthesis_energy h.1 h.2.1 _

def truncate {m l : ℕ} (U : Matrix (Fin m) (Fin m) ℝ)
    (sigma : Fin (min m l) → ℝ) (V : Matrix (Fin l) (Fin l) ℝ) (r : ℕ) :=
  synthesis U (fun k => if k.val < r then sigma k else 0) V

def tailEnergy {p : ℕ} (sigma : Fin p → ℝ) (r : ℕ) : ℝ :=
  ∑ k, if r ≤ k.val then (sigma k)^2 else 0

theorem validSVD_truncate_error {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V) (r : ℕ) :
    matrixEnergy (B - truncate U sigma V r) = tailEnergy sigma r := by
  rw [truncate, validSVD_error_energy h]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.val < r
  · simp [hk, Nat.not_le.mpr hk]
  · simp [hk, Nat.le_of_not_gt hk]

#assert_trust kernel validSVD_energy
#assert_trust kernel validSVD_error_energy
#assert_trust kernel validSVD_truncate_error
#print axioms validSVD_truncate_error

end NLA.Proofs.TR04.SVD
