import ProofProject.BasisEnergy
import ProofProject.DiagonalOperators

/-!
# Elementary patterns and tails in a fixed finite basis

All operator norms in this file refer to the given norm on the same space.
In particular, the adjacent-tail argument can be reused after perturbing a
Hilbert metric without transferring the old projection constants.
-/

noncomputable section

open scoped BigOperators

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [FiniteDimensional ℂ H] {N : ℕ}

/-- A diagonal map multiplies the coefficients of a finite synthesis. -/
lemma basisDiagonal_finiteSynthesis (b : Module.Basis (Fin N) ℂ H)
    (a c : Fin N → ℂ) :
    basisDiagonal b a (finiteSynthesis b c) = finiteSynthesis b (a * c) := by
  simp only [finiteSynthesis, map_sum, map_smul, basisDiagonal_basis, smul_smul,
    Pi.mul_apply]
  congr 1
  funext i
  rw [mul_comm]

/-- An elementary pattern as a continuous operator in the given basis. -/
def basisPattern (b : Module.Basis (Fin N) ℂ H) (i : Fin N) (z : ℂ) : H →L[ℂ] H :=
  basisDiagonal b (elementaryPattern i z (fun _ => 1))

lemma basisPattern_finiteSynthesis (b : Module.Basis (Fin N) ℂ H)
    (i : Fin N) (z : ℂ) (c : Fin N → ℂ) :
    basisPattern b i z (finiteSynthesis b c) =
      finiteSynthesis b (elementaryPattern i z c) := by
  rw [basisPattern, basisDiagonal_finiteSynthesis]
  congr 1
  funext j
  simp only [Pi.mul_apply, elementaryPattern, mul_one]
  split_ifs <;> simp

/-- The projection onto a terminal set of coordinates. -/
def basisTail (b : Module.Basis (Fin N) ℂ H) (k : ℕ) : H →L[ℂ] H :=
  basisDiagonal b (fun j => if k ≤ j.val then 1 else 0)

lemma basisTail_finiteSynthesis (b : Module.Basis (Fin N) ℂ H)
    (k : ℕ) (c : Fin N → ℂ) :
    basisTail b k (finiteSynthesis b c) = synthesisTail b c k := by
  rw [basisTail, basisDiagonal_finiteSynthesis]
  simp only [finiteSynthesis, synthesisTail, Pi.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

lemma basisTail_apply (b : Module.Basis (Fin N) ℂ H) (k : ℕ) (x : H) :
    basisTail b k x = synthesisTail b (fun j => b.repr x j) k := by
  have hx : finiteSynthesis b (fun j => b.repr x j) = x := b.sum_repr x
  rw [← basisTail_finiteSynthesis, hx]

/-- Adjacent tails isolate precisely the coordinate projection. -/
lemma basisTail_sub_succ (b : Module.Basis (Fin N) ℂ H) (i : Fin N) :
    basisTail b i.val - basisTail b (i.val + 1) = basisCoordinate b i := by
  ext x
  simp only [sub_apply, basisTail_apply, basisCoordinate_apply]
  exact synthesisTail_sub_succ b (fun j => b.repr x j) i

/-- A common elementary-pattern bound controls all tail projections. -/
theorem norm_basisTail_le (b : Module.Basis (Fin N) ℂ H) {K : ℝ} (hK : 0 ≤ K)
    (hpattern : ∀ (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 → ‖basisPattern b i z‖ ≤ K)
    (k : ℕ) : ‖basisTail b k‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro x
  rw [basisTail_apply]
  have hx : finiteSynthesis b (fun j => b.repr x j) = x := b.sum_repr x
  conv_rhs => rw [← hx]
  apply tail_bound_of_elementaryPattern_bound b _ K hK
  intro i z hz
  rw [← basisPattern_finiteSynthesis]
  exact ((basisPattern b i z).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hpattern i z hz) (norm_nonneg _))

/-- The same-norm adjacent-tail estimate gives the sharp constant `2K`. -/
theorem norm_basisCoordinate_le_of_patterns (b : Module.Basis (Fin N) ℂ H)
    {K : ℝ} (hK : 0 ≤ K)
    (hpattern : ∀ (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 → ‖basisPattern b i z‖ ≤ K)
    (i : Fin N) : ‖basisCoordinate b i‖ ≤ 2 * K := by
  rw [← basisTail_sub_succ b i]
  calc
    ‖basisTail b i.val - basisTail b (i.val + 1)‖ ≤
        ‖basisTail b i.val‖ + ‖basisTail b (i.val + 1)‖ := norm_sub_le _ _
    _ ≤ K + K := add_le_add (norm_basisTail_le b hK hpattern _)
      (norm_basisTail_le b hK hpattern _)
    _ = 2 * K := by ring

end ProofProject
