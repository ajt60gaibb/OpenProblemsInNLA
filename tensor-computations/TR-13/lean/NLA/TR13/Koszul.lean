import NLA.TR13.Definitions
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Matrix

noncomputable section
open scoped BigOperators
open Matrix

namespace NLA.TR13

abbrev ThreeSlices (a : ℕ) := Fin 3 → Matrix (Fin a) (Fin a) ℂ
abbrev KoszulIndex (a : ℕ) := Fin 3 × Fin a

/-- The three-slice Koszul flattening, in block-coordinate order. -/
def koszul {a : ℕ} {R : Type*} [Ring R]
    (M : Fin 3 → Matrix (Fin a) (Fin a) R) :
    Matrix (KoszulIndex a) (KoszulIndex a) R :=
  fun i j => !![-M 1 i.2 j.2, M 0 i.2 j.2, 0;
    -M 2 i.2 j.2, 0, M 0 i.2 j.2;
    0, -M 2 i.2 j.2, M 1 i.2 j.2] i.1 j.1

def scalarKoszul (c : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-c 1, c 0, 0; -c 2, 0, c 0; 0, -c 2, c 1]

theorem matrix_rank_pos_of_entry_ne_zero {ι κ : Type*}
    [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) (i : ι) (j : κ)
    (h : A i j ≠ 0) : 1 ≤ A.rank := by
  classical
  let B : Matrix (Fin 1) (Fin 1) ℂ := A.submatrix (fun _ => i) (fun _ => j)
  have hB : B.det ≠ 0 := by simpa [B, Matrix.det_fin_one] using h
  have hr : B.rank = 1 := by simpa using Matrix.rank_of_det_ne_zero hB
  have hh : B.rank ≤ A.rank := Matrix.rank_submatrix_le A
    (fun _ : Fin 1 => i) (fun _ : Fin 1 => j)
  rwa [hr] at hh

theorem scalarKoszul_rank_le (c : Fin 3 → ℂ) : (scalarKoszul c).rank ≤ 2 := by
  classical
  by_cases hc : c = 0
  · subst c
    have hzero : scalarKoszul (0 : Fin 3 → ℂ) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [scalarKoszul]
    simp [hzero]
  · obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra! h
      exact hc (funext h)
    let B : Matrix (Fin 3) (Fin 1) ℂ := fun i _ => c i
    have hrB : 1 ≤ B.rank := matrix_rank_pos_of_entry_ne_zero B i 0 hi
    have hz : scalarKoszul c * B = 0 := by
      ext i j
      simp only [Matrix.mul_apply]
      fin_cases i <;> simp [scalarKoszul, B, Fin.sum_univ_succ] <;> ring
    have h := Matrix.rank_add_rank_le_card_of_mul_eq_zero hz
    simp only [Fintype.card_fin] at h
    omega

theorem koszul_pure_rank_le {a : ℕ} (u v : Fin a → ℂ) (c : Fin 3 → ℂ) :
    (koszul (fun j x y => c j * u x * v y)).rank ≤ 2 := by
  classical
  let L : Matrix (KoszulIndex a) (Fin 3) ℂ :=
    fun i j => if i.1 = j then u i.2 else 0
  let R : Matrix (Fin 3) (KoszulIndex a) ℂ :=
    fun i j => if i = j.1 then v j.2 else 0
  have hfactor : koszul (fun j x y => c j * u x * v y) = L * scalarKoszul c * R := by
    ext ⟨i, x⟩ ⟨j, y⟩
    simp only [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      simp [koszul, L, R, scalarKoszul, mul_comm, mul_left_comm]
  rw [hfactor]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_mul_le_right _ _).trans (scalarKoszul_rank_le c))

theorem koszul_add {a : ℕ} (M N : ThreeSlices a) :
    koszul (M + N) = koszul M + koszul N := by
  ext ⟨i, x⟩ ⟨j, y⟩
  fin_cases i <;> fin_cases j <;> simp [koszul] <;> ring

theorem koszul_zero (a : ℕ) : koszul (0 : ThreeSlices a) = 0 := by
  ext ⟨i, x⟩ ⟨j, y⟩
  fin_cases i <;> fin_cases j <;> simp [koszul]

theorem koszul_sum {a : ℕ} {ι : Type*} (s : Finset ι) (M : ι → ThreeSlices a) :
    koszul (∑ i ∈ s, M i) = ∑ i ∈ s, koszul (M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [koszul_zero]
  | @insert i s hi ih => simp [hi, koszul_add, ih]

theorem continuous_koszul (a : ℕ) : Continuous (fun M : ThreeSlices a => koszul M) := by
  apply continuous_pi
  rintro ⟨i, x⟩
  apply continuous_pi
  rintro ⟨j, y⟩
  fin_cases i <;> fin_cases j <;> simp only [koszul]
  all_goals fun_prop

end NLA.TR13
