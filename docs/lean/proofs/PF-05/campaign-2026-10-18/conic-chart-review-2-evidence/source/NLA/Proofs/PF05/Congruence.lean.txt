import NLA.Proofs.PF05.Basic

/-! The exact primal/dual congruence action in the frozen PF-05 target.
This establishes preservation of factorizations and feasible directions. -/
set_option autoImplicit false
namespace NLA.Proofs.PF05
open NLA.Statements.PF05

def primalCongruence (S A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  S.transpose * A * S

noncomputable def dualCongruence (S B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  S⁻¹ * B * (S⁻¹).transpose

theorem primalCongruence_psd (S A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : PositiveSemidefinite A) : PositiveSemidefinite (primalCongruence S A) := by
  apply (psd_iff_posSemidef _).mpr
  have hp := ((psd_iff_posSemidef A).mp hA).conjTranspose_mul_mul_same S
  simpa [primalCongruence, Matrix.conjTranspose_eq_transpose_of_trivial] using hp

theorem dualCongruence_psd (S B : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : PositiveSemidefinite B) : PositiveSemidefinite (dualCongruence S B) := by
  apply (psd_iff_posSemidef _).mpr
  have hp := ((psd_iff_posSemidef B).mp hB).mul_mul_conjTranspose_same S⁻¹
  simpa [dualCongruence, Matrix.conjTranspose_eq_transpose_of_trivial] using hp

theorem trace_congruence_invariant
    (S A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hdet : S.det ≠ 0) :
    Matrix.trace (primalCongruence S A * dualCongruence S B) =
      Matrix.trace (A * B) := by
  have hunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hdet
  have hright : S * S⁻¹ = 1 := S.mul_nonsing_inv hunit
  have htrans : (S⁻¹).transpose * S.transpose = 1 := by
    rw [← Matrix.transpose_mul, hright, Matrix.transpose_one]
  calc
    Matrix.trace (primalCongruence S A * dualCongruence S B)
        = Matrix.trace ((S.transpose * (A * B)) * (S⁻¹).transpose) := by
            simp only [primalCongruence, dualCongruence, Matrix.mul_assoc]
            rw [← Matrix.mul_assoc S S⁻¹ (B * (S⁻¹).transpose), hright]
            simp
    _ = Matrix.trace ((S⁻¹).transpose * (S.transpose * (A * B))) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (A * B) := by simp [← Matrix.mul_assoc, htrans]

theorem factorization_congruence {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B : Fin q → Matrix (Fin 2) (Fin 2) ℝ)
    (h : Factorization M A B)
    (S : Matrix (Fin 2) (Fin 2) ℝ) (hdet : S.det ≠ 0) :
    Factorization M (fun i => primalCongruence S (A i))
      (fun j => dualCongruence S (B j)) := by
  refine ⟨fun i => primalCongruence_psd S (A i) (h.1 i),
    fun j => dualCongruence_psd S (B j) (h.2.1 j), ?_⟩
  intro i j
  rw [h.2.2 i j]
  exact (trace_congruence_invariant S (A i) (B j) hdet).symm

theorem primalCongruence_symmetric (S E : Matrix (Fin 2) (Fin 2) ℝ)
    (hE : NLA.Statements.PF05.Symmetric E) :
    NLA.Statements.PF05.Symmetric (primalCongruence S E) := by
  have hHerm : E.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    exact Matrix.IsSymm.ext fun i j => hE j i
  have hResult := Matrix.isHermitian_conjTranspose_mul_mul S hHerm
  rw [Matrix.isHermitian_iff_isSymm] at hResult
  intro i j
  have hr : (primalCongruence S E).IsSymm := by
    simpa [primalCongruence, Matrix.conjTranspose_eq_transpose_of_trivial] using hResult
  exact hr.apply j i

theorem dualCongruence_symmetric (S F : Matrix (Fin 2) (Fin 2) ℝ)
    (hF : NLA.Statements.PF05.Symmetric F) :
    NLA.Statements.PF05.Symmetric (dualCongruence S F) := by
  have hHerm : F.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    exact Matrix.IsSymm.ext fun i j => hF j i
  have hResult := Matrix.isHermitian_mul_mul_conjTranspose S⁻¹ hHerm
  rw [Matrix.isHermitian_iff_isSymm] at hResult
  intro i j
  have hr : (dualCongruence S F).IsSymm := by
    simpa [dualCongruence, Matrix.conjTranspose_eq_transpose_of_trivial] using hResult
  exact hr.apply j i

theorem primalCongruence_add_smul (S A E : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    primalCongruence S (A + t • E) =
      primalCongruence S A + t • primalCongruence S E := by
  simp [primalCongruence, Matrix.mul_add, Matrix.add_mul]

theorem dualCongruence_add_smul (S B F : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    dualCongruence S (B + t • F) =
      dualCongruence S B + t • dualCongruence S F := by
  simp [dualCongruence, Matrix.mul_add, Matrix.add_mul]

theorem feasibleDirection_congruence {p q : ℕ}
    (A E : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B F : Fin q → Matrix (Fin 2) (Fin 2) ℝ)
    (hEF : FeasibleDirection A E B F)
    (S : Matrix (Fin 2) (Fin 2) ℝ) (hdet : S.det ≠ 0) :
    FeasibleDirection
      (fun i => primalCongruence S (A i)) (fun i => primalCongruence S (E i))
      (fun j => dualCongruence S (B j)) (fun j => dualCongruence S (F j)) := by
  refine ⟨fun i => primalCongruence_symmetric S (E i) (hEF.1 i),
    fun j => dualCongruence_symmetric S (F j) (hEF.2.1 j), ?_, ?_⟩
  · intro i j
    rw [trace_congruence_invariant S (E i) (B j) hdet,
      trace_congruence_invariant S (A i) (F j) hdet]
    exact hEF.2.2.1 i j
  · obtain ⟨h, hh, htime⟩ := hEF.2.2.2
    refine ⟨h, hh, ?_⟩
    intro t ht hth
    obtain ⟨hpr, hdu⟩ := htime t ht hth
    constructor
    · intro i
      rw [← primalCongruence_add_smul]
      exact primalCongruence_psd S _ (hpr i)
    · intro j
      rw [← dualCongruence_add_smul]
      exact dualCongruence_psd S _ (hdu j)

end NLA.Proofs.PF05
