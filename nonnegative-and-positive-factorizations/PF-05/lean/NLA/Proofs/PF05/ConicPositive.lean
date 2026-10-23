import NLA.Proofs.PF05.ConicDeterminant
import NLA.Proofs.PF05.PositiveReduction
import NLA.Proofs.PF05.OperatorFactorization

/-! Choosing the actual positive component of a rank-one-conic preserver
from a single actual positive definite aggregate and its positive image. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05.ConicPositive
noncomputable section
open Matrix CoordinateActions
open NLA.Statements.PF05
open scoped BigOperators Matrix
abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev Vec2 := Fin 2 → ℝ
def outer (v : Vec2) : M2 := Matrix.vecMulVec v v
def polar (P U : M2) : ℝ := (P + U).det - P.det - U.det

theorem primal_add (L : M3) (A B : M2) : primal L (A+B)=primal L A+primal L B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primal, decodeLeft, leftVector, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
      Matrix.add_apply, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring

theorem polar_outer (P : M2) (hP : Symmetric P) (v : Vec2) :
    polar P (outer v) = ![-v 1,v 0] ⬝ᵥ (P *ᵥ ![-v 1,v 0]) := by
  simp [polar, outer, Matrix.det_fin_two, Matrix.vecMulVec_apply, hP 1 0,
    dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem polar_outer_pos (P : M2) (hP : P.PosDef) (v : Vec2) (hv : v ≠ 0) :
    0 < polar P (outer v) := by
  have hsym : Symmetric P := fun i j => (Matrix.isHermitian_iff_isSymm.mp hP.1).apply j i
  rw [polar_outer P hsym]
  have hw : (![-v 1,v 0] : Vec2) ≠ 0 := by
    intro hz
    apply hv
    have h0 := congrFun hz 0
    have h1 := congrFun hz 1
    ext i
    fin_cases i
    · simpa using h1
    · simpa using h0
  simpa only [star_trivial] using hP.dotProduct_mulVec_pos hw

theorem psd_or_neg_of_det_nonneg (U : M2) (hs : Symmetric U) (hd : 0 ≤ U.det) :
    PositiveSemidefinite U ∨ PositiveSemidefinite (-U) := by
  have hprod : 0 ≤ U 0 0 * U 1 1 := by
    rw [Matrix.det_fin_two, hs 1 0] at hd
    nlinarith [sq_nonneg (U 0 1)]
  have hneg (ha : U 0 0 ≤ 0) (hc : U 1 1 ≤ 0) : PositiveSemidefinite (-U) := by
    apply (psd_fin_two_iff _).mpr
    refine ⟨?_, by simpa using ha, by simpa using hc, ?_⟩
    · intro i j
      simp [Matrix.neg_apply, hs i j]
    · simpa [Matrix.det_fin_two] using hd
  by_cases ha : 0 ≤ U 0 0
  · by_cases hc : 0 ≤ U 1 1
    · exact Or.inl ((psd_fin_two_iff _).mpr ⟨hs, ha, hc, hd⟩)
    · exact Or.inr (hneg (by nlinarith) (le_of_not_ge hc))
  · exact Or.inr (hneg (le_of_not_ge ha) (by nlinarith))

theorem psd_of_det_zero_polar_pos (P U : M2) (hP : P.PosDef)
    (hs : Symmetric U) (hd : U.det = 0) (hp : 0 < polar P U) :
    PositiveSemidefinite U := by
  rcases psd_or_neg_of_det_nonneg U hs hd.ge with hU | hU
  · exact hU
  · have hdneg : (-U).det = 0 := by simpa [Matrix.det_fin_two] using hd
    obtain ⟨v, hv⟩ := outer_of_psd_det_zero (-U) hU hdneg
    have hsym : Symmetric P := fun i j => (Matrix.isHermitian_iff_isSymm.mp hP.1).apply j i
    have hpol : polar P U = -polar P (outer v) := by
      have hu : U = -outer v := by simpa [outer,NLA.Proofs.PF05.outer] using congrArg Neg.neg hv
      rw [hu]
      simp [polar, outer, Matrix.det_fin_two, Matrix.vecMulVec_apply, hsym 1 0]
      ring
    have hnonneg : 0 ≤ polar P (outer v) := by
      rw [polar_outer P hsym]
      simpa only [star_trivial] using
        (Matrix.posSemidef_iff_dotProduct_mulVec.mp hP.posSemidef).2 ![-v 1,v 0]
    linarith

theorem polar_scale (L : M3)
    (h : ∀ v : Vec2, (primal L (outer v)).det = 0)
    (P U : M2) (hP : Symmetric P) (hU : Symmetric U) :
    polar (primal L P) (primal L U) = ConicDeterminant.scale L * polar P U := by
  have hsum : Symmetric (P+U) := fun i j => by simp [Matrix.add_apply,hP i j,hU i j]
  unfold polar
  rw [← primal_add, ConicDeterminant.determinant_scale L h (P+U) hsum,
    ConicDeterminant.determinant_scale L h P hP,
    ConicDeterminant.determinant_scale L h U hU]
  ring

/-- An actual positive aggregate and its positive image force the positive
component on every rank-one PSD input. -/
theorem primal_outer_psd (L : M3) (hL : L.det ≠ 0)
    (h : ∀ v : Vec2, (primal L (outer v)).det = 0)
    (P : M2) (hP : P.PosDef) (hLP : (primal L P).PosDef) (v : Vec2) :
    PositiveSemidefinite (primal L (outer v)) := by
  by_cases hv : v = 0
  · subst v
    simp only [outer, Matrix.vecMulVec_zero, primal_zero_input]
    exact (psd_iff_posSemidef _).mpr Matrix.PosSemidef.zero
  · have hsym : Symmetric P := fun i j => (Matrix.isHermitian_iff_isSymm.mp hP.1).apply j i
    have hsx : Symmetric (outer v) := fun i j => by simp [outer,Matrix.vecMulVec_apply,mul_comm]
    have hp := mul_pos (ConicDeterminant.scale_pos L hL h) (polar_outer_pos P hP v hv)
    rw [← polar_scale L h P (outer v) hsym hsx] at hp
    exact psd_of_det_zero_polar_pos (primal L P) (primal L (outer v)) hLP
      (primal_symmetric L _) (h v) hp

theorem primal_comp (C D : M3) (A : M2) :
    primal D (primal C A) = primal (C*D) A := by
  apply leftVector_injective_symmetric _ _ (primal_symmetric _ _) (primal_symmetric _ _)
  simp [Matrix.vecMul_vecMul]

theorem primal_inv_left (L : M3) (hL : L.det ≠ 0) (A : M2) (hA : Symmetric A) :
    primal L (primal L⁻¹ A) = A := by
  rw [primal_comp, L.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hL), primal_one A hA]

theorem primal_inv_outer_psd (L : M3) (hL : L.det ≠ 0)
    (h : ∀ v : Vec2, (primal L (outer v)).det = 0)
    (P : M2) (hP : P.PosDef) (hLP : (primal L P).PosDef) (v : Vec2) :
    PositiveSemidefinite (primal L⁻¹ (outer v)) := by
  have hi : L⁻¹.det ≠ 0 := by
    rw [Matrix.det_nonsing_inv]
    simpa only [Ring.inverse_eq_inv] using inv_ne_zero hL
  have hback (A : M2) (hA : Symmetric A) : primal L⁻¹ (primal L A) = A := by
    rw [primal_comp, L.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hL), primal_one A hA]
  have hconic : ∀ w : Vec2, (primal L⁻¹ (outer w)).det = 0 := by
    intro w
    have hs : Symmetric (outer w) := fun i j => by simp [outer,Matrix.vecMulVec_apply,mul_comm]
    have hh := ConicDeterminant.determinant_scale L h (primal L⁻¹ (outer w))
      (primal_symmetric _ _)
    rw [primal_inv_left L hL (outer w) hs] at hh
    have hz : (outer w).det = 0 := by simp [outer, Matrix.det_fin_two,Matrix.vecMulVec_apply]; ring
    rw [hz] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left (ne_of_gt (ConicDeterminant.scale_pos L hL h))
  apply primal_outer_psd L⁻¹ hi hconic (primal L P) hLP
  simpa only [hback P (fun i j => (Matrix.isHermitian_iff_isSymm.mp hP.1).apply j i)] using hP

theorem trace_outer_right (U : M2) (v : Vec2) :
    Matrix.trace (U * outer v) = v ⬝ᵥ (U *ᵥ v) := by
  simp [outer, Matrix.trace_fin_two,Matrix.mul_apply,Matrix.vecMulVec_apply,
    dotProduct, Matrix.mulVec,Fin.sum_univ_two]
  ring

/-- The actual weighted inverse-dual map preserves each rank-one PSD matrix.
This follows from the proved inverse primal positivity and the trace pairing. -/
theorem dual_inv_outer_psd (L : M3) (hL : L.det ≠ 0)
    (h : ∀ v : Vec2, (primal L (outer v)).det = 0)
    (P : M2) (hP : P.PosDef) (hLP : (primal L P).PosDef) (w : Vec2) :
    PositiveSemidefinite (dual L⁻¹ (outer w)) := by
  apply (psd_iff_posSemidef _).mpr
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · rw [Matrix.isHermitian_iff_isSymm]
    exact Matrix.IsSymm.ext (fun i j => dual_symmetric _ _ j i)
  · intro v
    have hv : Symmetric (outer v) := fun i j => by simp [outer,Matrix.vecMulVec_apply,mul_comm]
    have hw : Symmetric (outer w) := fun i j => by simp [outer,Matrix.vecMulVec_apply,mul_comm]
    have hY := primal_inv_outer_psd L hL h P hP hLP v
    have ht := trace_primal_dual L L⁻¹ (L.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hL))
      (primal L⁻¹ (outer v)) (outer w) (primal_symmetric _ _) hw
    rw [primal_inv_left L hL (outer v) hv, Matrix.trace_mul_comm (outer v),
      trace_outer_right, trace_outer_right] at ht
    have hn := (Matrix.posSemidef_iff_dotProduct_mulVec.mp ((psd_iff_posSemidef _).mp hY)).2 w
    simpa only [star_trivial, ht] using hn

#assert_trust kernel psd_or_neg_of_det_nonneg
#assert_trust kernel primal_outer_psd
#assert_trust kernel primal_inv_outer_psd
#assert_trust kernel dual_inv_outer_psd
#print axioms primal_outer_psd
#print axioms dual_inv_outer_psd
end
end NLA.Proofs.PF05.ConicPositive
