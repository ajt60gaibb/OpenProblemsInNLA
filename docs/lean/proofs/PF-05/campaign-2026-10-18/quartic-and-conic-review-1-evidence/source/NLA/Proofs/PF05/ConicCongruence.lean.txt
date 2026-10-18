import NLA.Proofs.PF05.ConicPositive
import NLA.Proofs.PF05.ZeroAlternative
import NLA.Proofs.PF05.CongruenceLine
import NLA.Proofs.PF05.PositiveTopology

/-! Classify the actual conic-preserving operator by applying the proved
zero-pair normal form to a fixed genuine rank-three PSD factorization.
Four actual rank-one rows force the canonical parameters to be trivial. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05.ConicCongruence
noncomputable section
open Matrix CoordinateActions
open NLA.Statements.PF05
open scoped BigOperators Matrix
abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev Vec2 := Fin 2 → ℝ

def rowVectors : Fin 4 → Vec2 := ![![1,0],![0,1],![1,1],![1,-1]]
def columnVectors : Fin 3 → Vec2 := ![![0,1],![1,0],![1,-1]]
def rows (i : Fin 4) : M2 := ConicPositive.outer (rowVectors i)
def columns (j : Fin 3) : M2 := ConicPositive.outer (columnVectors j)
def matrix : Matrix (Fin 4) (Fin 3) ℝ := fun i j => Matrix.trace (rows i * columns j)

theorem outer_psd (v : Vec2) : PositiveSemidefinite (ConicPositive.outer v) := by
  apply (psd_iff_posSemidef _).mpr
  simpa only [ConicPositive.outer,star_trivial] using Matrix.posSemidef_vecMulVec_self_star v

theorem actual_factorization : Factorization matrix rows columns :=
  ⟨fun _ => outer_psd _, fun _ => outer_psd _, fun _ _ => rfl⟩

theorem actual_rank : matrix.rank = 3 := by
  let K : M3 := !![0,1,1;1,0,1;1,1,0]
  have hsub : matrix.submatrix Fin.castSucc id = K := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [matrix,rows,columns,rowVectors,columnVectors,ConicPositive.outer,
        Matrix.vecMulVec_apply,Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two,
        Matrix.submatrix,K,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons]
  have hdet : K.det ≠ 0 := by
    norm_num [K,Matrix.det_fin_three,Matrix.cons_val,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons]
  have hK : K.rank = 3 := by
    simpa using Matrix.rank_of_isUnit K (K.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet))
  apply Nat.le_antisymm (Matrix.rank_le_width matrix)
  have hb := Matrix.rank_submatrix_le matrix Fin.castSucc id
  rw [hsub,hK] at hb
  exact hb

/-- The entire actual operator is a genuine congruence operator. The
positive-component hypotheses are supplied by actual aggregates in use. -/
theorem operator_congruence (L : M3) (hL : L.det ≠ 0)
    (h : ∀ v : Vec2, (primal L (ConicPositive.outer v)).det = 0)
    (P : M2) (hP : P.PosDef) (hLP : (primal L P).PosDef) :
    ∃ S : M2, S.det ≠ 0 ∧ L = congruenceOperator S := by
  have ht : Factorization matrix (fun i => primal L (rows i))
      (fun j => dual L⁻¹ (columns j)) := by
    apply factorization_primal_dual matrix rows columns actual_factorization L L⁻¹
      (L.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hL))
    · intro i
      exact ConicPositive.primal_outer_psd L hL h P hP hLP (rowVectors i)
    · intro j
      exact ConicPositive.dual_inv_outer_psd L hL h P hP hLP (columnVectors j)
  have hr : rows 0 = !![1,0;0,0] := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [rows,rowVectors,ConicPositive.outer,Matrix.vecMulVec_apply]
  have hc : columns 0 = !![0,0;0,1] := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [columns,columnVectors,ConicPositive.outer,Matrix.vecMulVec_apply]
  obtain ⟨U, α, β, γ, hU, hγ, hmap, _⟩ := zeroAlternative_normal_form matrix rows
    (fun i => primal L (rows i)) columns (fun j => dual L⁻¹ (columns j))
    actual_factorization ht actual_rank 0 0 hr hc
  have hz (i : Fin 4) : (zeroCanonicalPrimal α β γ (rows i)).det = 0 := by
    rw [← hmap i]
    simp only [primalCongruence,Matrix.det_mul,Matrix.det_transpose]
    change U.det * (primal L (ConicPositive.outer (rowVectors i))).det * U.det = 0
    rw [h (rowVectors i)]
    ring
  have hq := hz 1
  have hu := hz 2
  have hv := hz 3
  norm_num [rows,rowVectors,ConicPositive.outer,Matrix.vecMulVec_apply,
    zeroCanonicalPrimal,Matrix.det_fin_two,Matrix.cons_val,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at hq hu hv
  have hb : β = 0 := by nlinarith
  have ha : α = 0 := by nlinarith
  have hg : γ = 1 := by nlinarith
  have hid (i : Fin 4) : primalCongruence U (primal L (rows i)) = rows i := by
    rw [hmap i,ha,hb,hg]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [zeroCanonicalPrimal,(actual_factorization.1 i).1 1 0]
  have hback (i : Fin 4) : primal L (rows i) = primalCongruence U⁻¹ (rows i) := by
    calc
      primal L (rows i) = primalCongruence U⁻¹ (primalCongruence U (primal L (rows i))) :=
        (primalCongruence_cancel_left U _ hU).symm
      _ = primalCongruence U⁻¹ (rows i) := congrArg (primalCongruence U⁻¹) (hid i)
  exact ⟨U⁻¹,congruence_inv_det_ne_zero U hU,
    operator_eq_congruence_of_factors matrix rows columns actual_factorization actual_rank L U⁻¹ hback⟩

theorem primal_sum {ι : Type*} (s : Finset ι) (L : M3) (A : ι → M2) :
    primal L (∑ i ∈ s, A i) = ∑ i ∈ s, primal L (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs => simp only [Finset.sum_insert hi,ConicPositive.primal_add,hs]

/-- A conic-preserving actual alternative is congruent in precisely the
original factor coordinates. The positive aggregate is derived here from
the two actual rank-three factorizations. -/
theorem congruent_of_conic_alternative {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A At : Fin p → M2) (B Bt : Fin q → M2)
    (hfact : Factorization M A B) (ht : Factorization M At Bt) (hrank : M.rank = 3)
    (L : M3) (hL : L.det ≠ 0) (hmap : ∀ i, At i = primal L (A i))
    (h : ∀ v : Vec2, (primal L (ConicPositive.outer v)).det = 0) :
    Congruent A At B Bt := by
  have hp := PositiveTopology.sum_rows_posDef M A B hfact hrank
  have hpt := PositiveTopology.sum_rows_posDef M At Bt ht hrank
  have hsum : primal L (∑ i, A i) = ∑ i, At i := by
    rw [primal_sum]
    exact Finset.sum_congr rfl (fun i _ => (hmap i).symm)
  have hLP : (primal L (∑ i, A i)).PosDef := hsum.symm ▸ hpt
  obtain ⟨S, hS, hOp⟩ := operator_congruence L hL h (∑ i, A i) hp hLP
  have hrows : ∀ i, At i = primalCongruence S (A i) := by
    intro i
    rw [hmap i,hOp,primal_congruenceOperator S (A i) (hfact.1 i).1]
  have hg := factorization_congruence M A B hfact S hS
  refine ⟨S,hS,hrows,?_⟩
  intro j
  have hz : Bt j - dualCongruence S (B j) = 0 := by
    apply trace_pairing_left_nondegenerate_of_rank_three M At Bt ht hrank
    · intro u v
      simp only [Matrix.sub_apply]
      rw [(ht.2.1 j).1 u v,dualCongruence_symmetric S (B j) (hfact.2.1 j).1 u v]
    · intro i
      rw [Matrix.mul_sub,Matrix.trace_sub,← ht.2.2 i j]
      have hh := hg.2.2 i j
      change M i j = (primalCongruence S (A i) * dualCongruence S (B j)).trace at hh
      rw [← hrows i] at hh
      linarith
  exact sub_eq_zero.mp hz

#assert_trust kernel actual_rank
#assert_trust kernel operator_congruence
#assert_trust kernel congruent_of_conic_alternative
#print axioms operator_congruence
#print axioms congruent_of_conic_alternative
end
end NLA.Proofs.PF05.ConicCongruence
