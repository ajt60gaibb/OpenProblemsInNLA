import NLA.Proofs.PF05.CoordinateActions
import NLA.Proofs.PF05.Congruence
import NLA.Proofs.PF05.PSDLine

/-! An actual affine line of congruence operators is scalar. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Matrix
namespace NLA.Proofs.PF05
namespace CoordinateActions
open NLA.Statements.PF05

/-- Actual congruence on row coordinates (a,c,b); the factor two occurs in the
third row, as required by the trace pairing. -/
def congruenceOperator (S : M2) : M3 :=
  !![(S 0 0)^2,(S 0 1)^2,S 0 0*S 0 1;
     (S 1 0)^2,(S 1 1)^2,S 1 0*S 1 1;
     2*S 0 0*S 1 0,2*S 0 1*S 1 1,S 0 0*S 1 1+S 0 1*S 1 0]

theorem primal_congruenceOperator (S A : M2) (hs : Symmetric A) :
    primal (congruenceOperator S) A=primalCongruence S A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primal,decodeLeft,leftVector,Matrix.vecMul,dotProduct,
      congruenceOperator,primalCongruence,Matrix.mul_apply,
      Fin.sum_univ_three,Fin.sum_univ_two,hs 1 0] <;> ring

/-- Equality on the actual spanning factor family identifies the entire
coordinate operator with the actual congruence operator. -/
theorem operator_eq_congruence_of_factors {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (hfact : Factorization M A B) (hrank : M.rank=3)
    (C : M3) (S : M2) (h : ∀ i, primal C (A i)=primalCongruence S (A i)) :
    C=congruenceOperator S := by
  have heq : (fun i => primal C (A i))=(fun i => primal (congruenceOperator S) (A i)) := by
    funext i
    rw [primal_congruenceOperator S (A i) (hfact.1 i).1]
    exact h i
  have hc := congrArg leftCoordinates heq
  rw [family_left_primal,family_left_primal] at hc
  obtain ⟨U,hU⟩ := left_inverse_of_row_span (leftCoordinates A)
    (factorization_coordinate_spans M A B hfact hrank).1
  have hh := congrArg (fun X => U*X) hc
  simpa [← Matrix.mul_assoc,hU] using hh

private theorem coefficients_of_two_roots (h q d : ℝ) (hh : 0<h)
    (h1 : (h/2)*q+(h/2)^2*d=0) (h2 : (h/4)*q+(h/4)^2*d=0) : q=0 ∧ d=0 := by
  have hd : h^2*d=0 := by linear_combination 8*h1-16*h2
  have hd0 : d=0 := (mul_eq_zero.mp hd).resolve_left (ne_of_gt (sq_pos_of_pos hh))
  have hq : (h/2)*q=0 := by rw [hd0] at h1; simpa using h1
  exact ⟨(mul_eq_zero.mp hq).resolve_left (ne_of_gt (half_pos hh)),hd0⟩

/-- Each nonzero rank-one PSD matrix is an eigenvector of the direction of an
actual affine line of congruences. The flat segment lemma supplies the exact
rank-one conclusion without selecting a differentiable congruence matrix. -/
theorem rank_one_scalar_of_congruence_line (T : M3) (h : ℝ) (hh : 0<h)
    (hcong : ∀ t : ℝ, 0≤t → t<h →
      ∃ S : M2, S.det≠0 ∧ 1+t • T=congruenceOperator S)
    (X : M2) (hX : PositiveSemidefinite X) (hne : X≠0) (hdX : X.det=0) :
    ∃ d : ℝ, primal T X=d • X := by
  have hseg : ∃ a : ℝ, 0<a ∧ ∀ t, 0≤t → t<a →
      PositiveSemidefinite (X+t • primal T X) := by
    refine ⟨h,hh,?_⟩
    intro t ht hth
    obtain ⟨S,_,hS⟩ := hcong t ht hth
    rw [← primal_one_add_smul T t X hX.1,hS,primal_congruenceOperator S X hX.1]
    exact primalCongruence_psd S X hX
  have hdet (t : ℝ) (ht : 0≤t) (hth : t<h) : (X+t • primal T X).det=0 := by
    obtain ⟨S,_,hS⟩ := hcong t ht hth
    rw [← primal_one_add_smul T t X hX.1,hS,primal_congruenceOperator S X hX.1]
    simp [primalCongruence,Matrix.det_mul,hdX]
  have h1 := hdet (h/2) (half_pos hh).le (half_lt_self hh)
  have h2 := hdet (h/4) (by positivity) (by linarith)
  rw [det_add_smul_two X (primal T X) hX.1 (primal_symmetric _ _),hdX] at h1 h2
  simp only [zero_add] at h1 h2
  have hq := (coefficients_of_two_roots h _ _ hh h1 h2).1
  exact flat_psd_segment_direction_scalar X (primal T X) hX hne
    (primal_symmetric _ _) hdX hq hseg

private theorem scalar_of_four_rays (T : M3)
    (hP : ∃ a : ℝ, primal T !![1,0;0,0]=a • !![1,0;0,0])
    (hQ : ∃ b : ℝ, primal T !![0,0;0,1]=b • !![0,0;0,1])
    (hU : ∃ c : ℝ, primal T !![1,1;1,1]=c • !![1,1;1,1])
    (hV : ∃ d : ℝ, primal T !![1,-1;-1,1]=d • !![1,-1;-1,1]) :
    ∃ a : ℝ, T=a • (1:M3) := by
  obtain ⟨a,hP⟩ := hP
  obtain ⟨b,hQ⟩ := hQ
  obtain ⟨c,hU⟩ := hU
  obtain ⟨d,hV⟩ := hV
  have p0 := congrArg (fun X : M2 => X 0 0) hP
  have p1 := congrArg (fun X : M2 => X 1 1) hP
  have p2 := congrArg (fun X : M2 => X 0 1) hP
  have q0 := congrArg (fun X : M2 => X 0 0) hQ
  have q1 := congrArg (fun X : M2 => X 1 1) hQ
  have q2 := congrArg (fun X : M2 => X 0 1) hQ
  have u0 := congrArg (fun X : M2 => X 0 0) hU
  have u1 := congrArg (fun X : M2 => X 1 1) hU
  have u2 := congrArg (fun X : M2 => X 0 1) hU
  have v0 := congrArg (fun X : M2 => X 0 0) hV
  have v1 := congrArg (fun X : M2 => X 1 1) hV
  have v2 := congrArg (fun X : M2 => X 0 1) hV
  simp [primal,decodeLeft,leftVector,Matrix.vecMul,dotProduct,Fin.sum_univ_three,
    Matrix.smul_apply,smul_eq_mul] at p0 p1 p2 q0 q1 q2 u0 u1 u2 v0 v1 v2
  refine ⟨a,?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply,smul_eq_mul] <;> linarith

/-- A line beginning at the identity and consisting of actual congruences on
an interval can only have scalar direction. -/
theorem congruence_line_scalar (T : M3) (h : ℝ) (hh : 0<h)
    (hcong : ∀ t : ℝ, 0≤t → t<h →
      ∃ S : M2, S.det≠0 ∧ 1+t • T=congruenceOperator S) :
    ∃ d : ℝ, T=d • (1:M3) := by
  apply scalar_of_four_rays T
  all_goals
    apply rank_one_scalar_of_congruence_line T h hh hcong
    · apply (psd_fin_two_iff _).mpr
      refine ⟨?_,by norm_num,by norm_num,by norm_num [Matrix.det_fin_two]⟩
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num
    · intro heq
      have he := congrArg Matrix.trace heq
      norm_num [Matrix.trace_fin_two] at he
    · norm_num [Matrix.det_fin_two]

#assert_trust kernel primal_congruenceOperator
#assert_trust kernel operator_eq_congruence_of_factors
#assert_trust kernel rank_one_scalar_of_congruence_line
#assert_trust kernel congruence_line_scalar
#print axioms congruence_line_scalar
end CoordinateActions
end NLA.Proofs.PF05
