import NLA.Proofs.PF05.InfinitesimalOperator

/-! Concrete actions on symmetric matrices using the weighted trace coordinates.
All dual actions below use the weight two in the off-diagonal coordinate. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
namespace CoordinateActions
noncomputable section
open scoped Matrix
open NLA.Statements.PF05

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ

def leftVector (A : M2) : Fin 3 → ℝ := ![A 0 0,A 1 1,A 0 1]
def rightVector (B : M2) : Fin 3 → ℝ := ![B 0 0,B 1 1,2*B 0 1]
def decodeLeft (x : Fin 3 → ℝ) : M2 := !![x 0,x 2;x 2,x 1]
def decodeRight (y : Fin 3 → ℝ) : M2 := !![y 0,y 2/2;y 2/2,y 1]

@[simp] theorem leftVector_decode (x : Fin 3 → ℝ) : leftVector (decodeLeft x)=x := by
  funext i; fin_cases i <;> simp [leftVector,decodeLeft]
@[simp] theorem rightVector_decode (x : Fin 3 → ℝ) : rightVector (decodeRight x)=x := by
  funext i; fin_cases i <;> simp [rightVector,decodeRight]; ring
@[simp] theorem decodeLeft_vector (A : M2) (hs : Symmetric A) : decodeLeft (leftVector A)=A := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [decodeLeft,leftVector,hs 1 0]
@[simp] theorem decodeRight_vector (A : M2) (hs : Symmetric A) : decodeRight (rightVector A)=A := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [decodeRight,rightVector,hs 1 0]

theorem decodeLeft_symmetric (x : Fin 3 → ℝ) : Symmetric (decodeLeft x) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [decodeLeft]
theorem decodeRight_symmetric (x : Fin 3 → ℝ) : Symmetric (decodeRight x) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [decodeRight]

theorem leftVector_injective_symmetric (A B : M2) (hA : Symmetric A) (hB : Symmetric B)
    (h : leftVector A=leftVector B) : A=B := by
  rw [← decodeLeft_vector A hA, ← decodeLeft_vector B hB, h]
theorem rightVector_injective_symmetric (A B : M2) (hA : Symmetric A) (hB : Symmetric B)
    (h : rightVector A=rightVector B) : A=B := by
  rw [← decodeRight_vector A hA, ← decodeRight_vector B hB, h]

@[simp] theorem leftVector_add (A B : M2) : leftVector (A+B)=leftVector A+leftVector B := by
  funext i; fin_cases i <;> simp [leftVector]
@[simp] theorem rightVector_add (A B : M2) : rightVector (A+B)=rightVector A+rightVector B := by
  funext i; fin_cases i <;> simp [rightVector,mul_add]
@[simp] theorem leftVector_smul (t : ℝ) (A : M2) : leftVector (t • A)=t • leftVector A := by
  funext i; fin_cases i <;> simp [leftVector]
@[simp] theorem rightVector_smul (t : ℝ) (A : M2) : rightVector (t • A)=t • rightVector A := by
  funext i; fin_cases i <;> simp [rightVector,smul_eq_mul]; ring
@[simp] theorem rightVector_zero : rightVector (0:M2)=0 := by simp [rightVector]
@[simp] theorem leftVector_zero : leftVector (0:M2)=0 := by simp [leftVector]

def primal (C : M3) (A : M2) : M2 := decodeLeft (leftVector A ᵥ* C)
def dual (C : M3) (B : M2) : M2 := decodeRight (C *ᵥ rightVector B)

theorem primal_symmetric (C : M3) (A : M2) : Symmetric (primal C A) := decodeLeft_symmetric _
theorem dual_symmetric (C : M3) (B : M2) : Symmetric (dual C B) := decodeRight_symmetric _
@[simp] theorem leftVector_primal (C : M3) (A : M2) : leftVector (primal C A)=leftVector A ᵥ* C := leftVector_decode _
@[simp] theorem rightVector_dual (C : M3) (B : M2) : rightVector (dual C B)=C *ᵥ rightVector B := rightVector_decode _
@[simp] theorem primal_one (A : M2) (hs : Symmetric A) : primal 1 A=A := by
  simp [primal,decodeLeft_vector A hs]
@[simp] theorem dual_one (A : M2) (hs : Symmetric A) : dual 1 A=A := by
  simp [dual,decodeRight_vector A hs]
@[simp] theorem primal_zero_input (C : M3) : primal C 0=0 := by
  simp [primal,decodeLeft]
  ext i j; fin_cases i <;> fin_cases j <;> rfl
@[simp] theorem dual_zero_input (C : M3) : dual C 0=0 := by
  simp [dual,decodeRight]
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem primal_one_add_smul (T : M3) (t : ℝ) (A : M2) (hs : Symmetric A) :
    primal (1+t • T) A=A+t • primal T A := by
  have hr : Symmetric (A+t • primal T A) := by
    intro i j
    simp [Matrix.add_apply,Matrix.smul_apply, hs i j, primal_symmetric T A i j]
  apply leftVector_injective_symmetric _ _ (primal_symmetric _ _) hr
  simp [Matrix.vecMul_add, Matrix.vecMul_smul]

theorem dual_one_add_smul (T : M3) (t : ℝ) (B : M2) (hs : Symmetric B) :
    dual (1+t • T) B=B+t • dual T B := by
  have hr : Symmetric (B+t • dual T B) := by
    intro i j
    simp [Matrix.add_apply,Matrix.smul_apply, hs i j, dual_symmetric T B i j]
  apply rightVector_injective_symmetric _ _ (dual_symmetric _ _) hr
  simp [Matrix.add_mulVec, Matrix.smul_mulVec]

theorem family_left_primal {p : ℕ} (C : M3) (A : Fin p → M2) :
    leftCoordinates (fun i => primal C (A i))=leftCoordinates A*C := by
  ext i j
  change leftVector (primal C (A i)) j = (leftVector (A i) ᵥ* C) j
  exact congrFun (leftVector_primal C (A i)) j

theorem family_right_dual {q : ℕ} (C : M3) (B : Fin q → M2) :
    rightCoordinates (fun j => dual C (B j))=C*rightCoordinates B := by
  ext i j
  change rightVector (dual C (B j)) i = (C *ᵥ rightVector (B j)) i
  exact congrFun (rightVector_dual C (B j)) i

/-- The exact resolvent action on a genuine eigenvector, with both guards
made explicit. -/
theorem dual_resolvent_eigen (T : M3) (B : M2) (hs : Symmetric B)
    (mu t : ℝ) (heig : dual T B=mu • B)
    (hinv : (1+t • T).det ≠ 0) (hscalar : 1+t*mu ≠ 0) :
    dual (1+t • T)⁻¹ B=(1+t*mu)⁻¹ • B := by
  have hr : Symmetric ((1+t*mu)⁻¹ • B) := by
    intro i j; simp [Matrix.smul_apply,hs i j]
  apply rightVector_injective_symmetric _ _ (dual_symmetric _ _) hr
  have hy : T *ᵥ rightVector B=mu • rightVector B := by
    have h := congrArg rightVector heig
    simpa using h
  have hCy : (1+t • T) *ᵥ rightVector B=(1+t*mu) • rightVector B := by
    simp [Matrix.add_mulVec,Matrix.smul_mulVec,hy,smul_smul,add_smul]
  have hc : (1+t • T)⁻¹ * (1+t • T)=1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hinv)
  simp only [rightVector_dual,rightVector_smul]
  calc
    (1+t • T)⁻¹ *ᵥ rightVector B =
        (1+t • T)⁻¹ *ᵥ ((1+t*mu)⁻¹ • ((1+t • T) *ᵥ rightVector B)) := by
      rw [hCy,smul_smul,inv_mul_cancel₀ hscalar,one_smul]
    _ = (1+t*mu)⁻¹ • rightVector B := by
      rw [Matrix.mulVec_smul,Matrix.mulVec_mulVec,hc,Matrix.one_mulVec]

#assert_trust kernel primal_one_add_smul
#assert_trust kernel dual_one_add_smul
#assert_trust kernel family_left_primal
#assert_trust kernel family_right_dual
#assert_trust kernel dual_resolvent_eigen
#print axioms dual_resolvent_eigen

end
end CoordinateActions
end NLA.Proofs.PF05
