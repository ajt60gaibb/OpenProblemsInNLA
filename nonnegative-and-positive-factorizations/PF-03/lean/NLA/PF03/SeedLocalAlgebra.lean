import NLA.PF03.CubicLowerBounds
import NLA.PF03.SeedQuadraticForm

/-!
Algebraic transport of actual local restrictions, kernels and strict signs.
All finite-certificate premises are internal and must be proved for all7 cones
before the exported C06 theorem can use this helper.
Original mathematics and seed: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Matrix
noncomputable section
namespace NLA.PF03

def cubicScale (q : ℚ) (x : Cubic) : Cubic := fun k => q * x k
def cubicSub (x y : Cubic) : Cubic := fun k => x k - y k

theorem cubicEval_cubicScale (q : ℚ) (x : Cubic) :
    cubicEval (cubicScale q x) = (q : ℝ) * cubicEval x := by
  simp only [cubicEval, cubicScale, Rat.cast_mul]
  ring

theorem cubicEval_cubicSub (x y : Cubic) :
    cubicEval (cubicSub x y) = cubicEval x - cubicEval y := by
  simp only [cubicEval, cubicSub, Rat.cast_sub]
  ring

/-- Same association as the actual two matrix multiplications C-transpose*Q*C. -/
def seedRestrictedCubic (i : Fin 7) (a b : Fin 3) : Cubic :=
  ∑ s : Fin 7, cubicScale (seedC i s b)
    (∑ r : Fin 7, cubicScale (seedC i r a) (RawData.quadraticMatrix r s))

def alphaCubicVector : Fin 3 → Cubic :=
  ![cubicOne, ![0, 1, 0], ![0, 0, 1]]

def seedKernelCubic (i : Fin 7) (r : Fin 3) : Cubic :=
  ∑ a : Fin 3, cubicMul (RawData.restrictedGram i r a) (alphaCubicVector a)

def seedLocalDet (i : Fin 7) : Cubic :=
  cubicSub (cubicMul (RawData.restrictedGram i 0 0) (RawData.restrictedGram i 1 1))
    (cubicMul (RawData.restrictedGram i 0 1) (RawData.restrictedGram i 0 1))

def SeedLocalRationalCertificate (i : Fin 7) : Prop :=
  (∀ a b : Fin 3, a ≤ b → ∀ k : Fin 3,
    RawData.restrictedGram i a b k = seedRestrictedCubic i a b k) ∧
  (∀ r k : Fin 3, seedKernelCubic i r k = cubicZero k) ∧
  0 < cubicLower (RawData.restrictedGram i 0 0) ∧
  0 < cubicLower (seedLocalDet i) ∧ seedMinor i ≠ 0

theorem seedRestrictedCubic_eval (i : Fin 7) (a b : Fin 3) :
    cubicEval (seedRestrictedCubic i a b) = localForm i a b := by
  change cubicEval (seedRestrictedCubic i a b) =
    ∑ s : Fin 7, (∑ r : Fin 7,
      (seedC i r a : ℝ) * cubicEval (RawData.quadraticMatrix r s)) * (seedC i s b : ℝ)
  simp only [seedRestrictedCubic, cubicEval_finset_sum, cubicEval_cubicScale]
  apply Finset.sum_congr rfl
  intro s _
  exact mul_comm _ _

theorem alphaCubicVector_eval (a : Fin 3) :
    cubicEval (alphaCubicVector a) = alphaVector a := by
  fin_cases a <;> simp [alphaCubicVector, alphaVector, cubicEval, cubicOne]

theorem seedKernelCubic_eval (i : Fin 7) (r : Fin 3) :
    cubicEval (seedKernelCubic i r) = ((localCache i).mulVec alphaVector) r := by
  change cubicEval (seedKernelCubic i r) =
    ∑ a : Fin 3, cubicEval (RawData.restrictedGram i r a) * alphaVector a
  rw [seedKernelCubic, cubicEval_finset_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [cubic_eval_operations.2.2.2, alphaCubicVector_eval]

theorem seedLocalDet_eval (i : Fin 7) :
    cubicEval (seedLocalDet i) =
      localCache i 0 0 * localCache i 1 1 - (localCache i 0 1) ^ 2 := by
  unfold seedLocalDet
  rw [cubicEval_cubicSub, cubic_eval_operations.2.2.2, cubic_eval_operations.2.2.2]
  change cubicEval (RawData.restrictedGram i 0 0) *
      cubicEval (RawData.restrictedGram i 1 1) -
      cubicEval (RawData.restrictedGram i 0 1) * cubicEval (RawData.restrictedGram i 0 1) = _
  simp only [localCache, Matrix.map_apply, pow_two]

private theorem raw_local_symm (i : Fin 7) (a b : Fin 3) :
    RawData.restrictedGram i a b = RawData.restrictedGram i b a := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;> rfl

theorem localCache_isSymm (i : Fin 7) : (localCache i).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  exact congrArg cubicEval (raw_local_symm i b a)

theorem localForm_isSymm (i : Fin 7) : (localForm i).IsSymm := by
  have hQ : quadraticSeedᵀ = quadraticSeed := seed_quadratic_form.1
  change ((castMatrix (seedC i))ᵀ * quadraticSeed * castMatrix (seedC i))ᵀ =
    (castMatrix (seedC i))ᵀ * quadraticSeed * castMatrix (seedC i)
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hQ, Matrix.mul_assoc]

theorem seed_local_data_of_certificate (i : Fin 7)
    (h : SeedLocalRationalCertificate i) :
    localCache i = localForm i ∧
      (localCache i).mulVec alphaVector = 0 ∧
      0 < localCache i 0 0 ∧
      0 < localCache i 0 0 * localCache i 1 1 - (localCache i 0 1) ^ 2 ∧
      seedMinor i ≠ 0 := by
  rcases h with ⟨hupper, hkernel, h00, hdet, hminor⟩
  have hu (a b : Fin 3) (hab : a ≤ b) : localCache i a b = localForm i a b := by
    have heq : RawData.restrictedGram i a b = seedRestrictedCubic i a b :=
      funext (hupper a b hab)
    change cubicEval (RawData.restrictedGram i a b) = localForm i a b
    rw [heq, seedRestrictedCubic_eval]
  have hcache : localCache i = localForm i := by
    ext a b
    rcases le_total a b with hab | hba
    · exact hu a b hab
    · calc
        localCache i a b = localCache i b a := (localCache_isSymm i).apply b a
        _ = localForm i b a := hu b a hba
        _ = localForm i a b := (localForm_isSymm i).apply a b
  have hker : (localCache i).mulVec alphaVector = 0 := by
    ext r
    change ((localCache i).mulVec alphaVector) r = 0
    have heq : seedKernelCubic i r = cubicZero := funext (hkernel r)
    rw [← seedKernelCubic_eval, heq, cubic_eval_operations.1]
  refine ⟨hcache, hker, ?_, ?_, hminor⟩
  · exact cubicEval_pos_of_lower (RawData.restrictedGram i 0 0) h00
  · have hp := cubicEval_pos_of_lower (seedLocalDet i) hdet
    rwa [seedLocalDet_eval] at hp

#print axioms seed_local_data_of_certificate
#assert_trust kernel seed_local_data_of_certificate

end NLA.PF03
