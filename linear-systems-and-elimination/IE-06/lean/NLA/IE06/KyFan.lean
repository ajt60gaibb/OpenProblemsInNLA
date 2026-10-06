/-
Deterministic contraction-supremum Ky Fan estimates. Exact definitions and
contracts were reviewed before implementation in reviews/kyfan-contraction-specification.md.
-/
import NLA.IE06.SpectralStacking
import NLA.IE06.GaussianFrobenius

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Matrix WithLp
open scoped BigOperators Matrix.Norms.Frobenius
namespace NLA.IE06.KyFan
open Spectral

/-- Literal Frobenius norm, including empty dimensions. -/
def frobeniusNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (A i j)^2)

theorem frobeniusNorm_eq_sqrt_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A = Real.sqrt (GaussianFrobenius.frobeniusSq A) := rfl

theorem frobeniusNorm_eq_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A = ‖A‖ := by
  rw [frobeniusNorm, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]

theorem frobeniusNorm_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ frobeniusNorm A := Real.sqrt_nonneg _

theorem frobeniusNorm_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A ^ 2 = ∑ i, ∑ j, (A i j)^2 :=
  Real.sq_sqrt (by positivity)

def entries {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin m × Fin n) := toLp 2 (fun ij => A ij.1 ij.2)

theorem norm_entries {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖entries A‖ = frobeniusNorm A := by
  rw [EuclideanSpace.norm_eq, frobeniusNorm, Fintype.sum_prod_type]
  simp only [entries, Real.norm_eq_abs, sq_abs]

theorem frobeniusNorm_conjTranspose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm Aᴴ = frobeniusNorm A := by
  simpa only [frobeniusNorm_eq_norm] using Matrix.frobenius_norm_conjTranspose A

theorem opNorm_conjTranspose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    opNorm Aᴴ = opNorm A := by
  simpa only [opNorm_eq_l2] using Matrix.l2_opNorm_conjTranspose A

theorem frobeniusNorm_sq_columns {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A^2 = ∑ j, ‖(toLp 2 (fun i => A i j) : EuclideanSpace ℝ (Fin m))‖^2 := by
  simp only [frobeniusNorm_sq, EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_comm

theorem frobeniusNorm_mul_left {r m n : ℕ} (Q : Matrix (Fin r) (Fin m) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm (Q*A) ≤ opNorm Q * frobeniusNorm A := by
  have hs : frobeniusNorm (Q*A)^2 ≤ (opNorm Q * frobeniusNorm A)^2 := by
    rw [frobeniusNorm_sq_columns, mul_pow, frobeniusNorm_sq_columns, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h := (euclideanMap Q).toContinuousLinearMap.le_opNorm
      (toLp 2 (fun i => A i j))
    have he : (toLp 2 (fun i => (Q*A) i j) : EuclideanSpace ℝ (Fin r)) =
        euclideanMap Q (toLp 2 (fun i => A i j)) := by
      ext i
      rfl
    rw [he, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  exact (sq_le_sq₀ (frobeniusNorm_nonneg _) (mul_nonneg (opNorm_nonneg _) (frobeniusNorm_nonneg _))).mp hs

theorem frobeniusNorm_mul_right {r m n : ℕ} (A : Matrix (Fin r) (Fin m) ℝ)
    (M : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm (A*M) ≤ frobeniusNorm A * opNorm M := by
  have h := frobeniusNorm_mul_left Mᴴ Aᴴ
  simpa only [← Matrix.conjTranspose_mul, frobeniusNorm_conjTranspose,
    opNorm_conjTranspose, mul_comm] using h

theorem frobeniusNorm_one (m : ℕ) :
    frobeniusNorm (1 : Matrix (Fin m) (Fin m) ℝ) = Real.sqrt m := by
  simp [frobeniusNorm, Matrix.one_apply]

theorem frobeniusNorm_le_sqrt_rows_opNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A ≤ Real.sqrt m * opNorm A := by
  simpa only [Matrix.one_mul, frobeniusNorm_one] using
    frobeniusNorm_mul_right (1 : Matrix (Fin m) (Fin m) ℝ) A

/-- Values attained by actual k-row contractions on the left. -/
def contractionValues {m n : ℕ} (k : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) : Set ℝ :=
  {v | ∃ Q : Matrix (Fin k) (Fin m) ℝ, opNorm Q ≤ 1 ∧ v = frobeniusNorm (Q*A)}

def kyFan {m n : ℕ} (k : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup (contractionValues k A)

theorem contractionValues_nonempty {m n : ℕ} (k : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    (contractionValues k A).Nonempty := by
  refine ⟨0, 0, ?_, ?_⟩
  · simp [opNorm, euclideanMap]
  · simp [frobeniusNorm]

theorem contraction_frobenius_le {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix (Fin k) (Fin m) ℝ) (hQ : opNorm Q ≤ 1) :
    frobeniusNorm (Q*A) ≤ Real.sqrt k * opNorm A := by
  calc
    _ ≤ frobeniusNorm Q * opNorm A := frobeniusNorm_mul_right Q A
    _ ≤ (Real.sqrt k * opNorm Q) * opNorm A :=
      mul_le_mul_of_nonneg_right (frobeniusNorm_le_sqrt_rows_opNorm Q) (opNorm_nonneg A)
    _ ≤ (Real.sqrt k * 1) * opNorm A :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hQ (Real.sqrt_nonneg _)) (opNorm_nonneg A)
    _ = _ := by ring

theorem contractionValues_bddAbove {m n : ℕ} (k : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    BddAbove (contractionValues k A) := by
  refine ⟨Real.sqrt k * opNorm A, ?_⟩
  rintro v ⟨Q,hQ,rfl⟩
  exact contraction_frobenius_le A Q hQ

theorem contraction_le_kyFan {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix (Fin k) (Fin m) ℝ) (hQ : opNorm Q ≤ 1) :
    frobeniusNorm (Q*A) ≤ kyFan k A :=
  le_csSup (contractionValues_bddAbove k A) ⟨Q,hQ,rfl⟩

theorem kyFan_le_sqrt_mul_opNorm {m n : ℕ} (k : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    kyFan k A ≤ Real.sqrt k * opNorm A := by
  apply csSup_le (contractionValues_nonempty k A)
  rintro v ⟨Q,hQ,rfl⟩
  exact contraction_frobenius_le A Q hQ

theorem kyFan_nonneg {m n : ℕ} (k : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ kyFan k A := by
  have h := contraction_le_kyFan A (0 : Matrix (Fin k) (Fin m) ℝ)
    (by simp [opNorm, euclideanMap])
  simpa [frobeniusNorm] using h

theorem kyFan_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : kyFan 0 A = 0 := by
  have hu := kyFan_le_sqrt_mul_opNorm 0 A
  simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul] at hu
  exact le_antisymm hu (kyFan_nonneg 0 A)

theorem kyFan_le_add {m n : ℕ} (k : ℕ) (A B : Matrix (Fin m) (Fin n) ℝ) :
    kyFan k A ≤ kyFan k B + frobeniusNorm (A-B) := by
  apply csSup_le (contractionValues_nonempty k A)
  rintro v ⟨Q,hQ,rfl⟩
  have ht : frobeniusNorm (Q*A) ≤ frobeniusNorm (Q*B)+frobeniusNorm (Q*(A-B)) := by
    simp only [frobeniusNorm_eq_norm, Matrix.mul_sub]
    exact (sub_le_iff_le_add).mp (norm_sub_norm_le (Q*A) (Q*B)) |>.trans_eq (add_comm _ _)
  calc
    _ ≤ _ := ht
    _ ≤ kyFan k B + (opNorm Q * frobeniusNorm (A-B)) :=
      add_le_add (contraction_le_kyFan B Q hQ) (frobeniusNorm_mul_left Q (A-B))
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_right hQ (frobeniusNorm_nonneg (A-B))
      linarith

theorem kyFan_abs_sub_le {m n : ℕ} (k : ℕ) (A B : Matrix (Fin m) (Fin n) ℝ) :
    |kyFan k A - kyFan k B| ≤ frobeniusNorm (A-B) := by
  apply abs_le.mpr
  have h1 := kyFan_le_add k A B
  have h2 := kyFan_le_add k B A
  have he : frobeniusNorm (B-A) = frobeniusNorm (A-B) := by
    simp only [frobeniusNorm_eq_norm]
    exact norm_sub_rev B A
  rw [he] at h2
  constructor <;> linarith

theorem kyFan_mul_abs_sub_le {m n p : ℕ} (k : ℕ)
    (G H : Matrix (Fin m) (Fin n) ℝ) (M : Matrix (Fin n) (Fin p) ℝ) :
    |kyFan k (G*M) - kyFan k (H*M)| ≤ opNorm M * frobeniusNorm (G-H) := by
  have h := kyFan_abs_sub_le k (G*M) (H*M)
  rw [← Matrix.sub_mul] at h
  exact h.trans ((frobeniusNorm_mul_right (G-H) M).trans_eq (mul_comm _ _))

/-- Coordinate matrix whose rows are the given Euclidean vectors. -/
def rowMatrix {k m : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin m)) :
    Matrix (Fin k) (Fin m) ℝ := fun i j => v i j

theorem rowMatrix_apply {k m : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) (i : Fin k) :
    euclideanMap (rowMatrix v) x i = inner ℝ (v i) x := by
  simp [euclideanMap, rowMatrix, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, PiLp.inner_apply, mul_comm]

theorem rowMatrix_contraction {k m : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin m))
    (hv : Orthonormal ℝ v) : opNorm (rowMatrix v) ≤ 1 := by
  apply (euclideanMap (rowMatrix v)).toContinuousLinearMap.opNorm_le_bound zero_le_one
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖euclideanMap (rowMatrix v) x‖^2 ≤ ‖x‖^2
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [rowMatrix_apply, Real.norm_eq_abs, sq_abs] using
    (hv.sum_inner_products_le x (s := Finset.univ))

theorem rowMatrix_mul_row {k m n : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin m))
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin k) :
    (toLp 2 (fun j => (rowMatrix v*A) i j) : EuclideanSpace ℝ (Fin n)) =
      (euclideanMap A).adjoint (v i) := by
  simp only [euclideanMap, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  ext j
  simp [rowMatrix, Matrix.toLpLin_apply, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, mul_comm]

theorem frobeniusNorm_sq_rowMatrix_mul {k m n : ℕ}
    (v : Fin k → EuclideanSpace ℝ (Fin m)) (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm (rowMatrix v*A)^2 = ∑ i, ‖(euclideanMap A).adjoint (v i)‖^2 := by
  simp_rw [← rowMatrix_mul_row, EuclideanSpace.real_norm_sq_eq]
  exact frobeniusNorm_sq _

theorem adjoint_leftSingularVector {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin (Fintype.card (Fin n))) (hi : A.singularValues i ≠ 0) :
    (euclideanMap A).adjoint (A.leftSingularVector i) =
      (A.singularValues i) • A.rightSingularVectorBasis i := by
  simp only [Matrix.leftSingularVector, map_smul, euclideanMap]
  have h : (LinearMap.adjoint (Matrix.toEuclideanLin A) ∘ₗ Matrix.toEuclideanLin A)
      (A.rightSingularVectorBasis i) =
      (A.singularValues i)^2 • A.rightSingularVectorBasis i := by
    simpa using A.adjoint_comp_self_apply_rightSingularVectorBasis i
  change (A.singularValues i)⁻¹ •
    ((LinearMap.adjoint (Matrix.toEuclideanLin A) ∘ₗ Matrix.toEuclideanLin A)
      (A.rightSingularVectorBasis i)) = _
  rw [h, smul_smul]
  congr 1
  field_simp

theorem sqrt_mul_singularValue_le_kyFan {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hk : 1 ≤ k) (_hkm : k ≤ m) (hkn : k ≤ n) :
    Real.sqrt k * singularValue A (k-1) ≤ kyFan k A := by
  by_cases hs : singularValue A (k-1) = 0
  · simpa only [hs, mul_zero] using kyFan_nonneg k A
  have hspos : 0 < singularValue A (k-1) :=
    lt_of_le_of_ne (singularValue_nonneg _ _) (Ne.symm hs)
  let f : Fin k → Fin (Fintype.card (Fin n)) := Fin.castLE (by simpa using hkn)
  have hpos (i : Fin k) : 0 < A.singularValues (f i) := by
    apply hspos.trans_le
    apply (singularValue_antitone A)
    change i.val ≤ k-1
    omega
  let v : Fin k → EuclideanSpace ℝ (Fin m) := fun i => A.leftSingularVector (f i)
  have hv : Orthonormal ℝ v := by
    let g : Fin k → {i : Fin (Fintype.card (Fin n)) // A.singularValues i ≠ 0} :=
      fun i => ⟨f i, ne_of_gt (hpos i)⟩
    have hg : Function.Injective g := by
      intro i j hij
      exact Fin.ext (congrArg (fun z => z.val.val) hij)
    exact (A.orthonormal_leftSingularVector_of_singularValues_ne_zero.comp g hg)
  have hQ := rowMatrix_contraction v hv
  have hrow (i : Fin k) : ‖(euclideanMap A).adjoint (v i)‖ = A.singularValues (f i) := by
    rw [show v i = A.leftSingularVector (f i) from rfl,
      adjoint_leftSingularVector A (f i) (ne_of_gt (hpos i)), norm_smul,
      A.rightSingularVectorBasis.norm_eq_one, mul_one, Real.norm_eq_abs,
      abs_of_pos (hpos i)]
  have hl : (Real.sqrt k * singularValue A (k-1))^2 ≤ frobeniusNorm (rowMatrix v*A)^2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg k), frobeniusNorm_sq_rowMatrix_mul]
    calc
      (k:ℝ)*singularValue A (k-1)^2 = ∑ _i : Fin k, singularValue A (k-1)^2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        rw [hrow]
        apply pow_le_pow_left₀ (singularValue_nonneg _ _)
        apply singularValue_antitone A
        change i.val ≤ k-1
        omega
  have he := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (singularValue_nonneg _ _))
    (frobeniusNorm_nonneg _)).mp hl
  exact he.trans (contraction_le_kyFan A (rowMatrix v) hQ)

/-- Matrix of the actual flattened Euclidean entries. -/
def matrixOfEntries {m n : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin n)) :
    Matrix (Fin m) (Fin n) ℝ := fun i j => x (i,j)

theorem frobeniusNorm_matrixOfEntries_sub {m n : ℕ}
    (x y : EuclideanSpace ℝ (Fin m × Fin n)) :
    frobeniusNorm (matrixOfEntries x - matrixOfEntries y) = ‖x-y‖ := by
  rw [← norm_entries]
  rfl

theorem kyFan_lipschitz {m n : ℕ} (k : ℕ) :
    LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin m × Fin n) =>
      kyFan k (matrixOfEntries x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul]
  have h := kyFan_abs_sub_le k (matrixOfEntries x) (matrixOfEntries y)
  rwa [frobeniusNorm_matrixOfEntries_sub] at h

theorem kyFan_mul_lipschitz {m n p : ℕ} (k : ℕ) (M : Matrix (Fin n) (Fin p) ℝ) :
    LipschitzWith ⟨opNorm M, opNorm_nonneg M⟩
      (fun x : EuclideanSpace ℝ (Fin m × Fin n) => kyFan k (matrixOfEntries x*M)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, Real.norm_eq_abs]
  have h := kyFan_mul_abs_sub_le k (matrixOfEntries x) (matrixOfEntries y) M
  rwa [frobeniusNorm_matrixOfEntries_sub] at h

theorem opNorm_le_frobeniusNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    opNorm A ≤ frobeniusNorm A := by
  apply (euclideanMap A).toContinuousLinearMap.opNorm_le_bound (frobeniusNorm_nonneg A)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (frobeniusNorm_nonneg _) (norm_nonneg _))).mp
  change ‖euclideanMap A x‖^2 ≤ (frobeniusNorm A * ‖x‖)^2
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow, frobeniusNorm_sq, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  let v : EuclideanSpace ℝ (Fin n) := toLp 2 (fun j => A i j)
  have he : euclideanMap A x i = inner ℝ v x := rowMatrix_apply (fun i => toLp 2 (fun j => A i j)) x i
  rw [he]
  have h := pow_le_pow_left₀ (norm_nonneg (inner ℝ v x)) (norm_inner_le_norm v x) 2
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow, EuclideanSpace.real_norm_sq_eq, v] using h

theorem opNorm_abs_sub_le_frobeniusNorm {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    |opNorm A - opNorm B| ≤ frobeniusNorm (A-B) := by
  have h := abs_norm_sub_norm_le (euclideanMap A).toContinuousLinearMap
    (euclideanMap B).toContinuousLinearMap
  have he : (euclideanMap A).toContinuousLinearMap - (euclideanMap B).toContinuousLinearMap =
      (euclideanMap (A-B)).toContinuousLinearMap := by
    exact (map_sub ((Matrix.toEuclideanLin (𝕜 := ℝ)).trans
      LinearMap.toContinuousLinearMap) A B).symm
  rw [he] at h
  exact h.trans (opNorm_le_frobeniusNorm (A-B))

theorem opNorm_mul_lipschitz {m n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ) :
    LipschitzWith ⟨opNorm M, opNorm_nonneg M⟩
      (fun x : EuclideanSpace ℝ (Fin m × Fin n) => opNorm (matrixOfEntries x*M)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, Real.norm_eq_abs]
  have h := opNorm_abs_sub_le_frobeniusNorm (matrixOfEntries x*M) (matrixOfEntries y*M)
  rw [← Matrix.sub_mul] at h
  have h2 := h.trans (frobeniusNorm_mul_right (matrixOfEntries x-matrixOfEntries y) M)
  rwa [frobeniusNorm_matrixOfEntries_sub, mul_comm] at h2

end NLA.IE06.KyFan

#assert_trust kernel NLA.IE06.KyFan.frobeniusNorm
#print axioms NLA.IE06.KyFan.frobeniusNorm
#assert_trust kernel NLA.IE06.KyFan.frobeniusNorm_eq_sqrt_sq
#print axioms NLA.IE06.KyFan.frobeniusNorm_eq_sqrt_sq
#assert_trust kernel NLA.IE06.KyFan.frobeniusNorm_eq_norm
#print axioms NLA.IE06.KyFan.frobeniusNorm_eq_norm
#assert_trust kernel NLA.IE06.KyFan.frobeniusNorm_nonneg
#print axioms NLA.IE06.KyFan.frobeniusNorm_nonneg
#assert_trust kernel NLA.IE06.KyFan.frobeniusNorm_sq
#print axioms NLA.IE06.KyFan.frobeniusNorm_sq
#assert_trust kernel NLA.IE06.KyFan.entries
#print axioms NLA.IE06.KyFan.entries
#assert_trust kernel NLA.IE06.KyFan.norm_entries
#print axioms NLA.IE06.KyFan.norm_entries
#assert_trust kernel NLA.IE06.KyFan.frobeniusNorm_conjTranspose
#print axioms NLA.IE06.KyFan.frobeniusNorm_conjTranspose
#assert_trust kernel NLA.IE06.KyFan.opNorm_conjTranspose
#print axioms NLA.IE06.KyFan.opNorm_conjTranspose
#assert_trust kernel NLA.IE06.KyFan.frobeniusNorm_sq_columns
#print axioms NLA.IE06.KyFan.frobeniusNorm_sq_columns
#assert_trust kernel NLA.IE06.KyFan.frobeniusNorm_mul_left
#print axioms NLA.IE06.KyFan.frobeniusNorm_mul_left
#assert_trust kernel NLA.IE06.KyFan.frobeniusNorm_mul_right
#print axioms NLA.IE06.KyFan.frobeniusNorm_mul_right
#assert_trust kernel NLA.IE06.KyFan.frobeniusNorm_one
#print axioms NLA.IE06.KyFan.frobeniusNorm_one
#assert_trust kernel NLA.IE06.KyFan.frobeniusNorm_le_sqrt_rows_opNorm
#print axioms NLA.IE06.KyFan.frobeniusNorm_le_sqrt_rows_opNorm
#assert_trust kernel NLA.IE06.KyFan.contractionValues
#print axioms NLA.IE06.KyFan.contractionValues
#assert_trust kernel NLA.IE06.KyFan.kyFan
#print axioms NLA.IE06.KyFan.kyFan
#assert_trust kernel NLA.IE06.KyFan.contractionValues_nonempty
#print axioms NLA.IE06.KyFan.contractionValues_nonempty
#assert_trust kernel NLA.IE06.KyFan.contraction_frobenius_le
#print axioms NLA.IE06.KyFan.contraction_frobenius_le
#assert_trust kernel NLA.IE06.KyFan.contractionValues_bddAbove
#print axioms NLA.IE06.KyFan.contractionValues_bddAbove
#assert_trust kernel NLA.IE06.KyFan.contraction_le_kyFan
#print axioms NLA.IE06.KyFan.contraction_le_kyFan
#assert_trust kernel NLA.IE06.KyFan.kyFan_le_sqrt_mul_opNorm
#print axioms NLA.IE06.KyFan.kyFan_le_sqrt_mul_opNorm
#assert_trust kernel NLA.IE06.KyFan.kyFan_nonneg
#print axioms NLA.IE06.KyFan.kyFan_nonneg
#assert_trust kernel NLA.IE06.KyFan.kyFan_zero
#print axioms NLA.IE06.KyFan.kyFan_zero
#assert_trust kernel NLA.IE06.KyFan.kyFan_le_add
#print axioms NLA.IE06.KyFan.kyFan_le_add
#assert_trust kernel NLA.IE06.KyFan.kyFan_abs_sub_le
#print axioms NLA.IE06.KyFan.kyFan_abs_sub_le
#assert_trust kernel NLA.IE06.KyFan.kyFan_mul_abs_sub_le
#print axioms NLA.IE06.KyFan.kyFan_mul_abs_sub_le
#assert_trust kernel NLA.IE06.KyFan.rowMatrix
#print axioms NLA.IE06.KyFan.rowMatrix
#assert_trust kernel NLA.IE06.KyFan.rowMatrix_apply
#print axioms NLA.IE06.KyFan.rowMatrix_apply
#assert_trust kernel NLA.IE06.KyFan.rowMatrix_contraction
#print axioms NLA.IE06.KyFan.rowMatrix_contraction
#assert_trust kernel NLA.IE06.KyFan.rowMatrix_mul_row
#print axioms NLA.IE06.KyFan.rowMatrix_mul_row
#assert_trust kernel NLA.IE06.KyFan.frobeniusNorm_sq_rowMatrix_mul
#print axioms NLA.IE06.KyFan.frobeniusNorm_sq_rowMatrix_mul
#assert_trust kernel NLA.IE06.KyFan.adjoint_leftSingularVector
#print axioms NLA.IE06.KyFan.adjoint_leftSingularVector
#assert_trust kernel NLA.IE06.KyFan.sqrt_mul_singularValue_le_kyFan
#print axioms NLA.IE06.KyFan.sqrt_mul_singularValue_le_kyFan
#assert_trust kernel NLA.IE06.KyFan.matrixOfEntries
#print axioms NLA.IE06.KyFan.matrixOfEntries
#assert_trust kernel NLA.IE06.KyFan.frobeniusNorm_matrixOfEntries_sub
#print axioms NLA.IE06.KyFan.frobeniusNorm_matrixOfEntries_sub
#assert_trust kernel NLA.IE06.KyFan.kyFan_lipschitz
#print axioms NLA.IE06.KyFan.kyFan_lipschitz
#assert_trust kernel NLA.IE06.KyFan.kyFan_mul_lipschitz
#print axioms NLA.IE06.KyFan.kyFan_mul_lipschitz
#assert_trust kernel NLA.IE06.KyFan.opNorm_le_frobeniusNorm
#print axioms NLA.IE06.KyFan.opNorm_le_frobeniusNorm
#assert_trust kernel NLA.IE06.KyFan.opNorm_abs_sub_le_frobeniusNorm
#print axioms NLA.IE06.KyFan.opNorm_abs_sub_le_frobeniusNorm
#assert_trust kernel NLA.IE06.KyFan.opNorm_mul_lipschitz
#print axioms NLA.IE06.KyFan.opNorm_mul_lipschitz
