/-
Exact deterministic truncated inverse. The mathematical contract was reviewed
before implementation in reviews/truncated-inverse-preimplementation-review.md.
-/
import NLA.IE06.KyFan

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Matrix Module WithLp
open scoped BigOperators Matrix.Norms.Frobenius
namespace NLA.IE06.TruncatedInverse
open Spectral KyFan

/-- Retained squared reciprocal singular values, zero for an empty retained set. -/
def sigmaInvSum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) : ℝ :=
  ∑ i : Fin (n-r), (singularValue M i)⁻¹ ^ 2

theorem sigmaInvSum_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    0 ≤ sigmaInvSum M r := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem sigmaInvSum_eq_zero_of_le {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (h : n ≤ r) : sigmaInvSum M r = 0 := by
  have : IsEmpty (Fin (n-r)) := ⟨fun i => by have := i.isLt; omega⟩
  simp [sigmaInvSum]

theorem retained_singularValue_ge {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (_hr : r < n) {μ : ℝ} (h : μ ≤ singularValue M (n-r-1))
    (i : Fin (n-r)) : μ ≤ singularValue M i := by
  apply h.trans
  apply singularValue_antitone M
  change i.val ≤ n-r-1
  omega

theorem retained_singularValue_pos {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hr : r < n) {μ : ℝ} (hμ : 0 < μ) (h : μ ≤ singularValue M (n-r-1))
    (i : Fin (n-r)) : 0 < singularValue M i :=
  hμ.trans_le (retained_singularValue_ge M hr h i)

/-- Frobenius energy computed on any genuine orthonormal input basis. -/
theorem frobeniusNorm_sq_eq_sum_basis {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    frobeniusNorm A^2 = ∑ j, ‖euclideanMap A (b j)‖^2 := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [Finset.sum_comm]
  rw [frobeniusNorm_sq]
  apply Finset.sum_congr rfl
  intro i _
  let v : EuclideanSpace ℝ (Fin n) := toLp 2 (fun j => A i j)
  have he (j : Fin n) : euclideanMap A (b j) i = inner ℝ v (b j) :=
    rowMatrix_apply (fun i => toLp 2 (fun j => A i j)) (b j) i
  simp_rw [he]
  have h := b.sum_sq_norm_inner_left v
  simpa only [Real.norm_eq_abs, sq_abs, EuclideanSpace.real_norm_sq_eq, v] using h.symm

theorem euclideanMap_injective_of_det_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.det ≠ 0) : Function.Injective (euclideanMap M) := by
  intro x y hxy
  apply (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).injective
  exact Matrix.mulVec_injective_of_det_ne_zero hM (congrArg WithLp.ofLp hxy)

theorem singularValues_pos_of_det_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.det ≠ 0) (i : Fin n) : 0 < singularValue M i := by
  exact (M.injective_toEuclideanLin_iff_singularValues_pos.mp
    (euclideanMap_injective_of_det_ne_zero M hM)) i (by simp)

/-- Fin-n indexing of the original left singular vectors. -/
def leftVectors {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Fin n → EuclideanSpace ℝ (Fin n) :=
  fun i => M.leftSingularVector ⟨i.val, by simp⟩

theorem leftVectors_orthonormal {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.det ≠ 0) : Orthonormal ℝ (leftVectors M) := by
  let f : Fin n → {i : Fin (Fintype.card (Fin n)) // M.singularValues i ≠ 0} :=
    fun i => ⟨⟨i.val, by simp⟩,
      ne_of_gt (singularValues_pos_of_det_ne_zero M hM i)⟩
  exact M.orthonormal_leftSingularVector_of_singularValues_ne_zero.comp f
    (fun i j h => Fin.ext (congrArg (fun z => z.val.val) h))

def leftBasis {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.det ≠ 0) :
    OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  OrthonormalBasis.mk (leftVectors_orthonormal M hM)
    ((leftVectors_orthonormal M hM).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simp)).ge

theorem leftBasis_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.det ≠ 0)
    (i : Fin n) : leftBasis M hM i = leftVectors M i := by
  simp [leftBasis]

theorem inverse_apply_leftBasis {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.det ≠ 0) (i : Fin n) :
    euclideanMap M⁻¹ (leftBasis M hM i) = (singularValue M i)⁻¹ •
      M.rightSingularVectorBasis ⟨i.val, by simp⟩ := by
  have hid : (euclideanMap M⁻¹).comp (euclideanMap M) = LinearMap.id := by
    simpa only [euclideanMap, Matrix.toLpLin_mul_same, Matrix.toLpLin_one] using
      congrArg Matrix.toEuclideanLin (Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM))
  rw [leftBasis_apply]
  simp only [leftVectors, Matrix.leftSingularVector, map_smul]
  have hx := congrArg (fun f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) =>
    f (M.rightSingularVectorBasis ⟨i.val, by simp⟩)) hid
  rw [show euclideanMap M⁻¹ (Matrix.toEuclideanLin M
    (M.rightSingularVectorBasis ⟨i.val, by simp⟩)) =
    M.rightSingularVectorBasis ⟨i.val, by simp⟩ from hx]
  rfl

theorem exists_retained_leftBasis {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hr : r < n) {μ : ℝ} (hμ : 0 < μ) (hs : μ ≤ singularValue M (n-r-1)) :
    ∃ b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      ∀ i : Fin n, i.val < n-r → b i = leftVectors M i := by
  let s : Set (Fin n) := {i | i.val < n-r}
  let f : s → {i : Fin (Fintype.card (Fin n)) // M.singularValues i ≠ 0} :=
    fun i => ⟨⟨i.val.val, by simp⟩,
      ne_of_gt (retained_singularValue_pos M hr hμ hs ⟨i.val.val,i.property⟩)⟩
  have hon : Orthonormal ℝ (s.domRestrict (leftVectors M)) :=
    M.orthonormal_leftSingularVector_of_singularValues_ne_zero.comp f
      (fun i j h => Subtype.ext (Fin.ext (congrArg (fun z => z.val.val) h)))
  exact hon.exists_orthonormalBasis_extension_of_card_eq (by simp)

def rightVectors {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Fin n → EuclideanSpace ℝ (Fin n) :=
  fun i => M.rightSingularVectorBasis ⟨i.val,by simp⟩

theorem rightVectors_orthonormal {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Orthonormal ℝ (rightVectors M) :=
  M.rightSingularVectorBasis.orthonormal.comp
    (fun i : Fin n => (⟨i.val,by simp⟩ : Fin (Fintype.card (Fin n))))
    (fun i j h => Fin.ext (congrArg (fun z : Fin (Fintype.card (Fin n)) => z.val) h))

/-- The actual linear inverse-SVD sum on the retained input basis vectors. -/
def retainedMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (r : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.toEuclideanLin.symm (b.toBasis.constr ℝ
    (fun i => if i.val < n-r then (singularValue M i)⁻¹ • rightVectors M i else 0))

theorem retainedMatrix_apply_basis {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (r : ℕ) (i : Fin n) :
    euclideanMap (retainedMatrix M b r) (b i) =
      if i.val < n-r then (singularValue M i)⁻¹ • rightVectors M i else 0 := by
  simp only [retainedMatrix, euclideanMap, LinearEquiv.apply_symm_apply]
  exact b.toBasis.constr_basis ℝ _ i

theorem sum_fin_ite_lt {n m : ℕ} (h : m ≤ n) (f : Fin n → ℝ) :
    (∑ i : Fin n, if i.val < m then f i else 0) =
      ∑ i : Fin m, f (Fin.castLE h i) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun i hi => (⟨i.val,(Finset.mem_filter.mp hi).2⟩ : Fin m))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro i hi j hj he
    exact Fin.ext (congrArg (fun z : Fin m => z.val) he)
  · intro j _
    refine ⟨Fin.castLE h j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,j.isLt⟩,rfl⟩
  · intro i hi
    rfl

theorem retainedMatrix_frobenius_sq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (r : ℕ) :
    frobeniusNorm (retainedMatrix M b r)^2 = sigmaInvSum M r := by
  rw [frobeniusNorm_sq_eq_sum_basis _ b]
  simp_rw [retainedMatrix_apply_basis]
  have he (i : Fin n) :
      ‖if i.val < n-r then (singularValue M i)⁻¹ • rightVectors M i else 0‖^2 =
      if i.val < n-r then (singularValue M i)⁻¹^2 else 0 := by
    split_ifs <;> simp [rightVectors, norm_smul, Real.norm_eq_abs, sq_abs]
  simp_rw [he]
  rw [sum_fin_ite_lt (Nat.sub_le n r)]
  rfl

def badIndex {n r : ℕ} (hr : r ≤ n) (i : Fin r) : Fin n :=
  ⟨n-r+i.val,by omega⟩

theorem badIndex_injective {n r : ℕ} (hr : r ≤ n) : Function.Injective (badIndex hr) := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  dsimp [badIndex] at hval
  omega

def badColumns {n r : ℕ} (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hr : r ≤ n) : Matrix (Fin n) (Fin r) ℝ := fun i j => b (badIndex hr j) i

theorem badColumns_conjTranspose {n r : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (hr : r ≤ n) :
    (badColumns b hr)ᴴ = rowMatrix (fun i => b (badIndex hr i)) := by
  ext i j
  simp [badColumns,rowMatrix,Matrix.conjTranspose_apply]

theorem badColumns_orthonormal {n r : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (hr : r ≤ n) :
    (badColumns b hr)ᴴ * badColumns b hr = 1 := by
  ext i j
  have he : ((badColumns b hr)ᴴ * badColumns b hr) i j =
      inner ℝ (b (badIndex hr i)) (b (badIndex hr j)) := by
    simp [badColumns,Matrix.mul_apply,PiLp.inner_apply,mul_comm]
  rw [he,b.inner_eq_ite]
  simp [Matrix.one_apply,(badIndex_injective hr).eq_iff]

theorem badColumns_apply {n r : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (hr : r ≤ n)
    (x : EuclideanSpace ℝ (Fin r)) :
    euclideanMap (badColumns b hr) x = ∑ j, x j • b (badIndex hr j) := by
  ext i
  simp [euclideanMap,badColumns,Matrix.toLpLin_apply,Matrix.mulVec,dotProduct,mul_comm]

theorem badProjection_apply_basis {n r : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (hr : r ≤ n) (i : Fin n) :
    euclideanMap (badColumns b hr * (badColumns b hr)ᴴ) (b i) =
      if i.val < n-r then 0 else b i := by
  have he : euclideanMap (badColumns b hr * (badColumns b hr)ᴴ) (b i) =
      ∑ j, (if badIndex hr j = i then (1:ℝ) else 0) • b (badIndex hr j) := by
    rw [show euclideanMap (badColumns b hr * (badColumns b hr)ᴴ) =
        (euclideanMap (badColumns b hr)).comp (euclideanMap (badColumns b hr)ᴴ) from
      Matrix.toLpLin_mul_same _ _ _, LinearMap.comp_apply, badColumns_apply]
    simp only [badColumns_conjTranspose,rowMatrix_apply,b.inner_eq_ite]
  rw [he]
  by_cases hi : i.val < n-r
  · rw [if_pos hi]
    apply Finset.sum_eq_zero
    intro j _
    have hne : badIndex hr j ≠ i := by
      intro h
      have he := congrArg Fin.val h
      dsimp [badIndex] at he
      omega
    simp [hne]
  · rw [if_neg hi]
    let j : Fin r := ⟨i.val-(n-r),by omega⟩
    have hj : badIndex hr j=i := by apply Fin.ext; dsimp [badIndex,j]; omega
    rw [← hj]
    simp [(badIndex_injective hr).eq_iff]

/-- Exact action of the retained inverse on arbitrary input coordinates. -/
theorem retainedMatrix_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanMap (retainedMatrix M b r) x =
      ∑ i, (if i.val < n-r then b.repr x i * (singularValue M i)⁻¹ else 0) •
        rightVectors M i := by
  conv_lhs => rw [← b.sum_repr x, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,retainedMatrix_apply_basis]
  split_ifs <;> simp [smul_smul]

theorem retainedMatrix_opNorm_le {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hr : r < n) {μ : ℝ} (hμ : 0 < μ) (hs : μ ≤ singularValue M (n-r-1)) :
    opNorm (retainedMatrix M b r) ≤ μ⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hμ.le)
  intro x
  change ‖euclideanMap (retainedMatrix M b r) x‖ ≤ μ⁻¹ * ‖x‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr hμ.le) (norm_nonneg _))).mp
  rw [retainedMatrix_apply]
  let c : Fin n → ℝ := fun i =>
    if i.val < n-r then b.repr x i * (singularValue M i)⁻¹ else 0
  have he : ‖∑ i, c i • rightVectors M i‖^2 = ∑ i, (c i)^2 := by
    simpa only [real_inner_self_eq_norm_sq,starRingEnd_apply,star_trivial,pow_two] using
      (rightVectors_orthonormal M).inner_sum c c Finset.univ
  change ‖∑ i, c i • rightVectors M i‖^2 ≤ (μ⁻¹ * ‖x‖)^2
  rw [he,mul_pow]
  have hp : ∑ i, (b.repr x i)^2 = ‖x‖^2 := by
    rw [← EuclideanSpace.real_norm_sq_eq,b.repr.norm_map]
  rw [← hp,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  dsimp [c]
  split_ifs with hi
  · have hge := retained_singularValue_ge M hr hs ⟨i.val,hi⟩
    have hinv : (singularValue M i)⁻¹ ≤ μ⁻¹ := inv_anti₀ hμ hge
    have hi0 : 0 ≤ (singularValue M i)⁻¹ := inv_nonneg.mpr (singularValue_nonneg M i)
    rw [mul_pow,mul_comm (μ⁻¹^2)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hi0 hinv 2) (sq_nonneg _)
  · simpa only [zero_pow (by decide : 2 ≠ 0)] using
      mul_nonneg (sq_nonneg (μ⁻¹)) (sq_nonneg (b.repr x i))

theorem mul_retainedMatrix {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hr : r < n) {μ : ℝ} (hμ : 0 < μ) (hs : μ ≤ singularValue M (n-r-1))
    (hb : ∀ i : Fin n, i.val < n-r → b i = leftVectors M i) :
    M * retainedMatrix M b r = 1 - badColumns b hr.le * (badColumns b hr.le)ᴴ := by
  apply Matrix.toEuclideanLin.injective
  apply b.toBasis.ext
  intro i
  change euclideanMap (M * retainedMatrix M b r) (b i) =
    euclideanMap (1 - badColumns b hr.le * (badColumns b hr.le)ᴴ) (b i)
  rw [show euclideanMap (M * retainedMatrix M b r) =
      (euclideanMap M).comp (euclideanMap (retainedMatrix M b r)) from
    Matrix.toLpLin_mul_same _ _ _,LinearMap.comp_apply,retainedMatrix_apply_basis]
  have rhs : euclideanMap (1 - badColumns b hr.le * (badColumns b hr.le)ᴴ) (b i) =
      b i - (if i.val < n-r then 0 else b i) := by
    rw [show euclideanMap (1 - badColumns b hr.le * (badColumns b hr.le)ᴴ) =
      euclideanMap (1 : Matrix (Fin n) (Fin n) ℝ) -
        euclideanMap (badColumns b hr.le * (badColumns b hr.le)ᴴ) from
      by simp only [euclideanMap,map_sub],LinearMap.sub_apply,badProjection_apply_basis]
    simp [euclideanMap]
  rw [rhs]
  by_cases hi : i.val < n-r
  · simp only [hi,if_true,sub_zero,map_smul]
    have hpos := retained_singularValue_pos M hr hμ hs ⟨i.val,hi⟩
    have hact : euclideanMap M (rightVectors M i) =
        singularValue M i • leftVectors M i :=
      M.apply_rightSingularVectorBasis_eq_smul_leftSingularVector (ne_of_gt hpos)
    rw [hact,smul_smul,inv_mul_cancel₀ (ne_of_gt hpos),one_smul,hb i hi]
  · simp [hi]

theorem retainedMatrix_mul_badColumns {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (hr : r ≤ n) :
    retainedMatrix M b r * badColumns b hr = 0 := by
  ext i j
  change (euclideanMap (retainedMatrix M b r) (b (badIndex hr j))) i = 0
  rw [retainedMatrix_apply_basis]
  have hi : ¬ (badIndex hr j).val < n-r := by dsimp [badIndex]; omega
  simp [hi]

/-- Retained inverse and discarded left orthonormal columns, valid also for singular M. -/
theorem exists_retained_decomposition {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hr : r < n) {μ : ℝ} (hμ : 0 < μ) (hs : μ ≤ singularValue M (n-r-1)) :
    ∃ R : Matrix (Fin n) (Fin n) ℝ, ∃ U : Matrix (Fin n) (Fin r) ℝ,
      Uᴴ * U = 1 ∧ M * R = 1 - U * Uᴴ ∧ R * U = 0 ∧
      frobeniusNorm R^2 = sigmaInvSum M r ∧ opNorm R ≤ μ⁻¹ := by
  obtain ⟨b,hb⟩ := exists_retained_leftBasis M hr hμ hs
  exact ⟨retainedMatrix M b r,badColumns b hr.le,badColumns_orthonormal b hr.le,
    mul_retainedMatrix M b hr hμ hs hb,retainedMatrix_mul_badColumns M b hr.le,
    retainedMatrix_frobenius_sq M b r,retainedMatrix_opNorm_le M b hr hμ hs⟩

/-- Actual inverse decomposition: a retained inverse and exactly r orthonormal discarded
left directions. No measurable random singular-vector choice is asserted. -/
theorem exists_inverse_decomposition {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.det ≠ 0) (hr : r < n) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ,
      ∃ H V : Matrix (Fin n) (Fin r) ℝ,
        Vᴴ * V = 1 ∧ H = M⁻¹ * V ∧ M⁻¹ = Z + H * Vᴴ ∧
        frobeniusNorm Z^2 = sigmaInvSum M r ∧ opNorm Z^2 ≤ sigmaInvSum M r := by
  have hpos : 0 < singularValue M (n-r-1) :=
    singularValues_pos_of_det_ne_zero M hM ⟨n-r-1,by omega⟩
  obtain ⟨Z,V,hV,hMZ,_,hF,hZ⟩ := exists_retained_decomposition M hr hpos le_rfl
  refine ⟨Z,M⁻¹ * V,V,hV,rfl,?_,hF,?_⟩
  · have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => M⁻¹ * A) hMZ
    rw [← Matrix.mul_assoc,Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mul,Matrix.mul_sub,Matrix.mul_one,← Matrix.mul_assoc] at he
    exact sub_eq_iff_eq_add.mp he.symm
  · rw [← hF]
    exact pow_le_pow_left₀ (opNorm_nonneg _) (opNorm_le_frobeniusNorm Z) 2

/- Every declaration in this module is checked under the kernel trust policy. -/
#assert_trust kernel sigmaInvSum
#print axioms sigmaInvSum
#assert_trust kernel sigmaInvSum_nonneg
#print axioms sigmaInvSum_nonneg
#assert_trust kernel sigmaInvSum_eq_zero_of_le
#print axioms sigmaInvSum_eq_zero_of_le
#assert_trust kernel retained_singularValue_ge
#print axioms retained_singularValue_ge
#assert_trust kernel retained_singularValue_pos
#print axioms retained_singularValue_pos
#assert_trust kernel frobeniusNorm_sq_eq_sum_basis
#print axioms frobeniusNorm_sq_eq_sum_basis
#assert_trust kernel euclideanMap_injective_of_det_ne_zero
#print axioms euclideanMap_injective_of_det_ne_zero
#assert_trust kernel singularValues_pos_of_det_ne_zero
#print axioms singularValues_pos_of_det_ne_zero
#assert_trust kernel leftVectors
#print axioms leftVectors
#assert_trust kernel leftVectors_orthonormal
#print axioms leftVectors_orthonormal
#assert_trust kernel leftBasis
#print axioms leftBasis
#assert_trust kernel leftBasis_apply
#print axioms leftBasis_apply
#assert_trust kernel inverse_apply_leftBasis
#print axioms inverse_apply_leftBasis
#assert_trust kernel exists_retained_leftBasis
#print axioms exists_retained_leftBasis
#assert_trust kernel rightVectors
#print axioms rightVectors
#assert_trust kernel rightVectors_orthonormal
#print axioms rightVectors_orthonormal
#assert_trust kernel retainedMatrix
#print axioms retainedMatrix
#assert_trust kernel retainedMatrix_apply_basis
#print axioms retainedMatrix_apply_basis
#assert_trust kernel sum_fin_ite_lt
#print axioms sum_fin_ite_lt
#assert_trust kernel retainedMatrix_frobenius_sq
#print axioms retainedMatrix_frobenius_sq
#assert_trust kernel badIndex
#print axioms badIndex
#assert_trust kernel badIndex_injective
#print axioms badIndex_injective
#assert_trust kernel badColumns
#print axioms badColumns
#assert_trust kernel badColumns_conjTranspose
#print axioms badColumns_conjTranspose
#assert_trust kernel badColumns_orthonormal
#print axioms badColumns_orthonormal
#assert_trust kernel badColumns_apply
#print axioms badColumns_apply
#assert_trust kernel badProjection_apply_basis
#print axioms badProjection_apply_basis
#assert_trust kernel retainedMatrix_apply
#print axioms retainedMatrix_apply
#assert_trust kernel retainedMatrix_opNorm_le
#print axioms retainedMatrix_opNorm_le
#assert_trust kernel mul_retainedMatrix
#print axioms mul_retainedMatrix
#assert_trust kernel retainedMatrix_mul_badColumns
#print axioms retainedMatrix_mul_badColumns
#assert_trust kernel exists_retained_decomposition
#print axioms exists_retained_decomposition
#assert_trust kernel exists_inverse_decomposition
#print axioms exists_inverse_decomposition

end NLA.IE06.TruncatedInverse
