import NLA.Proofs.IE22.EnergyBounds
import NLA.Proofs.IE22.GaussianBasics
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Trace

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.IE22

/-- Frobenius square is an actual matrix trace, with the coordinate sums explicit. -/
theorem matrix_entry_square_sum {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) :
    ∑ i, ∑ j, B i j ^ 2 = Matrix.trace (B.transpose * B) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    pow_two]
  exact Finset.sum_comm

/-- An exact diagonal retained covariance bounds the L1 Gram sum. -/
theorem gram_abs_sum_le_of_diagonal {m d r : ℕ}
    (B : Matrix (Fin m) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hdiag : B.transpose * B = Matrix.diagonal lam)
    (hnonneg : ∀ j, 0 ≤ lam j)
    (hcap : ∀ j, lam j ≤ (m : ℝ)/(r+1 : ℕ))
    (htrace : ∑ j, lam j ≤ (m : ℝ)) :
    (∑ i, ∑ j, |(B * B.transpose) i j|) ≤ (m : ℝ)^2/Real.sqrt (r+1 : ℕ) := by
  let G := B * B.transpose
  have hG : G.transpose = G := by simp [G, Matrix.transpose_mul]
  have hsq : ∑ i, ∑ j, G i j ^ 2 = ∑ j, (lam j)^2 := by
    rw [matrix_entry_square_sum, hG]
    have hcycle : Matrix.trace ((B*B.transpose)*(B*B.transpose)) =
        Matrix.trace ((B.transpose*B)*(B.transpose*B)) := by
      calc
        _ = Matrix.trace (B * (B.transpose * B * B.transpose)) := by
          congr 1; simp only [Matrix.mul_assoc]
        _ = Matrix.trace ((B.transpose * B * B.transpose) * B) := Matrix.trace_mul_comm _ _
        _ = _ := by congr 1; simp only [Matrix.mul_assoc]
    change Matrix.trace ((B*B.transpose)*(B*B.transpose)) = _
    rw [hcycle, hdiag]
    simp [Matrix.diagonal_mul_diagonal, pow_two]
  have hD : (0 : ℝ) < (r+1 : ℕ) := by positivity
  have hsum : ∑ j, (lam j)^2 ≤ (m : ℝ)^2/(r+1 : ℕ) := by
    calc
      _ ≤ ∑ j, ((m : ℝ)/(r+1 : ℕ)) * lam j := by
        apply Finset.sum_le_sum
        intro j _
        nlinarith [mul_le_mul_of_nonneg_right (hcap j) (hnonneg j)]
      _ = ((m : ℝ)/(r+1 : ℕ)) * ∑ j, lam j := by rw [Finset.mul_sum]
      _ ≤ ((m : ℝ)/(r+1 : ℕ)) * m :=
        mul_le_mul_of_nonneg_left htrace (by positivity)
      _ = _ := by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (Fin m × Fin m)))
    (f := fun _ => (1 : ℝ)) (g := fun ij => |G ij.1 ij.2|)
  have hcs' : (∑ i, ∑ j, |G i j|)^2 ≤ (m : ℝ)^2 * (∑ i, ∑ j, G i j ^ 2) := by
    simpa only [one_mul, one_pow, sq_abs, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, nsmul_eq_mul, mul_one,
      Fintype.sum_prod_type, ← pow_two, sq_abs, Nat.cast_pow] using hcs
  have hfinal : (∑ i, ∑ j, |G i j|)^2 ≤ (m : ℝ)^4/(r+1 : ℕ) := by
    rw [hsq] at hcs'
    calc
      _ ≤ (m : ℝ)^2 * (∑ j, (lam j)^2) := hcs'
      _ ≤ (m : ℝ)^2 * ((m : ℝ)^2/(r+1 : ℕ)) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = _ := by ring
  have hsqrt : (Real.sqrt (r+1 : ℕ))^2 = (r+1 : ℕ) := Real.sq_sqrt hD.le
  apply (sq_le_sq₀ (by positivity : 0 ≤ ∑ i, ∑ j, |G i j|)
    (by positivity : 0 ≤ (m : ℝ)^2/Real.sqrt (r+1 : ℕ))).1
  calc
    _ ≤ (m : ℝ)^4/(r+1 : ℕ) := hfinal
    _ = _ := by rw [div_pow, hsqrt]; ring

/-- An actual covariance matrix has an ordered orthonormal eigenbasis,
with nonnegative eigenvalues summing to the unit-row trace. -/
theorem ordered_covariance_basis {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : NLA.Statements.RowDeletion.UnitRows A) :
    ∃ b : OrthonormalBasis (Fin n) ℝ (Euclid n), ∃ lam : Fin n → ℝ,
      Antitone lam ∧ (∀ j, 0 ≤ lam j) ∧ (∑ j, lam j = (m : ℝ)) ∧
      ∀ j, Matrix.toEuclideanLin (A.transpose*A) (b j) = lam j • b j := by
  let C := A.transpose*A
  let T := Matrix.toEuclideanLin C
  have hC : C.IsHermitian := by
    simpa only [C, Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.isHermitian_conjTranspose_mul_self A
  have hCp : C.PosSemidef := by
    simpa only [C, Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self A
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hC
  have hn : Module.finrank ℝ (Euclid n) = n := by simp [Euclid]
  let b := hT.eigenvectorBasis hn
  let lam := hT.eigenvalues hn
  refine ⟨b,lam,hT.eigenvalues_antitone hn,?_,?_,hT.apply_eigenvectorBasis hn⟩
  · intro j
    apply eigenvalue_nonneg_of_nonneg (hT.hasEigenvalue_eigenvalues hn j)
    intro x
    simpa only [T, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
      RCLike.re_to_real, dotProduct_comm] using hCp.re_dotProduct_nonneg (WithLp.ofLp x)
  · have htrace := hT.trace_eq_sum_eigenvalues hn
    have heq : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis T = C := by
      ext i j
      simp [LinearMap.toMatrix_apply, T, Matrix.toLpLin_apply]
    have htraceT : LinearMap.trace ℝ (Euclid n) T = Matrix.trace C := by
      rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis, heq]
    rw [htraceT] at htrace
    change Matrix.trace C = ∑ j, lam j at htrace
    change ∑ j, lam j = _
    rw [← htrace]
    change Matrix.trace (A.transpose*A) = _
    rw [← matrix_entry_square_sum]
    calc
      _ = ∑ _i : Fin m, (1 : ℝ) := Finset.sum_congr rfl (fun i _ => hA i)
      _ = _ := by simp

/-- Ordered nonnegative eigenvalues obey the trace-over-index tail bound. -/
theorem antitone_tail_le {n r : ℕ} (hr : r < n) (lam : Fin n → ℝ)
    (hanti : Antitone lam) (hpos : ∀ j, 0 ≤ lam j) {M : ℝ}
    (hsum : ∑ j, lam j ≤ M) (j : Fin n) (hj : r ≤ j.val) :
    lam j ≤ M/(r+1 : ℕ) := by
  classical
  let q : Fin n := ⟨r, hr⟩
  let e : Fin (r+1) → Fin n := fun i => ⟨i.val, by omega⟩
  have heinj : Function.Injective e := by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin n => x.val) hij)
  have hprefix : ∑ i : Fin (r+1), lam (e i) ≤ ∑ j, lam j := by
    rw [← Finset.sum_image (fun i _ j _ hij => heinj hij)]
    exact Finset.sum_le_univ_sum_of_nonneg hpos
  have hlower : ((r+1 : ℕ) : ℝ)*lam q ≤ ∑ i : Fin (r+1), lam (e i) := by
    calc
      _ = ∑ _i : Fin (r+1), lam q := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hanti (by change i.val ≤ r; omega)
  have hq : lam q ≤ M/(r+1 : ℕ) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (r+1 : ℕ))).2
    nlinarith [(hlower.trans hprefix).trans hsum]
  exact (hanti (by exact hj)).trans hq

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The linear map with a genuinely orthonormal column family is an isometry. -/
def columnIsometry {n d : ℕ} (u : Fin d → Euclid n) (hu : Orthonormal ℝ u) :
    Euclid d →ₗᵢ[ℝ] Euclid n := by
  let U : Matrix (Fin n) (Fin d) ℝ := fun k j => u j k
  let L := Matrix.toEuclideanLin U
  have himage : L ∘ (EuclideanSpace.basisFun (Fin d) ℝ).toBasis = u := by
    ext j k
    change (WithLp.ofLp (Matrix.toEuclideanLin U ((EuclideanSpace.basisFun (Fin d) ℝ) j))) k = u j k
    rw [Matrix.ofLp_toEuclideanLin_apply]
    simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.single, PiLp.ofLp_single]
    exact congrArg (fun v : Fin n → ℝ => v k) (Matrix.mulVec_single_one U j)
  let eb : Module.Basis (Fin d) ℝ (Euclid d) := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  have heb : Orthonormal ℝ eb := (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal
  have hL : Orthonormal ℝ (L ∘ eb) := by
    change Orthonormal ℝ (L ∘ (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
    rw [himage]
    exact hu
  exact L.isometryOfOrthonormal (v := eb) heb hL

theorem columnIsometry_apply {n d : ℕ} (u : Fin d → Euclid n) (hu : Orthonormal ℝ u)
    (g : Euclid d) :
    WithLp.ofLp (columnIsometry u hu g) =
      Matrix.mulVec ((fun k j => u j k) : Matrix (Fin n) (Fin d) ℝ) (WithLp.ofLp g) := rfl

/-- Data of a genuine orthogonal retained subspace and its actual projected rows. -/
structure SpectralProjectionData {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : ℕ) where
  rows : Matrix (Fin m) (Fin (n-r)) ℝ
  lift : Euclid (n-r) →ₗᵢ[ℝ] Euclid n
  row_eq : ∀ i (g : Euclid (n-r)),
    NLA.Statements.RowDeletion.RowValue A i (WithLp.ofLp (lift g)) =
      inner ℝ (WithLp.toLp 2 (rows i)) g
  row_norm_sq : ∀ i, ‖WithLp.toLp 2 (rows i)‖^2 ≤ 1
  gram_sum : (∑ i, ∑ j, |inner ℝ (WithLp.toLp 2 (rows i)) (WithLp.toLp 2 (rows j))|) ≤
    (m : ℝ)^2/Real.sqrt (r+1 : ℕ)

/-- The actual covariance eigenspace construction supplies every field of the
retained-subspace data, with no spectral assumption beyond genuine unit rows. -/
theorem exists_spectral_projection {m n r : ℕ} (hr : r < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : NLA.Statements.RowDeletion.UnitRows A) :
    Nonempty (SpectralProjectionData A r) := by
  classical
  obtain ⟨b,lam,hanti,hpos,hsum,heigen⟩ := ordered_covariance_basis A hA
  let e : Fin (n-r) → Fin n := fun j => ⟨r+j.val, by omega⟩
  have heinj : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    dsimp [e] at hv
    omega
  let u : Fin (n-r) → Euclid n := fun j => b (e j)
  have hu : Orthonormal ℝ u := b.orthonormal.comp e heinj
  let U : Matrix (Fin n) (Fin (n-r)) ℝ := fun k j => u j k
  let B := A*U
  let lam' : Fin (n-r) → ℝ := fun j => lam (e j)
  have hCU : ∀ k j, ((A.transpose*A)*U) k j = lam' j * U k j := by
    intro k j
    have h := congrArg (fun x : Euclid n => x k) (heigen (e j))
    change ((A.transpose*A).mulVec (WithLp.ofLp (u j))) k = lam' j * U k j at h
    exact h
  have hUU : U.transpose*U = 1 := by
    ext i j
    have h := (orthonormal_iff_ite.mp hu) i j
    change (∑ k, U k i * U k j) = if i = j then 1 else 0
    change (∑ k, u i k * u j k) = _
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial, mul_comm] using h
  have hdiag : B.transpose*B = Matrix.diagonal lam' := by
    change (A*U).transpose*(A*U) = _
    rw [Matrix.transpose_mul]
    have hmul : (U.transpose*A.transpose)*(A*U) = U.transpose*((A.transpose*A)*U) := by
      simp only [Matrix.mul_assoc]
    rw [hmul]
    ext i j
    simp only [Matrix.mul_apply, hCU]
    have hf : ∑ k, U.transpose i k * (lam' j * U k j) =
        lam' j * (U.transpose*U) i j := by
      simp only [Matrix.mul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hf, hUU]
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hrow : ∀ i, ∑ j, B i j ^ 2 ≤ 1 := by
    intro i
    have h := hu.sum_inner_products_le (x := WithLp.toLp 2 (A i)) (s := Finset.univ)
    have heq (j : Fin (n-r)) : inner ℝ (u j) (WithLp.toLp 2 (A i)) = B i j := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
        star_trivial, B, Matrix.mul_apply, U]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simpa only [heq, Real.norm_eq_abs, sq_abs, EuclideanSpace.norm_sq_eq,
      WithLp.ofLp_toLp, hA i] using h
  have htrace : ∑ j, lam' j ≤ (m : ℝ) := by
    have heq : ∑ j, lam' j = ∑ i, ∑ j, B i j ^ 2 := by
      rw [matrix_entry_square_sum, hdiag]
      simp
    rw [heq]
    calc
      _ ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hrow i)
      _ = _ := by simp
  have hcap : ∀ j, lam' j ≤ (m : ℝ)/(r+1 : ℕ) := by
    intro j
    exact antitone_tail_le hr lam hanti hpos hsum.le (e j) (by dsimp [e]; omega)
  let lift : Euclid (n-r) →ₗᵢ[ℝ] Euclid n := columnIsometry u hu
  refine ⟨{rows := B, lift := lift, row_eq := ?_, row_norm_sq := ?_, gram_sum := ?_}⟩
  · intro i g
    have hlift : WithLp.ofLp (lift g) = U.mulVec (WithLp.ofLp g) := columnIsometry_apply u hu g
    unfold NLA.Statements.RowDeletion.RowValue
    rw [hlift]
    change (A.mulVec (U.mulVec (WithLp.ofLp g))) i = _
    rw [Matrix.mulVec_mulVec]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      B, Matrix.mulVec]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro i
    simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] using hrow i
  · have hg := gram_abs_sum_le_of_diagonal B lam' hdiag (fun j => hpos (e j)) hcap htrace
    convert hg using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      Matrix.mul_apply, Matrix.transpose_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring

#assert_trust kernel antitone_tail_le
#assert_trust kernel exists_spectral_projection
#assert_trust kernel ordered_covariance_basis
#assert_trust kernel gram_abs_sum_le_of_diagonal
#print axioms gram_abs_sum_le_of_diagonal
end NLA.Proofs.IE22
