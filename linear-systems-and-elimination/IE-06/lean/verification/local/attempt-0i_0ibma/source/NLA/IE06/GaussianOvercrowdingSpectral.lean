/-
Deterministic spectral event to inverse-Gram principal-minor implication for
Gaussian overcrowding. Exact contracts independently reviewed before code in
reviews/gaussian-overcrowding-spectral-contract.md. No probability input here.
-/
import NLA.IE06.SpectralStacking

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Matrix Module Polynomial
open scoped BigOperators
namespace NLA.IE06.GaussianOvercrowdingSpectral
open Spectral SpectralStacking

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]

theorem singularValue_le_of_norm_le (S : E →ₗ[ℝ] F) (T : E →ₗ[ℝ] G)
    {n : ℕ} (hn : finrank ℝ E = n) (i : Fin n)
    (h : ∀ x, ‖S x‖ ≤ ‖T x‖) : S.singularValues i ≤ T.singularValues i := by
  let U := S.isSymmetric_adjoint_comp_self.leadingEigenSubspace hn
    (Nat.succ_le_of_lt i.isLt)
  apply singular_lower_of_subspace T hn i U
    (le_of_eq (S.isSymmetric_adjoint_comp_self.finrank_leadingEigenSubspace hn _).symm)
  intro x hx
  exact (singularValue_mul_norm_le_of_mem_leading S hn i hx).trans (h x)

theorem row_restriction_norm_le {m n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (e : Fin m ↪ Fin n) (x : EuclideanSpace ℝ (Fin p)) :
    ‖euclideanMap (A.submatrix e id) x‖ ≤ ‖euclideanMap A x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change ∑ i, (euclideanMap A x (e i))^2 ≤ ∑ j, (euclideanMap A x j)^2
  rw [← Finset.sum_image (f := fun j => (euclideanMap A x j)^2)
    (fun i _ j _ h => e.injective h)]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro i _ _
  exact sq_nonneg _

theorem singularValue_rows_le {m n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (e : Fin m ↪ Fin n) (i : Fin p) :
    singularValue (A.submatrix e id) i ≤ singularValue A i :=
  singularValue_le_of_norm_le _ _ (by simp) i (row_restriction_norm_le A e)

theorem eigenvalue_lower_of_subspace (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    {n : ℕ} (hn : finrank ℝ E = n) (i : Fin n) (U : Submodule ℝ E)
    (hU : i.val+1 ≤ finrank ℝ U) (a : ℝ)
    (h : ∀ x ∈ U, a*‖x‖^2 ≤ inner ℝ (T x) x) : a ≤ hT.eigenvalues hn i := by
  obtain ⟨x,hx,ht,hx0⟩ := Submodule.exists_ne_zero_mem_inf_of_finrank_lt_add_finrank
    U (hT.trailingEigenSubspace hn i) (by
      rw [hn,hT.finrank_trailingEigenSubspace hn i]
      omega)
  have hl : a ≤ LinearMap.rayleighQuotient T x := by
    exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx0))).mpr (h x hx)
  exact hl.trans (hT.rayleighQuotient_le_eigenvalues_of_mem_trailingEigenSubspace hn i ht hx0)

theorem inverse_gram_quadratic_lower {m n : ℕ} (R : Matrix (Fin m) (Fin n) ℝ)
    (hR : (R*Rᴴ).PosDef) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin m))
    (hx : ‖(euclideanMap R).adjoint x‖ ≤ t*‖x‖) :
    (t^2)⁻¹ * ‖x‖^2 ≤ inner ℝ (euclideanMap ((R*Rᴴ)⁻¹) x) x := by
  let T := euclideanMap R
  let H := euclideanMap ((R*Rᴴ)⁻¹)
  have hid : T.comp (T.adjoint.comp H) = LinearMap.id := by
    have hm := Matrix.mul_nonsing_inv (R*Rᴴ)
      ((Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit)
    have hh := congrArg Matrix.toEuclideanLin hm
    simpa only [T,H,euclideanMap, Matrix.toLpLin_mul_same,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.toLpLin_one,
      LinearMap.comp_assoc] using hh
  have hxid : T (T.adjoint (H x)) = x :=
    congrArg (fun f : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) => f x) hid
  have hquad : ‖T.adjoint (H x)‖^2 = inner ℝ (H x) x := by
    rw [← real_inner_self_eq_norm_sq, T.adjoint_inner_left, hxid]
  by_cases hx0 : x=0
  · simp [hx0]
  have hc : ‖x‖^2 ≤ ‖T.adjoint x‖ * ‖T.adjoint (H x)‖ := by
    calc
      ‖x‖^2 = inner ℝ (T.adjoint x) (T.adjoint (H x)) := by
        rw [T.adjoint_inner_left, hxid, real_inner_self_eq_norm_sq]
      _ ≤ _ := real_inner_le_norm _ _
  have hd := mul_le_mul_of_nonneg_right hx (norm_nonneg (T.adjoint (H x)))
  have hb : ‖x‖ ≤ t*‖T.adjoint (H x)‖ := by
    apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hx0)).mp
    change ‖T.adjoint x‖ ≤ _ at hx
    nlinarith
  have hs := pow_le_pow_left₀ (norm_nonneg x) hb 2
  rw [mul_pow, hquad] at hs
  exact (inv_mul_le_iff₀ (sq_pos_of_pos ht)).mpr hs

/-- True decreasing Euclidean eigenvalues, with explicit finite cardinality. -/
def sortedEigenvalues {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (hH : H.IsHermitian) :
    Fin m → ℝ :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH).eigenvalues (by simp)

theorem charpoly_eq_diagonal_sorted {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (hH : H.IsHermitian) : H.charpoly = (Matrix.diagonal (sortedEigenvalues H hH)).charpoly := by
  rw [Matrix.charpoly_diagonal]
  calc
    H.charpoly = (euclideanMap H).charpoly :=
      (Matrix.charpoly_toLin H (PiLp.basisFun 2 ℝ (Fin m))).symm
    _ = _ := by
      simpa [sortedEigenvalues, euclideanMap] using
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH).charpoly_eq
          (show finrank ℝ (EuclideanSpace ℝ (Fin m)) = m by simp)

theorem sum_principal_minors_eq_eigen_products {m r : ℕ}
    (H : Matrix (Fin m) (Fin m) ℝ) (hH : H.IsHermitian) (hr : r ≤ m) :
    (∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
      (H.submatrix (Subtype.val : S → Fin m) Subtype.val).det) =
    ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
      ∏ i : S, sortedEigenvalues H hH i := by
  have hc := congrArg (fun f : ℝ[X] => f.coeff (m-r)) (charpoly_eq_diagonal_sorted H hH)
  have hc1 := Matrix.charpoly_coeff_eq_sum_minors H r (by simpa using hr)
  have hc2 := Matrix.charpoly_coeff_eq_sum_minors (Matrix.diagonal (sortedEigenvalues H hH))
    r (by simpa using hr)
  simp only [Fintype.card_fin] at hc1 hc2
  rw [hc1,hc2] at hc
  have he : (∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
      ((Matrix.diagonal (sortedEigenvalues H hH)).submatrix
        (Subtype.val : S → Fin m) Subtype.val).det) =
      ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
        ∏ i : S, sortedEigenvalues H hH i := by
    apply Finset.sum_congr rfl
    intro S _
    rw [Matrix.submatrix_diagonal _ _ Subtype.val_injective, Matrix.det_diagonal]
    rfl
  rw [he] at hc
  exact mul_left_cancel₀ (pow_ne_zero r (by norm_num : (-1:ℝ)≠0)) hc

theorem inverse_gram_eigenvalue_lower {m n r : ℕ}
    (R : Matrix (Fin m) (Fin n) ℝ) (hR : (R*Rᴴ).PosDef)
    (hr : 1 ≤ r) (hrm : r ≤ m) (hmn : m ≤ n) {t : ℝ} (ht : 0 < t)
    (hs : singularValue R (m-r) ≤ t) :
    (t^2)⁻¹ ≤ sortedEigenvalues ((R*Rᴴ)⁻¹) hR.inv.isHermitian ⟨r-1, by omega⟩ := by
  let T := euclideanMap R
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  let i : Fin n := ⟨m-r, by omega⟩
  let V := T.isSymmetric_adjoint_comp_self.trailingEigenSubspace hn i
  let K := Vᗮ.map T
  let W := Kᗮ
  have hV : finrank ℝ V = n-(m-r) :=
    T.isSymmetric_adjoint_comp_self.finrank_trailingEigenSubspace hn i
  have hK : finrank ℝ K ≤ m-r := by
    have hv := V.finrank_add_finrank_orthogonal
    rw [hn,hV] at hv
    have he := Submodule.finrank_map_le T Vᗮ
    change finrank ℝ K ≤ finrank ℝ Vᗮ at he
    omega
  have hW : r ≤ finrank ℝ W := by
    have he := K.finrank_add_finrank_orthogonal
    have hm : finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by simp
    rw [hm] at he
    change finrank ℝ K + finrank ℝ W = m at he
    omega
  apply eigenvalue_lower_of_subspace (euclideanMap ((R*Rᴴ)⁻¹))
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hR.inv.isHermitian)
    (show finrank ℝ (EuclideanSpace ℝ (Fin m)) = m by simp)
    ⟨r-1, by omega⟩ W (by change r-1+1 ≤ finrank ℝ W; omega)
  intro x hx
  apply inverse_gram_quadratic_lower R hR ht x
  have hupper := adjoint_upper_off_image T V (T.singularValues_nonneg i)
    (fun z hz => norm_le_singularValue_mul_of_mem_trailing T hn i hz) hx
  exact hupper.trans (mul_le_mul_of_nonneg_right hs (norm_nonneg x))

theorem exists_large_principal_minor {m r : ℕ}
    (H : Matrix (Fin m) (Fin m) ℝ) (hH : H.PosSemidef)
    (hr : 1 ≤ r) (hrm : r ≤ m) {a : ℝ} (ha : 0 ≤ a)
    (hl : a ≤ sortedEigenvalues H hH.isHermitian ⟨r-1, by omega⟩) :
    ∃ S : Finset (Fin m), S.card=r ∧ a^r / (m.choose r : ℝ) ≤
      (H.submatrix (Subtype.val : S → Fin m) Subtype.val).det := by
  let eig := sortedEigenvalues H hH.isHermitian
  have heig : ∀ i, 0 ≤ eig i := by
    intro i
    exact (Matrix.isPositive_toEuclideanLin_iff.mpr hH).nonneg_eigenvalues (by simp) i
  have hant : Antitone eig :=
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH.isHermitian).eigenvalues_antitone (by simp)
  let f : Fin r ↪ Fin m := ⟨Fin.castLE hrm, Fin.castLE_injective hrm⟩
  let L : Finset (Fin m) := Finset.univ.image f
  have hc : L.card=r := by
    simp [L, Finset.card_image_of_injective _ f.injective]
  have hm : L ∈ (Finset.univ : Finset (Fin m)).powersetCard r :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc⟩
  have hp : a^r ≤ ∏ i : L, eig i := by
    rw [Finset.prod_coe_sort]
    calc
      a^r = ∏ _i ∈ L, a := by rw [Finset.prod_const, hc]
      _ ≤ _ := by
        apply Finset.prod_le_prod (fun _ _ => ha)
        intro i hi
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
        exact hl.trans (hant (by change j.val ≤ r-1; omega))
  have hs : a^r ≤ ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
      (H.submatrix (Subtype.val : S → Fin m) Subtype.val).det := by
    rw [sum_principal_minors_eq_eigen_products H hH.isHermitian hrm]
    have hnon (S : Finset (Fin m)) : 0 ≤ ∏ i : S, eig i :=
      Finset.prod_nonneg (fun i _ => heig i)
    exact hp.trans (Finset.single_le_sum
      (f := fun S : Finset (Fin m) => ∏ i : S, eig i) (fun S _ => hnon S) hm)
  have hN : 0 < (m.choose r : ℝ) := by exact_mod_cast Nat.choose_pos hrm
  have hcard : ((Finset.univ : Finset (Fin m)).powersetCard r).card=m.choose r := by
    simp
  have hsum : (∑ _S ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
      a^r/(m.choose r : ℝ)) ≤
      ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
        (H.submatrix (Subtype.val : S → Fin m) Subtype.val).det := by
    simpa only [Finset.sum_const, nsmul_eq_mul, hcard, mul_div_cancel₀ _ (ne_of_gt hN)] using hs
  obtain ⟨S,hS,h⟩ := Finset.exists_le_of_sum_le ⟨L,hm⟩ hsum
  exact ⟨S,(Finset.mem_powersetCard.mp hS).2,h⟩

/-- The precise deterministic implication used before the Gaussian moment
union bound; all inverse-Gram and spectral premises are explicit. -/
theorem singular_event_implies_large_inverse_gram_minor {m n r : ℕ}
    (R : Matrix (Fin m) (Fin n) ℝ) (hR : (R*Rᴴ).PosDef)
    (hr : 1 ≤ r) (hrm : r ≤ m) (hmn : m ≤ n) {t : ℝ} (ht : 0<t)
    (hs : singularValue R (m-r) ≤ t) :
    ∃ S : Finset (Fin m), S.card=r ∧ (t^(2*r))⁻¹/(m.choose r : ℝ) ≤
      (((R*Rᴴ)⁻¹).submatrix (Subtype.val : S → Fin m) Subtype.val).det := by
  have he := inverse_gram_eigenvalue_lower R hR hr hrm hmn ht hs
  obtain ⟨S,hS,h⟩ := exists_large_principal_minor ((R*Rᴴ)⁻¹) hR.inv.posSemidef
    hr hrm (by positivity : 0 ≤ (t^2)⁻¹) he
  refine ⟨S,hS,?_⟩
  simpa only [inv_pow, ← pow_mul] using h

end NLA.IE06.GaussianOvercrowdingSpectral

#assert_trust kernel NLA.IE06.GaussianOvercrowdingSpectral.singularValue_le_of_norm_le
#print axioms NLA.IE06.GaussianOvercrowdingSpectral.singularValue_le_of_norm_le
#assert_trust kernel NLA.IE06.GaussianOvercrowdingSpectral.row_restriction_norm_le
#print axioms NLA.IE06.GaussianOvercrowdingSpectral.row_restriction_norm_le
#assert_trust kernel NLA.IE06.GaussianOvercrowdingSpectral.singularValue_rows_le
#print axioms NLA.IE06.GaussianOvercrowdingSpectral.singularValue_rows_le
#assert_trust kernel NLA.IE06.GaussianOvercrowdingSpectral.eigenvalue_lower_of_subspace
#print axioms NLA.IE06.GaussianOvercrowdingSpectral.eigenvalue_lower_of_subspace
#assert_trust kernel NLA.IE06.GaussianOvercrowdingSpectral.inverse_gram_quadratic_lower
#print axioms NLA.IE06.GaussianOvercrowdingSpectral.inverse_gram_quadratic_lower
#assert_trust kernel NLA.IE06.GaussianOvercrowdingSpectral.sortedEigenvalues
#print axioms NLA.IE06.GaussianOvercrowdingSpectral.sortedEigenvalues
#assert_trust kernel NLA.IE06.GaussianOvercrowdingSpectral.charpoly_eq_diagonal_sorted
#print axioms NLA.IE06.GaussianOvercrowdingSpectral.charpoly_eq_diagonal_sorted
#assert_trust kernel NLA.IE06.GaussianOvercrowdingSpectral.sum_principal_minors_eq_eigen_products
#print axioms NLA.IE06.GaussianOvercrowdingSpectral.sum_principal_minors_eq_eigen_products
#assert_trust kernel NLA.IE06.GaussianOvercrowdingSpectral.inverse_gram_eigenvalue_lower
#print axioms NLA.IE06.GaussianOvercrowdingSpectral.inverse_gram_eigenvalue_lower
#assert_trust kernel NLA.IE06.GaussianOvercrowdingSpectral.exists_large_principal_minor
#print axioms NLA.IE06.GaussianOvercrowdingSpectral.exists_large_principal_minor
#assert_trust kernel NLA.IE06.GaussianOvercrowdingSpectral.singular_event_implies_large_inverse_gram_minor
#print axioms NLA.IE06.GaussianOvercrowdingSpectral.singular_event_implies_large_inverse_gram_minor
