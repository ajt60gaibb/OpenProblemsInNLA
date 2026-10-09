/-
Deterministic spectral support for manuscript Lemma 4.6. Exact target approved
before implementation in reviews/spectral-stacking-specification.md. Forward
singular-value min–max uses the separately reviewed, attributed vendor proofs.
-/
import NLA.IE06.Spectral
import NLA.IE06.Vendor.SLT.MatrixInfra.CourantFischer

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Module Matrix
namespace NLA.IE06.SpectralStacking

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- A forward expansion on an adequately large subspace gives the indexed
singular lower bound, directly from the trailing Gram subspace. -/
theorem singular_lower_of_subspace (T : E →ₗ[ℝ] F) {n : ℕ}
    (hn : finrank ℝ E = n) (i : Fin n) (U : Submodule ℝ E)
    (hU : i.val + 1 ≤ finrank ℝ U) (a : ℝ)
    (h : ∀ x ∈ U, a * ‖x‖ ≤ ‖T x‖) : a ≤ T.singularValues i := by
  obtain ⟨x, hx, ht, hx0⟩ :=
    Submodule.exists_ne_zero_mem_inf_of_finrank_lt_add_finrank U
      (T.isSymmetric_adjoint_comp_self.trailingEigenSubspace hn i) (by
        rw [hn, T.isSymmetric_adjoint_comp_self.finrank_trailingEigenSubspace hn i]
        omega)
  have hl : a ≤ LinearMap.singularQuotient T x := by
    exact (le_div_iff₀ (norm_pos_iff.mpr hx0)).mpr (h x hx)
  exact hl.trans
    (T.singularQuotient_le_singularValues_of_mem_gram_trailingEigenSubspace hn i ht hx0)

theorem norm_le_singularValue_mul_of_mem_trailing (T : E →ₗ[ℝ] F) {n : ℕ}
    (hn : finrank ℝ E = n) (i : Fin n) {x : E}
    (hx : x ∈ T.isSymmetric_adjoint_comp_self.trailingEigenSubspace hn i) :
    ‖T x‖ ≤ T.singularValues i * ‖x‖ := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · exact (div_le_iff₀ (norm_pos_iff.mpr hx0)).mp
      (T.singularQuotient_le_singularValues_of_mem_gram_trailingEigenSubspace hn i hx hx0)

theorem singularValue_mul_norm_le_of_mem_leading (T : E →ₗ[ℝ] F) {n : ℕ}
    (hn : finrank ℝ E = n) (i : Fin n) {x : E}
    (hx : x ∈ T.isSymmetric_adjoint_comp_self.leadingEigenSubspace hn
      (Nat.succ_le_of_lt i.isLt)) :
    T.singularValues i * ‖x‖ ≤ ‖T x‖ := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · exact (le_div_iff₀ (norm_pos_iff.mpr hx0)).mp
      (T.singularValues_le_singularQuotient_of_mem_gram_leadingEigenSubspace hn i hx hx0)

/-- The adjoint is bounded below on the image of a subspace on which the
forward map is bounded below. -/
theorem adjoint_lower_on_image (T : E →ₗ[ℝ] F) (U : Submodule ℝ E)
    {d : ℝ} (hd : 0 < d) (hU : ∀ x ∈ U, d * ‖x‖ ≤ ‖T x‖)
    {y : F} (hy : y ∈ U.map T) : d * ‖y‖ ≤ ‖T.adjoint y‖ := by
  obtain ⟨x, hx, rfl⟩ := hy
  by_cases hy0 : T x = 0
  · simp [hy0]
  have hinner : ‖T x‖ ^ 2 ≤ ‖T.adjoint (T x)‖ * ‖x‖ := by
    calc
      ‖T x‖ ^ 2 = inner ℝ (T.adjoint (T x)) x := by
        rw [T.adjoint_inner_left, real_inner_self_eq_norm_sq]
      _ ≤ _ := real_inner_le_norm _ _
  have h1 := mul_le_mul_of_nonneg_left hinner hd.le
  have h2 := mul_le_mul_of_nonneg_left (hU x hx) (norm_nonneg (T.adjoint (T x)))
  apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hy0)).mp
  nlinarith

/-- Removing the image of the orthogonal complement of a good domain subspace
bounds the adjoint, without assuming an adjoint singular-value identity. -/
theorem adjoint_upper_off_image (T : E →ₗ[ℝ] F) (V : Submodule ℝ E)
    {b : ℝ} (hb : 0 ≤ b) (hV : ∀ x ∈ V, ‖T x‖ ≤ b * ‖x‖)
    {y : F} (hy : y ∈ (Vᗮ.map T)ᗮ) : ‖T.adjoint y‖ ≤ b * ‖y‖ := by
  have hx : T.adjoint y ∈ V := by
    rw [← V.orthogonal_orthogonal, Submodule.mem_orthogonal]
    intro x hx
    rw [T.adjoint_inner_right]
    exact (Submodule.mem_orthogonal _ _).mp hy (T x) ⟨x, hx, rfl⟩
  by_cases hx0 : T.adjoint y = 0
  · simp only [hx0, norm_zero]
    positivity
  have hinner : ‖T.adjoint y‖ ^ 2 ≤ ‖y‖ * ‖T (T.adjoint y)‖ := by
    calc
      ‖T.adjoint y‖ ^ 2 = inner ℝ y (T (T.adjoint y)) := by
        rw [← T.adjoint_inner_left, real_inner_self_eq_norm_sq]
      _ ≤ _ := real_inner_le_norm _ _
  have h2 := mul_le_mul_of_nonneg_left (hV (T.adjoint y) hx) (norm_nonneg y)
  apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hx0)).mp
  nlinarith

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem injective_of_norm_lower (T : E →ₗ[ℝ] F) {d : ℝ} (hd : 0 < d)
    (h : ∀ x, d * ‖x‖ ≤ ‖T x‖) : Function.Injective T := by
  intro x y hxy
  have hb := h (x-y)
  rw [map_sub, hxy, sub_self, norm_zero] at hb
  have hz : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Simultaneous adjoint bounds, using only forward Gram eigenspaces. -/
theorem exists_good_subspace {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (T : E →ₗ[ℝ] F) (S : G →ₗ[ℝ] F) {n m : ℕ}
    (hn : finrank ℝ E = n) (hm : finrank ℝ G = m)
    (i : Fin n) (j : Fin m) (hd : 0 < T.singularValues i) :
    ∃ W : Submodule ℝ F, i.val + 1 - j.val ≤ finrank ℝ W ∧
      (∀ y ∈ W, T.singularValues i * ‖y‖ ≤ ‖T.adjoint y‖) ∧
      (∀ y ∈ W, ‖S.adjoint y‖ ≤ S.singularValues j * ‖y‖) := by
  let U := T.isSymmetric_adjoint_comp_self.leadingEigenSubspace hn
    (Nat.succ_le_of_lt i.isLt)
  let V := S.isSymmetric_adjoint_comp_self.trailingEigenSubspace hm j
  let L := U.map T
  let K := Vᗮ.map S
  let W := L ⊓ Kᗮ
  have hU : finrank ℝ U = i.val+1 :=
    T.isSymmetric_adjoint_comp_self.finrank_leadingEigenSubspace hn _
  have hV : finrank ℝ V = m-j.val :=
    S.isSymmetric_adjoint_comp_self.finrank_trailingEigenSubspace hm j
  have hLo : ∀ x ∈ U, T.singularValues i * ‖x‖ ≤ ‖T x‖ :=
    fun x hx => singularValue_mul_norm_le_of_mem_leading T hn i hx
  have hi : Function.Injective (T.domRestrict U) :=
    injective_of_norm_lower (T.domRestrict U) hd fun x => hLo x x.property
  have hL : finrank ℝ L = i.val+1 := by
    change finrank ℝ (U.map T) = _
    rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hi, hU]
  have hK : finrank ℝ K ≤ j.val := by
    have hb := V.finrank_add_finrank_orthogonal
    rw [hm, hV] at hb
    have hf := Submodule.finrank_map_le S Vᗮ
    change finrank ℝ K ≤ finrank ℝ Vᗮ at hf
    omega
  have hW : i.val+1-j.val ≤ finrank ℝ W := by
    have hb := Submodule.finrank_sup_add_finrank_inf_eq L Kᗮ
    have hp := Submodule.finrank_le (L ⊔ Kᗮ)
    have hk := K.finrank_add_finrank_orthogonal
    change _ + finrank ℝ W = _ at hb
    omega
  refine ⟨W, hW, ?_, ?_⟩
  · intro y hy
    exact adjoint_lower_on_image T U hd hLo hy.1
  · intro y hy
    exact adjoint_upper_off_image S V (S.singularValues_nonneg j)
      (fun x hx => norm_le_singularValue_mul_of_mem_trailing S hm j hx) hy.2

/-- A positive lower bound for the adjoint produces a genuine linear right
inverse with the reciprocal norm bound. -/
theorem exists_bounded_rightInverse (T : E →ₗ[ℝ] F) {d : ℝ} (hd : 0 < d)
    (h : ∀ y, d * ‖y‖ ≤ ‖T.adjoint y‖) :
    ∃ R : F →ₗ[ℝ] E, T.comp R = LinearMap.id ∧ ∀ y, ‖R y‖ ≤ ‖y‖ / d := by
  have hi := injective_of_norm_lower T.adjoint hd h
  have hiA : Function.Injective (T.comp T.adjoint) :=
    T.self_comp_adjoint_injective_iff.mpr hi
  let e := LinearEquiv.ofInjectiveEndo (T.comp T.adjoint) hiA
  let R := T.adjoint.comp e.symm.toLinearMap
  have hR : T.comp R = LinearMap.id := by
    ext y
    exact e.apply_symm_apply y
  refine ⟨R, hR, ?_⟩
  intro y
  by_cases hr0 : R y = 0
  · simp only [hr0, norm_zero]
    positivity
  have hr : T (R y) = y := congrArg (fun f : F →ₗ[ℝ] F => f y) hR
  have hinner : ‖R y‖ ^ 2 ≤ ‖e.symm y‖ * ‖y‖ := by
    calc
      ‖R y‖ ^ 2 = inner ℝ (e.symm y) (T (R y)) := by
        rw [← T.adjoint_inner_left]
        exact (real_inner_self_eq_norm_sq (R y)).symm
      _ = inner ℝ (e.symm y) y := by rw [hr]
      _ ≤ _ := real_inner_le_norm _ _
  have hl := h (e.symm y)
  change d * ‖e.symm y‖ ≤ ‖R y‖ at hl
  have h1 := mul_le_mul_of_nonneg_left hinner hd.le
  have h2 := mul_le_mul_of_nonneg_right hl (norm_nonneg y)
  apply (le_div_iff₀ hd).mpr
  apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hr0)).mp
  nlinarith

theorem projection_comp_adjoint (T : E →ₗ[ℝ] F) (W : Submodule ℝ F) :
    (W.orthogonalProjectionOnto.toLinearMap.comp T).adjoint =
      T.adjoint.comp W.subtype := by
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  rw [LinearMap.adjoint_comp, ContinuousLinearMap.adjoint_toLinearMap,
    W.adjoint_orthogonalProjectionOnto]
  rfl

theorem projection_norm_le_of_adjoint (T : E →ₗ[ℝ] F) (W : Submodule ℝ F)
    {b : ℝ} (hb : 0 ≤ b) (h : ∀ y ∈ W, ‖T.adjoint y‖ ≤ b * ‖y‖) (x : E) :
    ‖W.orthogonalProjectionOnto (T x)‖ ≤ b * ‖x‖ := by
  let D := W.orthogonalProjectionOnto.toLinearMap.comp T
  have hd : ∀ y : W, ‖D.adjoint y‖ ≤ b * ‖y‖ := by
    intro y
    rw [projection_comp_adjoint]
    exact h y y.property
  by_cases hx : D x = 0
  · change ‖D x‖ ≤ _
    simp only [hx, norm_zero]
    positivity
  have hi : ‖D x‖ ^ 2 ≤ ‖D.adjoint (D x)‖ * ‖x‖ := by
    calc
      ‖D x‖ ^ 2 = inner ℝ (D.adjoint (D x)) x := by
        rw [D.adjoint_inner_left, real_inner_self_eq_norm_sq]
      _ ≤ _ := real_inner_le_norm _ _
  have he := mul_le_mul_of_nonneg_right (hd (D x)) (norm_nonneg x)
  change ‖D x‖ ≤ _
  apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hx)).mp
  nlinarith

omit [FiniteDimensional ℝ E] in
/-- The explicit corrected right inverse in the stacking argument. The final
norm comparison uses the two actual row-block norms of the stacked operator. -/
theorem exists_lifted_subspace
    {A K H : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [FiniteDimensional ℝ A] [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [FiniteDimensional ℝ K] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    (M : E →ₗ[ℝ] A) (B : E →ₗ[ℝ] F) (P : A →ₗ[ℝ] E)
    (Q : K →ₗ[ℝ] E) (Z : E →ₗ[ℝ] H) (W : Submodule ℝ F)
    (hMP : M.comp P = LinearMap.id) (hMQ : M.comp Q = 0)
    (hQ : ∀ v, ‖Q v‖ ≤ ‖v‖)
    {p b d : ℝ} (hp : 0 ≤ p) (hb : 0 ≤ b) (hd : 0 < d)
    (hP : ∀ a, ‖P a‖ ≤ p * ‖a‖)
    (hT : ∀ y ∈ W, d * ‖y‖ ≤ ‖(B.comp Q).adjoint y‖)
    (hS : ∀ y ∈ W, ‖(B.comp P).adjoint y‖ ≤ b * ‖y‖)
    (hZM : ∀ x, ‖M x‖ ≤ ‖Z x‖) (hZB : ∀ x, ‖B x‖ ≤ ‖Z x‖) :
    ∃ U : Submodule ℝ E, finrank ℝ U = finrank ℝ A + finrank ℝ W ∧
      ∀ x ∈ U, ‖x‖ ≤ (p + (1+b)/d) * ‖Z x‖ := by
  let π := W.orthogonalProjectionOnto.toLinearMap
  let T := π.comp (B.comp Q)
  have ht : ∀ y : W, d * ‖y‖ ≤ ‖T.adjoint y‖ := by
    intro y
    rw [projection_comp_adjoint]
    exact hT y y.property
  obtain ⟨R, hR, hnR⟩ := exists_bounded_rightInverse T hd ht
  let S := π.comp (B.comp P)
  let J : A × W →ₗ[ℝ] E :=
    P.comp (LinearMap.fst ℝ A W) +
      Q.comp (R.comp (LinearMap.snd ℝ A W - S.comp (LinearMap.fst ℝ A W)))
  have hJa (a : A) (w : W) : M (J (a,w)) = a := by
    have h1 : M (P a) = a := congrArg (fun f : A →ₗ[ℝ] A => f a) hMP
    have h2 (v : K) : M (Q v) = 0 := congrArg (fun f : K →ₗ[ℝ] A => f v) hMQ
    change M (P a + Q (R (w-S a))) = a
    rw [map_add, h1, h2, add_zero]
  have hJw (a : A) (w : W) : π (B (J (a,w))) = w := by
    have h1 (v : W) : π (B (Q (R v))) = v :=
      congrArg (fun f : W →ₗ[ℝ] W => f v) hR
    change π (B (P a + Q (R (w-S a)))) = w
    rw [map_add, map_add, h1]
    change S a + (w-S a) = w
    abel
  have hiJ : Function.Injective J := by
    rintro ⟨a,w⟩ ⟨a',w'⟩ he
    have ha := congrArg M he
    have hw := congrArg (fun x => π (B x)) he
    rw [hJa, hJa] at ha
    rw [hJw, hJw] at hw
    exact Prod.ext ha hw
  refine ⟨J.range, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hiJ, Module.finrank_prod]
  · rintro x ⟨⟨a,w⟩, rfl⟩
    have ha : ‖a‖ ≤ ‖Z (J (a,w))‖ := by
      calc
        ‖a‖ = ‖M (J (a,w))‖ := congrArg norm (hJa a w).symm
        _ ≤ _ := hZM _
    have hw : ‖w‖ ≤ ‖Z (J (a,w))‖ := by
      calc
        ‖w‖ = ‖π (B (J (a,w)))‖ := congrArg norm (hJw a w).symm
        _ ≤ _ := (W.norm_orthogonalProjectionOnto_apply_le _).trans (hZB _)
    have hSa : ‖S a‖ ≤ b * ‖a‖ := projection_norm_le_of_adjoint (B.comp P) W hb hS a
    calc
      ‖J (a,w)‖ = ‖P a + Q (R (w-S a))‖ := rfl
      _ ≤ ‖P a‖ + ‖Q (R (w-S a))‖ := norm_add_le _ _
      _ ≤ p*‖a‖ + ‖R (w-S a)‖ := add_le_add (hP a) (hQ _)
      _ ≤ p*‖a‖ + ‖w-S a‖/d := add_le_add_right (hnR _) _
      _ ≤ p*‖a‖ + (‖w‖+b*‖a‖)/d := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add_right hSa _)
      _ ≤ p*‖Z (J (a,w))‖ + (‖Z (J (a,w))‖+b*‖Z (J (a,w))‖)/d := by
        gcongr
      _ = (p+(1+b)/d)*‖Z (J (a,w))‖ := by ring

open Spectral

theorem norm_stack_sq {r c n : Type*} [Fintype r] [Fintype c] [Fintype n]
    [DecidableEq n] (M : Matrix r n ℝ) (B : Matrix c n ℝ)
    (x : EuclideanSpace ℝ n) :
    ‖euclideanMap (Matrix.fromRows M B) x‖^2 =
      ‖euclideanMap M x‖^2 + ‖euclideanMap B x‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
  rfl

theorem norm_map_of_orthonormal_columns {r c : Type*} [Fintype r] [Fintype c]
    [DecidableEq r] [DecidableEq c] (Q : Matrix r c ℝ) (hQ : Qᴴ*Q=1)
    (x : EuclideanSpace ℝ c) : ‖euclideanMap Q x‖ = ‖x‖ := by
  have h : (euclideanMap Q).adjoint.comp (euclideanMap Q) = LinearMap.id := by
    simpa only [euclideanMap, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.toLpLin_mul_same, Matrix.toLpLin_one] using
      congrArg Matrix.toEuclideanLin hQ
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    ‖euclideanMap Q x‖^2 = inner ℝ x ((euclideanMap Q).adjoint (euclideanMap Q x)) := by
      rw [LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
    _ = ‖x‖^2 := by
      have hx : (euclideanMap Q).adjoint (euclideanMap Q x) = x :=
        congrArg (fun f : EuclideanSpace ℝ c →ₗ[ℝ] EuclideanSpace ℝ c => f x) h
      rw [hx, real_inner_self_eq_norm_sq]

/-- Manuscript Lemma 4.6, with one-based source singular values translated to
zero-based descending indices and the required positive denominator explicit. -/
theorem spectral_stacking {s k j : ℕ}
    (M : Matrix (Fin s) (Fin (s+k)) ℝ)
    (B : Matrix (Fin k) (Fin (s+k)) ℝ)
    (Q : Matrix (Fin (s+k)) (Fin k) ℝ)
    (hM : Function.Surjective (euclideanMap M))
    (hQ : Qᴴ*Q=1)
    (hker : LinearMap.range (euclideanMap Q) = LinearMap.ker (euclideanMap M))
    (hjk : 2*j<k) (hjs : j<s)
    (hd : 0 < singularValue (B*Q) (k-j-1)) :
    (opNorm (pinv M) + (1 + singularValue (B*pinv M) j) /
      singularValue (B*Q) (k-j-1))⁻¹ ≤
      singularValue (Matrix.fromRows M B) (s+k-2*j-1) := by
  let i : Fin k := ⟨k-j-1, by omega⟩
  let z : Fin s := ⟨j, hjs⟩
  have hkdim : finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := by simp
  have hsdim : finrank ℝ (EuclideanSpace ℝ (Fin s)) = s := by simp
  have hT : euclideanMap (B*Q) = (euclideanMap B).comp (euclideanMap Q) :=
    Matrix.toLpLin_mul_same _ _ _
  have hS : euclideanMap (B*pinv M) = (euclideanMap B).comp (euclideanMap (pinv M)) :=
    Matrix.toLpLin_mul_same _ _ _
  obtain ⟨W,hW,hWT,hWS⟩ := exists_good_subspace (euclideanMap (B*Q))
    (euclideanMap (B*pinv M)) hkdim hsdim i z hd
  have hMP : (euclideanMap M).comp (euclideanMap (pinv M)) = LinearMap.id := by
    simpa only [euclideanMap, Matrix.toLpLin_mul_same, Matrix.toLpLin_one] using
      congrArg Matrix.toEuclideanLin
        (mul_pinv_eq_one M (gram_posDef_of_surjective M hM).isUnit)
  have hMQ : (euclideanMap M).comp (euclideanMap Q) = 0 := by
    apply LinearMap.ext
    intro x
    have hx : euclideanMap Q x ∈ (euclideanMap M).ker := by
      rw [← hker]
      exact ⟨x,rfl⟩
    exact hx
  have hQM : ∀ v, ‖euclideanMap Q v‖ ≤ ‖v‖ :=
    fun v => (norm_map_of_orthonormal_columns Q hQ v).le
  have hZM (x : EuclideanSpace ℝ (Fin (s+k))) :
      ‖euclideanMap M x‖ ≤ ‖euclideanMap (Matrix.fromRows M B) x‖ := by
    have hh := norm_stack_sq M B x
    nlinarith [norm_nonneg (euclideanMap M x),
      norm_nonneg (euclideanMap (Matrix.fromRows M B) x),
      sq_nonneg ‖euclideanMap B x‖]
  have hZB (x : EuclideanSpace ℝ (Fin (s+k))) :
      ‖euclideanMap B x‖ ≤ ‖euclideanMap (Matrix.fromRows M B) x‖ := by
    have hh := norm_stack_sq M B x
    nlinarith [norm_nonneg (euclideanMap B x),
      norm_nonneg (euclideanMap (Matrix.fromRows M B) x),
      sq_nonneg ‖euclideanMap M x‖]
  have hWP : ∀ y ∈ W, singularValue (B*Q) (k-j-1) * ‖y‖ ≤
      ‖((euclideanMap B).comp (euclideanMap Q)).adjoint y‖ := by
    simpa only [← hT, singularValue, i] using hWT
  have hWB : ∀ y ∈ W, ‖((euclideanMap B).comp (euclideanMap (pinv M))).adjoint y‖ ≤
      singularValue (B*pinv M) j * ‖y‖ := by
    simpa only [← hS, singularValue, z] using hWS
  obtain ⟨U,hU,hu⟩ := exists_lifted_subspace (euclideanMap M) (euclideanMap B)
    (euclideanMap (pinv M)) (euclideanMap Q)
    (euclideanMap (Matrix.fromRows M B)) W hMP hMQ hQM
    (opNorm_nonneg (pinv M)) (singularValue_nonneg (B*pinv M) j) hd
    (fun a => (euclideanMap (pinv M)).toContinuousLinearMap.le_opNorm a)
    hWP hWB hZM hZB
  let C := opNorm (pinv M) + (1+singularValue (B*pinv M) j) /
    singularValue (B*Q) (k-j-1)
  have hC : 0<C := by
    dsimp [C]
    have hp := opNorm_nonneg (pinv M)
    have hb := singularValue_nonneg (B*pinv M) j
    positivity
  have hdim : s+k-2*j-1+1 ≤ finrank ℝ U := by
    rw [hU, hsdim]
    change k-j-1+1-j ≤ finrank ℝ W at hW
    omega
  apply singular_lower_of_subspace (euclideanMap (Matrix.fromRows M B))
    (show finrank ℝ (EuclideanSpace ℝ (Fin (s+k))) = s+k by simp)
    ⟨s+k-2*j-1, by omega⟩ U hdim C⁻¹
  intro x hx
  have h := hu x hx
  change ‖x‖ ≤ C * ‖euclideanMap (Matrix.fromRows M B) x‖ at h
  exact (inv_mul_le_iff₀ hC).mpr h

end NLA.IE06.SpectralStacking

#assert_trust kernel NLA.IE06.SpectralStacking.singular_lower_of_subspace
#print axioms NLA.IE06.SpectralStacking.singular_lower_of_subspace
#assert_trust kernel NLA.IE06.SpectralStacking.norm_le_singularValue_mul_of_mem_trailing
#print axioms NLA.IE06.SpectralStacking.norm_le_singularValue_mul_of_mem_trailing
#assert_trust kernel NLA.IE06.SpectralStacking.singularValue_mul_norm_le_of_mem_leading
#print axioms NLA.IE06.SpectralStacking.singularValue_mul_norm_le_of_mem_leading
#assert_trust kernel NLA.IE06.SpectralStacking.adjoint_lower_on_image
#print axioms NLA.IE06.SpectralStacking.adjoint_lower_on_image
#assert_trust kernel NLA.IE06.SpectralStacking.adjoint_upper_off_image
#print axioms NLA.IE06.SpectralStacking.adjoint_upper_off_image
#assert_trust kernel NLA.IE06.SpectralStacking.injective_of_norm_lower
#print axioms NLA.IE06.SpectralStacking.injective_of_norm_lower
#assert_trust kernel NLA.IE06.SpectralStacking.exists_good_subspace
#print axioms NLA.IE06.SpectralStacking.exists_good_subspace
#assert_trust kernel NLA.IE06.SpectralStacking.exists_bounded_rightInverse
#print axioms NLA.IE06.SpectralStacking.exists_bounded_rightInverse
#assert_trust kernel NLA.IE06.SpectralStacking.projection_comp_adjoint
#print axioms NLA.IE06.SpectralStacking.projection_comp_adjoint
#assert_trust kernel NLA.IE06.SpectralStacking.projection_norm_le_of_adjoint
#print axioms NLA.IE06.SpectralStacking.projection_norm_le_of_adjoint
#assert_trust kernel NLA.IE06.SpectralStacking.exists_lifted_subspace
#print axioms NLA.IE06.SpectralStacking.exists_lifted_subspace
#assert_trust kernel NLA.IE06.SpectralStacking.norm_stack_sq
#print axioms NLA.IE06.SpectralStacking.norm_stack_sq
#assert_trust kernel NLA.IE06.SpectralStacking.norm_map_of_orthonormal_columns
#print axioms NLA.IE06.SpectralStacking.norm_map_of_orthonormal_columns
#assert_trust kernel NLA.IE06.SpectralStacking.spectral_stacking
#print axioms NLA.IE06.SpectralStacking.spectral_stacking
